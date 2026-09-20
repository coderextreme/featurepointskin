# SPDX-License-Identifier: GPL-3.0-or-later
"""
hanim_x3d.py

Standalone HAnim (HAnimHumanoid / HAnimJoint / HAnimSegment / HAnimSite)
support for the io_scene_x3d Blender extension.

Design decisions baked into this module:
  1. Skin weighting is per-HAnimJoint -> one Blender vertex group per joint/bone.
  2. HAnimSite center/translation is auto-compensated for Blender's tail-relative Empty parenting.
  3. HAnimJoint.scaleOrientation is baked into the bone's rest-pose matrix on import.
"""

import json
import bpy
import mathutils
from mathutils import Vector, Matrix, Quaternion

# ---------------------------------------------------------------------------
# Custom property namespace
# ---------------------------------------------------------------------------

HANIM_PREFIX = "hanim_"

HUMANOID_PROPS = ("version", "center", "bboxCenter", "bboxSize", "info")
JOINT_PROPS = ("ulimit", "llimit", "limitOrientation", "stiffness",
               "bboxCenter", "bboxSize")
SEGMENT_PROPS = ("mass", "centerOfMass", "momentsOfInertia",
                 "bboxCenter", "bboxSize")
SITE_PROPS = ("bboxCenter", "bboxSize")


def prop(name):
    return f"{HANIM_PREFIX}{name}"


# ---------------------------------------------------------------------------
# Node-access adapter over io_scene_x3d's real vrmlNode API
# ---------------------------------------------------------------------------

_FLOAT3_FIELDS = {"center", "translation", "scale", "bboxCenter", "bboxSize",
                  "centerOfMass", "stiffness"}
_FLOAT4_FIELDS = {"rotation", "scaleOrientation", "limitOrientation"}
_STRING_FIELDS = {"name", "version"}
_FLOAT_FIELDS = {"mass"}
_INT_ARRAY_FIELDS = {"skinCoordIndex", "coordIndex", "index"}
_FLOAT_ARRAY_FIELDS = {"skinCoordWeight", "momentsOfInertia", "ulimit", "llimit", "point"}


def get_field(node, field_name, default=None, ancestry=()):
    """Typed dispatch over vrmlNode's getFieldAsX() accessors."""
    if field_name == "node_type":
        return node.getSpec()
    if field_name in _FLOAT3_FIELDS:
        return tuple(node.getFieldAsFloatTuple(field_name, default, ancestry) or default or (0.0, 0.0, 0.0))
    if field_name in _FLOAT4_FIELDS:
        return tuple(node.getFieldAsFloatTuple(field_name, default, ancestry) or default or (0.0, 0.0, 1.0, 0.0))
    if field_name in _STRING_FIELDS:
        return node.getFieldAsString(field_name, default, ancestry)
    if field_name in _FLOAT_FIELDS:
        return node.getFieldAsFloat(field_name, default, ancestry)
    if field_name in _INT_ARRAY_FIELDS:
        return node.getFieldAsArray(field_name, 0, ancestry) or []
    if field_name in _FLOAT_ARRAY_FIELDS:
        return node.getFieldAsArray(field_name, 0, ancestry) or []

    try:
        return node.getFieldAsString(field_name, default, ancestry)
    except Exception:
        return default


def get_children(node, field_name="children"):
    return list(getattr(node, "children", []) or [])


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------

def bone_head_to_tail_offset(bone):
    return Vector((0.0, -bone.length, 0.0))


def site_offset_import(bone, x3d_center_translation):
    head_relative = Vector(x3d_center_translation)
    return head_relative + (-bone_head_to_tail_offset(bone))


def site_offset_export(bone, blender_local_translation):
    tail_relative = Vector(blender_local_translation)
    return tail_relative + bone_head_to_tail_offset(bone)


def bake_scale_orientation(local_matrix, scale_orientation):
    ax, ay, az, angle = scale_orientation
    if angle == 0.0 or (ax, ay, az) == (0.0, 0.0, 0.0):
        return local_matrix.copy()

    loc, rot, scale = local_matrix.decompose()
    so = Quaternion(Vector((ax, ay, az)).normalized(), angle)
    so_mat = so.to_matrix().to_4x4()
    scale_mat = Matrix.Diagonal((*scale, 1.0))
    baked_scale_block = so_mat @ scale_mat @ so_mat.inverted()

    return (Matrix.Translation(loc)
            @ rot.to_matrix().to_4x4()
            @ baked_scale_block)


# ---------------------------------------------------------------------------
# Import logic
# ---------------------------------------------------------------------------

def import_humanoid(bpycollection, humanoid_node, ancestry, global_matrix, context):
    armature_obj, joint_bone_names, root_joints = \
        import_humanoid_armature(context, humanoid_node, bpycollection)

    from . import import_x3d as _import_x3d
    ancestry_matrix = _import_x3d.getFinalMatrix(humanoid_node, None, ancestry, global_matrix)
    humanoid_local_matrix = read_rest_local_matrix_from(armature_obj)
    armature_obj.matrix_basis = ancestry_matrix @ humanoid_local_matrix

    consumed_ids = {id(humanoid_node)}
    consumed_ids.update(id(n) for n in root_joints)

    body_mesh_obj = None
    skin_coord_node = humanoid_node.getChildBySpec('Coordinate')
    skin_shape_node = humanoid_node.getChildBySpec('Shape')

    # Fallback: skin Coordinate inside skin Shape geometry
    if skin_coord_node is None and skin_shape_node is not None:
        geom = (skin_shape_node.getChildBySpec('IndexedFaceSet') or
                skin_shape_node.getChildBySpec('IndexedTriangleSet'))
        if geom is not None:
            skin_coord_node = geom.getChildBySpec('Coordinate')

    if skin_coord_node is not None:
        consumed_ids.add(id(skin_coord_node))
        if skin_shape_node is not None:
            consumed_ids.add(id(skin_shape_node))
        body_mesh_obj = _create_shared_skin_object(
            humanoid_node, skin_coord_node, skin_shape_node,
            armature_obj, bpycollection)

    # Pass 2/3: Traverse only from the true root joint(s)
    for real_child in root_joints:
        spec = real_child.getSpec()
        if spec == 'HAnimJoint':
            bone_name = joint_bone_names.get(get_field(real_child, "name", "Joint"))
            if not bone_name:
                continue
            if body_mesh_obj is not None:
                import_joint_skin_weights(real_child, bone_name, body_mesh_obj)
            _import_body_recursive(context, real_child, armature_obj, bone_name,
                                   joint_bone_names, bpycollection, body_mesh_obj,
                                   consumed_ids)

    return consumed_ids


def _create_shared_skin_object(humanoid_node, skin_coord_node, skin_shape_node,
                               armature_obj, collection):
    name = get_field(humanoid_node, "name", "Humanoid") + "_Skin"
    points = get_field(skin_coord_node, "point", [])
    verts = _grouped(points, 3)

    faces = []
    if skin_shape_node is not None:
        geometry = (skin_shape_node.getChildBySpec('IndexedFaceSet') or
                    skin_shape_node.getChildBySpec('IndexedTriangleSet'))
        if geometry is not None:
            geo_type = geometry.getSpec()
            if geo_type == 'IndexedFaceSet':
                coord_index = geometry.getFieldAsArray('coordIndex', 0, ())
                current_face = []
                for idx in coord_index:
                    if idx == -1:
                        if len(current_face) >= 3:
                            faces.append(tuple(current_face))
                        current_face = []
                    else:
                        current_face.append(idx)
                if len(current_face) >= 3:
                    faces.append(tuple(current_face))
            else:
                index = geometry.getFieldAsArray('index', 0, ())
                for i in range(0, len(index) - 2, 3):
                    faces.append(tuple(index[i:i + 3]))

    mesh_data = bpy.data.meshes.new(name)
    mesh_data.from_pydata(verts, [], faces)
    mesh_data.update()

    mesh_obj = bpy.data.objects.new(name, mesh_data)
    collection.objects.link(mesh_obj)
    mesh_obj.parent = armature_obj
    modifier = mesh_obj.modifiers.new(name="HAnimSkin", type='ARMATURE')
    modifier.object = armature_obj
    mesh_obj[prop("node_type")] = "SharedSkin"
    return mesh_obj


def _grouped(flat, n):
    return [tuple(flat[i:i + n]) for i in range(0, len(flat) - n + 1, n)]


def _import_body_recursive(context, node, armature_obj, joint_bone_name,
                           joint_bone_names, collection, body_mesh_obj,
                           consumed_ids):
    for child in get_children(node):
        consumed_ids.add(id(child))
        spec = child.getSpec()

        if spec == 'HAnimJoint':
            child_bone_name = joint_bone_names.get(get_field(child, "name", "Joint"))
            if child_bone_name:
                if body_mesh_obj is not None:
                    import_joint_skin_weights(child, child_bone_name, body_mesh_obj)
                _import_body_recursive(context, child, armature_obj, child_bone_name,
                                       joint_bone_names, collection, body_mesh_obj,
                                       consumed_ids)

        elif spec == 'HAnimSegment':
            if body_mesh_obj is not None:
                import_segment_metadata(child, joint_bone_name, body_mesh_obj)
            else:
                import_segment(context, child, armature_obj, joint_bone_name,
                               collection, shared_mesh_data=None)
                for shape in get_children(child):
                    consumed_ids.add(id(shape))
                    geometry = (shape.getChildBySpec('IndexedFaceSet') or
                                shape.getChildBySpec('IndexedTriangleSet'))
                    if geometry is not None:
                        consumed_ids.add(id(geometry))
                        coord = geometry.getChildBySpec('Coordinate')
                        if coord is not None:
                            consumed_ids.add(id(coord))

        elif spec == 'HAnimSite':
            import_site(context, child, armature_obj, joint_bone_name, collection)


def import_segment_metadata(segment_node, joint_bone_name, body_mesh_obj):
    entry = {"name": get_field(segment_node, "name", "Segment"),
             "joint_bone_name": joint_bone_name}
    for field_name in SEGMENT_PROPS:
        val = get_field(segment_node, field_name)
        if val:
            entry[field_name] = val

    key = prop("segments")
    raw = body_mesh_obj.get(key, None)
    try:
        segments = json.loads(raw) if raw else []
    except Exception:
        segments = []
    segments.append(entry)
    body_mesh_obj[key] = json.dumps(segments)


def real_node(node):
    getter = getattr(node, "getRealNode", None)
    return getter() if getter is not None else node


def unique_real_children(node, consumed_real_ids):
    out = []
    for child in get_children(node):
        real = real_node(child)
        if id(real) in consumed_real_ids:
            continue
        consumed_real_ids.add(id(real))
        out.append(real)
    return out


def import_humanoid_armature(context, humanoid_node, collection):
    name = get_field(humanoid_node, "name", "Humanoid")
    armature_data = bpy.data.armatures.new(f"{name}_Armature")
    armature_obj = bpy.data.objects.new(name, armature_data)
    collection.objects.link(armature_obj)

    for field_name in HUMANOID_PROPS:
        val = get_field(humanoid_node, field_name)
        if val is not None:
            armature_obj[prop(field_name)] = val

    h_translation = Vector(get_field(humanoid_node, "translation", (0, 0, 0)))
    h_rotation = get_field(humanoid_node, "rotation", (0, 0, 1, 0))
    h_scale = get_field(humanoid_node, "scale", (1, 1, 1))
    h_scale_orientation = get_field(humanoid_node, "scaleOrientation", (0, 0, 1, 0))

    h_rot_axis = Vector(h_rotation[:3])
    h_rot_quat = (Quaternion(h_rot_axis.normalized(), h_rotation[3])
                  if h_rot_axis.length > 0 else Quaternion())
    humanoid_local_matrix = (Matrix.Translation(h_translation)
                             @ h_rot_quat.to_matrix().to_4x4()
                             @ Matrix.Diagonal((*h_scale, 1.0)))
    humanoid_local_matrix = bake_scale_orientation(humanoid_local_matrix,
                                                   h_scale_orientation)

    armature_obj.matrix_basis = humanoid_local_matrix
    armature_obj[prop("rest_local_matrix")] = tuple(
        elem for row in humanoid_local_matrix for elem in row)

    context.view_layer.objects.active = armature_obj
    bpy.ops.object.mode_set(mode='EDIT')

    joint_bone_names = {}
    bone_custom_props = {}
    world_matrices = {}
    consumed_real_ids = set()
    top_level_real_children = unique_real_children(humanoid_node, consumed_real_ids)

    # Identify true skeleton roots
    root_joints = [
        n for n in top_level_real_children
        if n.getSpec() == 'HAnimJoint' and getattr(n, 'parent', None) == humanoid_node
    ]
    if len(root_joints) > 1:
        named_roots = [j for j in root_joints if "root" in get_field(j, "name", "").lower()]
        root_joints = named_roots if named_roots else root_joints[:1]

    for root in root_joints:
        _import_joint_recursive(armature_data, root, parent_bone_name=None,
                                parent_matrix=Matrix.Identity(4),
                                joint_bone_names=joint_bone_names,
                                bone_custom_props=bone_custom_props,
                                world_matrices=world_matrices)

    resolve_bone_tails(armature_data, world_matrices)

    bpy.ops.object.mode_set(mode='OBJECT')

    # Re-apply custom properties to Bone datablocks in Object Mode
    for b_name, props in bone_custom_props.items():
        if b_name in armature_data.bones:
            b = armature_data.bones[b_name]
            for k, v in props.items():
                b[k] = v

    return armature_obj, joint_bone_names, root_joints


def resolve_bone_tails(armature_data, world_matrices):
    for bone in armature_data.edit_bones:
        children = list(bone.children)
        if len(children) == 1:
            bone.tail = children[0].head
        elif len(children) > 1:
            avg = Vector((0.0, 0.0, 0.0))
            for child in children:
                avg += (child.head - bone.head)
            avg /= len(children)
            bone.tail = bone.head + avg if avg.length > 1e-6 else \
                bone.head + _leaf_tail_direction(bone, world_matrices)
        else:
            bone.tail = bone.head + _leaf_tail_direction(bone, world_matrices)

        if (bone.tail - bone.head).length < 1e-6:
            bone.tail = bone.head + Vector((0.0, 0.01, 0.0))


def _leaf_tail_direction(bone, world_matrices):
    world_matrix = world_matrices.get(bone.name)
    length_ref = bone.parent.length * 0.5 if bone.parent else 0.05
    length_ref = max(length_ref, 0.01)
    if world_matrix is not None:
        y_axis = world_matrix.to_3x3() @ Vector((0.0, 1.0, 0.0))
        if y_axis.length > 1e-6:
            return y_axis.normalized() * length_ref
    return Vector((0.0, length_ref, 0.0))


def _import_joint_recursive(armature_data, joint_node, parent_bone_name,
                            parent_matrix, joint_bone_names,
                            bone_custom_props, world_matrices):
    joint_name = get_field(joint_node, "name", "Joint")
    bone = armature_data.edit_bones.new(joint_name)
    joint_bone_names[joint_name] = bone.name

    center = Vector(get_field(joint_node, "center", (0, 0, 0)))
    rotation = get_field(joint_node, "rotation", (0, 0, 1, 0))
    scale = get_field(joint_node, "scale", (1, 1, 1))
    scale_orientation = get_field(joint_node, "scaleOrientation", (0, 0, 1, 0))
    translation = Vector(get_field(joint_node, "translation", (0, 0, 0)))

    rot_axis = Vector(rotation[:3])
    rot_angle = rotation[3]
    rot_quat = (Quaternion(rot_axis.normalized(), rot_angle)
                if rot_axis.length > 0 else Quaternion())

    local_matrix = (Matrix.Translation(translation)
                    @ rot_quat.to_matrix().to_4x4()
                    @ Matrix.Diagonal((*scale, 1.0)))
    local_matrix = bake_scale_orientation(local_matrix, scale_orientation)

    world_matrix = parent_matrix @ local_matrix
    world_matrices[bone.name] = world_matrix
    head = world_matrix.translation + center
    bone.head = head
    bone.tail = head + Vector((0, 0.01, 0))

    if parent_bone_name:
        bone.parent = armature_data.edit_bones[parent_bone_name]
        bone.use_connect = False

    props = {}
    for field_name in JOINT_PROPS:
        val = get_field(joint_node, field_name)
        if val:
            props[prop(field_name)] = val

    props[prop("rest_local_matrix")] = tuple(
        elem for row in local_matrix for elem in row)
    bone_custom_props[bone.name] = props

    for child in get_children(joint_node):
        if get_field(child, "node_type") == "HAnimJoint":
            _import_joint_recursive(armature_data, child, bone.name,
                                    world_matrix, joint_bone_names,
                                    bone_custom_props, world_matrices)


def import_segment(context, segment_node, armature_obj, joint_bone_name,
                   collection, shared_mesh_data=None):
    seg_name = get_field(segment_node, "name", "Segment")
    uses_shared_skin = shared_mesh_data is not None

    if uses_shared_skin:
        mesh_obj = bpy.data.objects.new(seg_name, shared_mesh_data)
        mesh_obj.parent = armature_obj
    else:
        mesh_data = bpy.data.meshes.new(seg_name)
        import_segment_own_geometry(mesh_data, segment_node)
        mesh_obj = bpy.data.objects.new(seg_name, mesh_data)
        mesh_obj.parent = armature_obj
        mesh_obj.parent_type = 'BONE'
        mesh_obj.parent_bone = joint_bone_name

    collection.objects.link(mesh_obj)

    if uses_shared_skin:
        modifier = mesh_obj.modifiers.new(name="HAnimSkin", type='ARMATURE')
        modifier.object = armature_obj

    for field_name in SEGMENT_PROPS:
        val = get_field(segment_node, field_name)
        if val:
            mesh_obj[prop(field_name)] = val
    mesh_obj[prop("node_type")] = "Segment"
    mesh_obj[prop("uses_shared_skin")] = uses_shared_skin

    return mesh_obj


def import_segment_own_geometry(mesh_data, segment_node):
    verts = []
    faces = []
    vertex_offset = 0

    for shape in get_children(segment_node):
        if get_field(shape, "node_type") != "Shape":
            continue
        geometry = (shape.getChildBySpec('IndexedFaceSet') or
                    shape.getChildBySpec('IndexedTriangleSet'))
        if geometry is None:
            continue
        geo_type = geometry.getSpec()

        coord_node = geometry.getChildBySpec('Coordinate')
        points = get_field(coord_node, "point", []) if coord_node else []
        verts.extend(_grouped(points, 3))

        if geo_type == "IndexedFaceSet":
            coord_index = get_field(geometry, "coordIndex", [])
            current_face = []
            for idx in coord_index:
                if idx == -1:
                    if len(current_face) >= 3:
                        faces.append(tuple(vertex_offset + i for i in current_face))
                    current_face = []
                else:
                    current_face.append(idx)
            if len(current_face) >= 3:
                faces.append(tuple(vertex_offset + i for i in current_face))
        else:
            index = get_field(geometry, "index", [])
            for i in range(0, len(index) - 2, 3):
                faces.append(tuple(vertex_offset + index[i + k] for k in range(3)))

        vertex_offset += len(points) // 3

    mesh_data.from_pydata(verts, [], faces)
    mesh_data.update()
    return mesh_data


def import_joint_skin_weights(joint_node, joint_bone_name, mesh_obj):
    indices = get_field(joint_node, "skinCoordIndex", [])
    weights = get_field(joint_node, "skinCoordWeight", [])
    if not indices:
        return

    num_verts = len(mesh_obj.data.vertices)
    if num_verts == 0:
        return

    vg = mesh_obj.vertex_groups.get(joint_bone_name)
    if vg is None:
        vg = mesh_obj.vertex_groups.new(name=joint_bone_name)

    if weights and len(weights) == len(indices):
        for idx, w in zip(indices, weights):
            if 0 <= idx < num_verts:
                vg.add([idx], w, 'REPLACE')
    else:
        valid_indices = [idx for idx in indices if 0 <= idx < num_verts]
        if valid_indices:
            vg.add(valid_indices, 1.0, 'REPLACE')


def import_site(context, site_node, armature_obj, joint_bone_name, collection):
    site_name = get_field(site_node, "name", "Site")
    empty = bpy.data.objects.new(site_name, None)
    empty.empty_display_type = 'PLAIN_AXES'
    empty.empty_display_size = 0.02
    collection.objects.link(empty)

    empty.parent = armature_obj
    empty.parent_type = 'BONE'
    empty.parent_bone = joint_bone_name

    bone = armature_obj.data.bones[joint_bone_name]
    center = get_field(site_node, "center", (0, 0, 0))
    translation = get_field(site_node, "translation", (0, 0, 0))
    x3d_offset = Vector(center) + Vector(translation)

    empty.location = site_offset_import(bone, x3d_offset)

    for field_name in SITE_PROPS:
        val = get_field(site_node, field_name)
        if val:
            empty[prop(field_name)] = val
    empty[prop("node_type")] = "Site"
    empty[prop("center")] = tuple(center)
    empty[prop("translation")] = tuple(translation)

    return empty


# ---------------------------------------------------------------------------
# Export logic
# ---------------------------------------------------------------------------

def export_humanoid(armature_obj):
    humanoid = {
        "node_type": "HAnimHumanoid",
        "name": armature_obj.name,
    }
    for field_name in HUMANOID_PROPS:
        key = prop(field_name)
        if key in armature_obj:
            humanoid[field_name] = armature_obj[key]

    humanoid_local_matrix = read_rest_local_matrix_from(armature_obj)
    if humanoid_local_matrix is not None:
        loc, rot, scale = humanoid_local_matrix.decompose()
        axis, angle = rot.to_axis_angle()
        axis = axis.normalized() if axis.length > 1e-6 else Vector((0, 0, 1))
        humanoid["translation"] = tuple(loc)
        humanoid["rotation"] = (*axis, angle)
        humanoid["scale"] = tuple(scale)

    body_mesh_obj = _find_shared_skin_object(armature_obj)

    root_bones = [b for b in armature_obj.data.bones if b.parent is None]
    world_matrix_cache = {}
    humanoid["skeleton"] = [
        export_joint_recursive(armature_obj, b, world_matrix_cache, body_mesh_obj)
        for b in root_bones]

    if body_mesh_obj is not None:
        humanoid["skinCoord"] = {
            "node_type": "Coordinate",
            "point": [tuple(v.co) for v in body_mesh_obj.data.vertices],
        }
        humanoid["skin"] = export_mesh_as_indexed_face_set(body_mesh_obj.data)
        humanoid["skinNormal"] = None
    else:
        humanoid["skin"] = None
        humanoid["skinCoord"] = None
        humanoid["skinNormal"] = None

    return humanoid


def _find_shared_skin_object(armature_obj):
    for child in armature_obj.children:
        if child.type == 'MESH' and child.get(prop("node_type")) == "SharedSkin":
            return child
    return None


def read_rest_local_matrix_from(id_data):
    key = prop("rest_local_matrix")
    if key not in id_data:
        return None
    flat = id_data[key]
    return Matrix((flat[0:4], flat[4:8], flat[8:12], flat[12:16]))


def read_rest_local_matrix(bone):
    return read_rest_local_matrix_from(bone)


def export_joint_recursive(armature_obj, bone, world_matrix_cache, body_mesh_obj):
    local_matrix = read_rest_local_matrix(bone)
    parent_world = (world_matrix_cache[bone.parent.name]
                    if bone.parent else Matrix.Identity(4))
    world_matrix = (parent_world @ local_matrix if local_matrix is not None
                    else Matrix.Translation(bone.head_local))
    world_matrix_cache[bone.name] = world_matrix

    center = Vector(bone.head_local) - world_matrix.translation

    joint = {
        "node_type": "HAnimJoint",
        "name": bone.name,
        "center": tuple(center),
    }

    if local_matrix is not None:
        loc, rot, scale = local_matrix.decompose()
        axis, angle = rot.to_axis_angle()
        axis = axis.normalized() if axis.length >= 1e-6 else Vector((0.0, 0.0, 1.0))
        joint["translation"] = tuple(loc)
        joint["rotation"] = (*axis, angle)
        joint["scale"] = tuple(scale)

    for field_name in JOINT_PROPS:
        key = prop(field_name)
        if key in bone:
            joint[field_name] = bone[key]

    joint["skinCoordIndex"], joint["skinCoordWeight"] = \
        export_joint_skin_weights(body_mesh_obj, bone)

    children = []
    for child_bone in bone.children:
        children.append(
            export_joint_recursive(armature_obj, child_bone, world_matrix_cache,
                                   body_mesh_obj))
    children.extend(export_segments_for_bone(armature_obj, bone, body_mesh_obj))
    children.extend(export_sites_for_bone(armature_obj, bone))
    joint["children"] = children

    return joint


def export_joint_skin_weights(body_mesh_obj, bone):
    if body_mesh_obj is None:
        return [], []
    vg = body_mesh_obj.vertex_groups.get(bone.name)
    if vg is None:
        return [], []
    indices, weights = [], []
    for v in body_mesh_obj.data.vertices:
        for g in v.groups:
            if g.group == vg.index:
                indices.append(v.index)
                weights.append(g.weight)
    return indices, weights


def export_mesh_as_indexed_face_set(mesh_data):
    points = [tuple(v.co) for v in mesh_data.vertices]
    coord_index = []
    for polygon in mesh_data.polygons:
        coord_index.extend(polygon.vertices)
        coord_index.append(-1)
    return {
        "node_type": "IndexedFaceSet",
        "coordIndex": coord_index,
        "coord": {"node_type": "Coordinate", "point": points},
    }


def export_segments_for_bone(armature_obj, bone, body_mesh_obj):
    segments = []

    if body_mesh_obj is not None:
        raw = body_mesh_obj.get(prop("segments"), None)
        try:
            stored_segments = json.loads(raw) if isinstance(raw, str) else list(raw or [])
        except Exception:
            stored_segments = []
        for entry in stored_segments:
            if entry.get("joint_bone_name") != bone.name:
                continue
            seg = {"node_type": "HAnimSegment", "name": entry.get("name", "Segment")}
            for field_name in SEGMENT_PROPS:
                if field_name in entry:
                    seg[field_name] = entry[field_name]
            segments.append(seg)

    for mesh_obj in armature_obj.children:
        if mesh_obj.type != 'MESH':
            continue
        if mesh_obj.get(prop("node_type")) != "Segment":
            continue
        if mesh_obj.get(prop("uses_shared_skin"), True):
            continue
        if mesh_obj.parent_bone != bone.name:
            continue
        seg = {"node_type": "HAnimSegment", "name": mesh_obj.name}
        for field_name in SEGMENT_PROPS:
            key = prop(field_name)
            if key in mesh_obj:
                seg[field_name] = mesh_obj[key]
        ifs = export_mesh_as_indexed_face_set(mesh_obj.data)
        seg["children"] = [{"node_type": "Shape", "geometry": ifs}]
        segments.append(seg)

    return segments


def export_sites_for_bone(armature_obj, bone):
    sites = []
    for obj in armature_obj.children:
        if obj.type != 'EMPTY':
            continue
        if obj.get(prop("node_type")) != "Site":
            continue
        if obj.parent_bone != bone.name:
            continue
        x3d_offset = site_offset_export(bone, obj.location)
        site = {
            "node_type": "HAnimSite",
            "name": obj.name,
            "center": tuple(x3d_offset),
        }
        for field_name in SITE_PROPS:
            key = prop(field_name)
            if key in obj:
                site[field_name] = obj[key]
        sites.append(site)
    return sites
