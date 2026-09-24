# SPDX-License-Identifier: GPL-3.0-or-later
"""
hanim_x3d.py

Standalone HAnim (HAnimHumanoid / HAnimJoint / HAnimSegment / HAnimSite / HAnimDisplacer)
support for the io_scene_x3d Blender extension.

Design decisions baked into this module:
  1. Skin weighting is per-HAnimJoint -> one Blender vertex group per joint/bone.
  2. HAnimSite center/translation is auto-compensated for Blender's tail-relative Empty parenting.
  3. HAnimJoint.scaleOrientation is baked into the bone's rest-pose matrix on import.
  4. HAnimSegment own-geometry walks Transform hierarchies, baking cumulative matrices.
  5. HAnimDisplacer nodes import as Blender Shape Keys with coordinate displacements.
"""

import json
import os
import re
import hashlib
import tempfile
import urllib.request
import xml.etree.ElementTree as ET
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
DISPLACER_PROPS = ("weight", "coordIndex", "displacements", "bboxCenter", "bboxSize")


def prop(name):
    return f"{HANIM_PREFIX}{name}"


# ---------------------------------------------------------------------------
# Node-access adapter over io_scene_x3d's real vrmlNode API
# ---------------------------------------------------------------------------

_FLOAT3_FIELDS = {"center", "translation", "scale", "bboxCenter", "bboxSize",
                  "centerOfMass", "stiffness"}
_FLOAT4_FIELDS = {"rotation", "scaleOrientation", "limitOrientation"}
_STRING_FIELDS = {"name", "version", "description"}
_FLOAT_FIELDS = {"mass", "weight"}
_INT_ARRAY_FIELDS = {"skinCoordIndex", "coordIndex", "texCoordIndex", "index"}
_FLOAT_ARRAY_FIELDS = {"skinCoordWeight", "momentsOfInertia", "ulimit", "llimit",
                       "point", "displacements", "key", "keyValue"}


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


def get_node_transform_matrix(node):
    """Computes cumulative local 4x4 matrix of an X3D Transform node."""
    cent = Vector(get_field(node, "center", (0.0, 0.0, 0.0)))
    rot = get_field(node, "rotation", (0.0, 0.0, 1.0, 0.0))
    sca = Vector(get_field(node, "scale", (1.0, 1.0, 1.0)))
    scaori = get_field(node, "scaleOrientation", (0.0, 0.0, 1.0, 0.0))
    tx = Vector(get_field(node, "translation", (0.0, 0.0, 0.0)))

    cent_mat = Matrix.Translation(cent)
    cent_imat = Matrix.Translation(-cent)

    rot_axis = Vector(rot[:3])
    rot_quat = (Quaternion(rot_axis.normalized(), rot[3])
                if rot_axis.length > 1e-6 else Quaternion())
    rot_mat = rot_quat.to_matrix().to_4x4()

    sca_mat = Matrix.Diagonal((*sca, 1.0))

    so_axis = Vector(scaori[:3])
    so_quat = (Quaternion(so_axis.normalized(), scaori[3])
               if so_axis.length > 1e-6 else Quaternion())
    so_mat = so_quat.to_matrix().to_4x4()
    so_imat = so_mat.inverted()

    tx_mat = Matrix.Translation(tx)
    return tx_mat @ cent_mat @ rot_mat @ so_mat @ sca_mat @ so_imat @ cent_imat


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


def _consume_subtree(node, consumed_ids):
    consumed_ids.add(id(node))
    consumed_ids.add(id(real_node(node)))
    for child in get_children(node):
        _consume_subtree(child, consumed_ids)


# ---------------------------------------------------------------------------
# X3D appearance / animation bridge
# ---------------------------------------------------------------------------

def _ensure_node_image_material(material, image):
    """Make a Blender 5.x node material use an ImageTexture as Base Color."""
    if material is None:
        material = bpy.data.materials.new("X3D_ImageTexture")
    material.use_nodes = True
    nodes = material.node_tree.nodes
    links = material.node_tree.links

    out = next((n for n in nodes if n.type == 'OUTPUT_MATERIAL'), None)
    bsdf = next((n for n in nodes if n.type == 'BSDF_PRINCIPLED'), None)
    if out is None:
        out = nodes.new("ShaderNodeOutputMaterial")
    if bsdf is None:
        bsdf = nodes.new("ShaderNodeBsdfPrincipled")
    tex = next((n for n in nodes if n.type == 'TEX_IMAGE'), None)
    if tex is None:
        tex = nodes.new("ShaderNodeTexImage")

    tex.image = image
    if not any(l.to_node == bsdf and l.to_socket == bsdf.inputs.get("Base Color")
               for l in links):
        try:
            links.new(tex.outputs["Color"], bsdf.inputs["Base Color"])
        except Exception:
            pass
    if not any(l.to_node == out and l.to_socket == out.inputs.get("Surface")
               for l in links):
        try:
            links.new(bsdf.outputs["BSDF"], out.inputs["Surface"])
        except Exception:
            pass
    return material


def _image_urls_from_node(tex_node):
    """Return ImageTexture URLs, including the common X3D MFString form."""
    urls = []
    try:
        raw = tex_node.getFieldAsStringArray('url', ())
        if raw:
            urls.extend(raw)
    except Exception:
        pass
    if not urls:
        try:
            raw = tex_node.getFieldAsString('url', None, ())
        except Exception:
            raw = None
        if raw:
            quoted = re.findall(r'"([^"]+)"', raw)
            urls.extend(quoted or [raw])
    return [u.strip().strip('"') for u in urls if u and u.strip()]


def _load_x3d_image(tex_node):
    """Load ImageTexture through the stock importer, then robust local/HTTP fallback."""
    from . import import_x3d as _import_x3d

    try:
        image = _import_x3d.appearance_LoadImageTexture(tex_node, (), tex_node)
    except Exception:
        image = None
    if image:
        return image

    urls = _image_urls_from_node(tex_node)
    filename = getattr(tex_node, "getFilename", lambda: None)()
    base_dir = os.path.dirname(filename) if filename else os.getcwd()

    for url in urls:
        if not re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*://', url):
            candidates = [
                url,
                os.path.join(base_dir, url),
                bpy.path.abspath(url),
            ]
            for candidate in candidates:
                candidate = os.path.normpath(candidate)
                if os.path.exists(candidate):
                    try:
                        return bpy.data.images.load(candidate, check_existing=True)
                    except Exception:
                        pass
            continue

        if url.lower().startswith(("http://", "https://")):
            ext = os.path.splitext(url.split("?", 1)[0])[1] or ".img"
            cache_name = hashlib.sha256(url.encode("utf-8")).hexdigest() + ext
            cache_path = os.path.join(tempfile.gettempdir(), cache_name)
            try:
                if not os.path.exists(cache_path):
                    urllib.request.urlretrieve(url, cache_path)
                return bpy.data.images.load(cache_path, check_existing=True)
            except Exception as exc:
                print("HAnim X3D: unable to load ImageTexture", url, exc)

    return None


def _apply_shape_appearance(shape, appearance, ancestry):
    """Return a modern Blender material/image pair for an X3D Shape."""
    from . import import_x3d as _import_x3d

    material = None
    image = None
    if appearance is not None and hasattr(_import_x3d, "importShape_LoadAppearance"):
        try:
            material, image, _ = _import_x3d.importShape_LoadAppearance(
                shape.getDefName() or "Shape", appearance, ancestry, shape, False
            )
        except Exception as exc:
            print("HAnim X3D: appearance import fallback:", exc)

    real_appr = real_node(appearance) if appearance is not None else None
    tex_node = (real_appr.getChildBySpec(('ImageTexture', 'PixelTexture'))
                if real_appr is not None else None)

    if tex_node is not None and tex_node.getSpec() == "ImageTexture":
        if image is None:
            image = _load_x3d_image(tex_node)
        if image is not None:
            material = _ensure_node_image_material(material, image)

    if material is None:
        material = bpy.data.materials.new(shape.getDefName() or "X3D_Material")
        material.use_nodes = True

    return material, image


def _split_indexed(values):
    """Split an X3D index field into per-face integer tuples."""
    if values is None:
        return []
    if isinstance(values, str):
        values = values.replace(',', ' ').split()
    faces = []
    current = []
    for value in values:
        if isinstance(value, str):
            value = value.strip()
            if not value:
                continue
        value = int(value)
        if value == -1:
            if len(current) >= 3:
                faces.append(tuple(current))
            current = []
        else:
            current.append(value)
    if len(current) >= 3:
        faces.append(tuple(current))
    return faces


def _assign_shape_uvs(mesh_data, face_tex_indices, tex_points):
    if not tex_points or not face_tex_indices:
        return
    try:
        uv_layer = mesh_data.uv_layers.get("X3D_UV") or mesh_data.uv_layers.new(name="X3D_UV")
        loop_index = 0
        for poly, tex_face in zip(mesh_data.polygons, face_tex_indices):
            for corner, tex_index in zip(range(poly.loop_start, poly.loop_start + poly.loop_total),
                                         tex_face):
                if 0 <= int(tex_index) < len(tex_points):
                    uv = tex_points[int(tex_index)]
                    if len(uv) >= 2:
                        uv_layer.data[corner].uv = (float(uv[0]), float(uv[1]))
                loop_index += 1
    except Exception as exc:
        print("HAnim X3D: UV assignment failed:", exc)


def _find_source_root(node):
    p = node
    while getattr(p, "parent", None) is not None:
        p = p.parent
    return p


def _parse_x3d_animation_metadata(filename):
    """Read only ROUTE/MenuItem/ScalarInterpolator metadata from the source X3D."""
    if not filename or not os.path.exists(filename):
        return None
    try:
        root = ET.parse(filename).getroot()
    except Exception as exc:
        print("HAnim X3D: XML animation metadata unavailable:", exc)
        return None

    nodes = {}
    for elem in root.iter():
        tag = elem.tag.rsplit("}", 1)[-1]
        if elem.get("DEF"):
            nodes[elem.get("DEF")] = (tag, elem)

    routes = []
    for elem in root.iter():
        if elem.tag.rsplit("}", 1)[-1] == "ROUTE":
            routes.append((
                elem.get("fromNode"), elem.get("fromField"),
                elem.get("toNode"), elem.get("toField")
            ))

    menus = []
    for elem in root.iter():
        if elem.tag.rsplit("}", 1)[-1] != "ProtoInstance" or elem.get("name") != "MenuItem":
            continue
        fields = {}
        for fv in elem:
            if fv.tag.rsplit("}", 1)[-1] == "fieldValue":
                fields[fv.get("name")] = fv.get("value", "")
        menu_id = elem.get("DEF")
        if menu_id:
            menus.append({
                "id": menu_id,
                "description": fields.get("description", menu_id),
            })

    return nodes, routes, menus


def _parse_x3d_numbers(value):
    if not value:
        return []
    return [float(v) for v in re.split(r'[\s,]+', value.strip()) if v]


def _menu_clock(metadata, menu_id):
    nodes, routes, menus = metadata
    from_map = {}
    for a, b, c, d in routes:
        from_map.setdefault((a, b), []).append((c, d))

    for target, field in from_map.get((menu_id, "startTime"), []):
        if field == "startTime":
            return target
    return None


def _menu_animation_graph(metadata, menu_id):
    nodes, routes, menus = metadata
    from_map = {}
    for a, b, c, d in routes:
        from_map.setdefault((a, b), []).append((c, d))

    clock = _menu_clock(metadata, menu_id)
    if not clock:
        return {}

    adapters = [
        target for target, field in from_map.get((clock, "fraction_changed"), [])
        if field == "set_fraction"
    ]

    result = {}
    for adapter in adapters:
        info = nodes.get(adapter)
        if not info or info[0] not in {"ScalarInterpolator", "FloatVertexAttribute"}:
            continue
        elem = info[1]
        keys = _parse_x3d_numbers(elem.get("key"))
        values = _parse_x3d_numbers(elem.get("keyValue"))
        if not keys or not values:
            continue
        values = values[:len(keys)]

        for target, field in from_map.get((adapter, "value_changed"), []):
            if field != "weight":
                continue
            result[target] = (keys, values)
    return result


_ID_TYPE_COLLECTIONS = {
    'OBJECT': 'objects',
    'ARMATURE': 'armatures',
    'KEY': 'shape_keys',
    'MESH': 'meshes',
}


def _resolve_tagged_datablock(action):
    id_type = action.get("x3d_target_id_type")
    id_name = action.get("x3d_target_id_name")
    if not id_type or not id_name:
        return None
    coll_name = _ID_TYPE_COLLECTIONS.get(id_type)
    if not coll_name:
        return None
    coll = getattr(bpy.data, coll_name, None)
    return coll.get(id_name) if coll else None


def _prettify_clock_name(def_name):
    text = def_name.replace('_', ' ')
    text = re.sub(r'(?<=[a-z0-9])(?=[A-Z])', ' ', text)
    text = re.sub(r'(?<=[A-Z])(?=[A-Z][a-z])', ' ', text)
    text = re.sub(r'(?<=[A-Za-z])(?=[0-9])', ' ', text)
    text = re.sub(r'\s+', ' ', text).strip()
    return text or def_name


def _collect_standalone_clocks(used_clock_defs):
    by_clock = {}
    for action in bpy.data.actions:
        clock_def = action.get("x3d_timesensor")
        if not clock_def or clock_def in used_clock_defs:
            continue
        by_clock.setdefault(clock_def, []).append(action)

    items = []
    for clock_def in by_clock:
        items.append({
            "id": clock_def,
            "description": _prettify_clock_name(clock_def),
        })
    return items


def _register_animation_ui():
    try:
        bpy.types.Scene.hanim_x3d_active_menu
    except AttributeError:
        bpy.types.Scene.hanim_x3d_active_menu = bpy.props.StringProperty(
            name="X3D Animation", default=""
        )

    class X3D_HANIM_OT_PlayMenu(bpy.types.Operator):
        bl_idname = "hanim_x3d.play_menu"
        bl_label = "Play X3D Animation"
        menu_id: bpy.props.StringProperty()

        def execute(self, context):
            _activate_hanim_menu(self.menu_id)
            return {'FINISHED'}

    class X3D_HANIM_PT_Menu(bpy.types.Panel):
        bl_label = "X3D HAnim Menu"
        bl_idname = "X3D_HANIM_PT_Menu"
        bl_space_type = 'VIEW_3D'
        bl_region_type = 'UI'
        bl_category = "X3D"

        def draw(self, context):
            layout = self.layout
            items = []
            raw = context.scene.get("hanim_menu_items")
            if raw:
                try:
                    items = json.loads(raw)
                except Exception:
                    items = []
            if not items:
                for sk in bpy.data.shape_keys:
                    raw = sk.get("hanim_menu_items")
                    if raw:
                        try:
                            items = json.loads(raw)
                        except Exception:
                            pass
                        if items:
                            break
            if not items:
                layout.label(text="No X3D MenuItems found")
                return
            for item in items:
                op = layout.operator(
                    "hanim_x3d.play_menu",
                    text=item["description"],
                    depress=(context.scene.hanim_x3d_active_menu == item["id"])
                )
                op.menu_id = item["id"]

    for cls in (X3D_HANIM_OT_PlayMenu, X3D_HANIM_PT_Menu):
        try:
            bpy.utils.register_class(cls)
        except ValueError:
            pass


def _assign_action(datablock, action):
    if datablock is None or action is None:
        return
    datablock.animation_data_create()
    datablock.animation_data.action = action
    try:
        suitable = datablock.animation_data.action_suitable_slots
        if suitable:
            datablock.animation_data.action_slot = suitable[0]
    except (AttributeError, RuntimeError):
        pass


def _activate_hanim_menu(menu_id):
    scene = bpy.context.scene

    for sk in bpy.data.shape_keys:
        if sk.get("hanim_menu_items"):
            if sk.animation_data:
                sk.animation_data.action = None
            for kb in sk.key_blocks:
                kb.value = 0.0

    for action in bpy.data.actions:
        if not action.get("x3d_timesensor"):
            continue
        target = _resolve_tagged_datablock(action)
        if target is not None and target.animation_data and target.animation_data.action is action:
            target.animation_data.action = None

    if menu_id == "Reset":
        scene.hanim_x3d_active_menu = "Reset"
        return

    matched = False
    for sk in bpy.data.shape_keys:
        raw = sk.get("hanim_menu_actions")
        if not raw:
            continue
        try:
            actions = json.loads(raw)
        except Exception:
            continue
        action_name = actions.get(menu_id)
        if action_name:
            action = bpy.data.actions.get(action_name)
            if action:
                _assign_action(sk, action)
                matched = True

    if not matched:
        for action in bpy.data.actions:
            if action.get("x3d_timesensor") != menu_id:
                continue
            target = _resolve_tagged_datablock(action)
            if target is not None:
                _assign_action(target, action)

    scene.hanim_x3d_active_menu = menu_id


def _build_hanim_animation_actions(humanoid_node):
    filename = getattr(humanoid_node, "getFilename", lambda: None)()
    metadata = _parse_x3d_animation_metadata(filename)
    if not metadata:
        return

    _, _, menus = metadata
    menu_map = {m["id"]: m for m in menus}

    displacer_map = {}
    for sk in bpy.data.shape_keys:
        raw = sk.get(prop("displacers"))
        if not raw:
            continue
        try:
            info = json.loads(raw)
        except Exception:
            continue
        for key_name, meta in info.items():
            def_name = meta.get("def_name")
            if def_name:
                displacer_map[def_name] = (sk, key_name)

    if displacer_map:
        for sk in bpy.data.shape_keys:
            relevant = {d: v for d, v in displacer_map.items() if v[0] == sk}
            if not relevant:
                continue

            action_names = {}
            for menu_id, menu in menu_map.items():
                if menu_id == "Reset":
                    continue
                graph = _menu_animation_graph(metadata, menu_id)
                if not graph:
                    continue

                targets = [(def_name, key_name, graph[def_name])
                           for def_name, (_, key_name) in relevant.items()
                           if def_name in graph]
                if not targets:
                    continue

                action = bpy.data.actions.new(
                    f"X3D_{menu_id}_{sk.name}"
                )
                action["hanim_menu_id"] = menu_id
                action["hanim_source"] = filename or ""

                sk.animation_data_create()
                sk.animation_data.action = action

                for _, key_name, (keys, values) in targets:
                    fcurve = action.fcurve_ensure_for_datablock(
                        sk,
                        data_path=f'key_blocks["{key_name}"].value',
                        index=0,
                    )
                    for key, value in zip(keys, values):
                        frame = 1.0 + float(key) * 29.0
                        fcurve.keyframe_points.insert(frame, float(value), options={'FAST'})
                    fcurve.update()
                    if not any(mod.type == 'CYCLES' for mod in fcurve.modifiers):
                        fcurve.modifiers.new(type='CYCLES')

                action_names[menu_id] = action.name

            if sk.animation_data:
                sk.animation_data.action = None

            if action_names:
                sk["hanim_menu_actions"] = json.dumps(action_names)
                sk["hanim_menu_items"] = json.dumps(
                    [m for m in menus],
                    separators=(",", ":")
                )

    _pending_menu_metadata.append(metadata)
    print("HAnim X3D: found", len(menu_map), "MenuItem(s) for", filename or humanoid_node)


_pending_menu_metadata = []


def finalize_animation_menu():
    global _pending_menu_metadata

    all_menus = []
    used_clock_defs = set()
    for metadata in _pending_menu_metadata:
        _, _, menus = metadata
        all_menus.extend(menus)
        for menu in menus:
            menu_id = menu.get("id")
            if not menu_id or menu_id == "Reset":
                continue
            clock = _menu_clock(metadata, menu_id)
            if clock:
                used_clock_defs.add(clock)

    standalone_items = _collect_standalone_clocks(used_clock_defs)
    combined_items = all_menus + standalone_items

    if combined_items:
        bpy.context.scene["hanim_menu_items"] = json.dumps(
            combined_items, separators=(",", ":")
        )

    _register_animation_ui()
    print(
        "HAnim X3D: installed", len(all_menus), "MenuItem(s) and",
        len(standalone_items), "standalone TimeSensor(s) as Blender animation controls."
    )

    _pending_menu_metadata = []


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

    consumed_ids = {id(humanoid_node), id(real_node(humanoid_node))}
    consumed_ids.update(id(n) for n in root_joints)
    consumed_ids.update(id(real_node(n)) for n in root_joints)

    humanoid_node.blendObject = armature_obj
    humanoid_node.blendData = armature_obj.data
    real_node(humanoid_node).blendObject = armature_obj
    real_node(humanoid_node).blendData = armature_obj.data

    body_mesh_obj = None
    skin_coord_node = humanoid_node.getChildBySpec('Coordinate')
    skin_shape_node = humanoid_node.getChildBySpec('Shape')

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

    _build_hanim_animation_actions(humanoid_node)

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
        consumed_ids.add(id(real_node(child)))
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
                import_displacers(body_mesh_obj, child)
            else:
                import_segment(context, child, armature_obj, joint_bone_name,
                               collection, shared_mesh_data=None)
            _consume_subtree(child, consumed_ids)

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

    root_joints = [
        n for n in top_level_real_children
        if n.getSpec() == 'HAnimJoint' and getattr(n, 'parent', None) == humanoid_node
    ]
    if len(root_joints) > 1:
        named_roots = [j for j in root_joints if "root" in get_field(j, "name", "").lower()]
        root_joints = named_roots if named_roots else root_joints[:1]

    for root in root_joints:
        _import_joint_recursive(armature_data, root, armature_obj=armature_obj,
                                parent_bone_name=None,
                                parent_matrix=Matrix.Identity(4),
                                joint_bone_names=joint_bone_names,
                                bone_custom_props=bone_custom_props,
                                world_matrices=world_matrices)

    resolve_bone_tails(armature_data, world_matrices)

    bpy.ops.object.mode_set(mode='OBJECT')

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

        # Explicitly align bone roll to avoid Blender's Damped Track -Y singularity
        # where local axes can flip 180 degrees.
        # In H-Anim: +Y is UP, +Z is FORWARD, +X is LATERAL (humanoid's left).
        bone_vec = bone.tail - bone.head
        if bone_vec.length > 1e-6:
            y_comp = bone_vec.normalized().y
            if y_comp < -0.5:
                # Downward bones (legs, arms hanging down):
                # Aligning local Z to (0, 0, -1) makes local X = (-Y) x (-Z) = (+X, 0, 0)
                bone.align_roll(Vector((0.0, 0.0, -1.0)))
            elif y_comp > 0.5:
                # Upward bones (spine, neck, head):
                # Aligning local Z to (0, 0, 1) makes local X = (+Y) x (+Z) = (+X, 0, 0)
                bone.align_roll(Vector((0.0, 0.0, 1.0)))
            else:
                # Horizontal or angled bones (arms in T-pose, feet):
                bone.align_roll(Vector((0.0, 0.0, 1.0)))


def _leaf_tail_direction(bone, world_matrices):
    world_matrix = world_matrices.get(bone.name)
    length_ref = bone.parent.length * 0.5 if bone.parent else 0.05
    length_ref = max(length_ref, 0.01)
    if world_matrix is not None:
        y_axis = world_matrix.to_3x3() @ Vector((0.0, 1.0, 0.0))
        if y_axis.length > 1e-6:
            return y_axis.normalized() * length_ref
    return Vector((0.0, length_ref, 0.0))


def _import_joint_recursive(armature_data, joint_node, armature_obj=None,
                            parent_bone_name=None, parent_matrix=None,
                            joint_bone_names=None, bone_custom_props=None,
                            world_matrices=None):
    if parent_matrix is None:
        parent_matrix = Matrix.Identity(4)
    if joint_bone_names is None:
        joint_bone_names = {}
    if bone_custom_props is None:
        bone_custom_props = {}
    if world_matrices is None:
        world_matrices = {}

    joint_name = get_field(joint_node, "name", "Joint")
    bone = armature_data.edit_bones.new(joint_name)
    joint_bone_names[joint_name] = bone.name

    if armature_obj is not None:
        joint_node.blendObject = armature_obj
        joint_node.blendData = bone.name
        real_node(joint_node).blendObject = armature_obj
        real_node(joint_node).blendData = bone.name

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
            _import_joint_recursive(armature_data, child, armature_obj=armature_obj,
                                    parent_bone_name=bone.name,
                                    parent_matrix=world_matrix,
                                    joint_bone_names=joint_bone_names,
                                    bone_custom_props=bone_custom_props,
                                    world_matrices=world_matrices)


def _collect_segment_shapes(node, current_matrix, shape_list):
    """Walks Transform/Group wrappers within a segment collecting (Shape, cumulative_matrix)."""
    for child in get_children(node):
        spec = child.getSpec()
        if spec == 'Transform':
            tx_mat = get_node_transform_matrix(child)
            _collect_segment_shapes(child, current_matrix @ tx_mat, shape_list)
        elif spec == 'Shape':
            shape_list.append((child, current_matrix))
        elif spec in ('Group', 'StaticGroup'):
            _collect_segment_shapes(child, current_matrix, shape_list)


def import_segment(context, segment_node, armature_obj, joint_bone_name,
                   collection, shared_mesh_data=None):
    seg_name = get_field(segment_node, "name", "Segment")
    uses_shared_skin = shared_mesh_data is not None

    if uses_shared_skin:
        mesh_obj = bpy.data.objects.new(seg_name, shared_mesh_data)
        mesh_obj.parent = armature_obj
    else:
        mesh_data = bpy.data.meshes.new(seg_name)
        primary_matrix = import_segment_own_geometry(mesh_data, segment_node)
        mesh_obj = bpy.data.objects.new(seg_name, mesh_data)
        mesh_obj.parent = armature_obj
        if joint_bone_name and joint_bone_name in armature_obj.data.bones:
            mesh_obj.parent_type = 'BONE'
            mesh_obj.parent_bone = joint_bone_name

    collection.objects.link(mesh_obj)

    segment_node.blendObject = mesh_obj
    segment_node.blendData = mesh_obj.data
    real_node(segment_node).blendObject = mesh_obj
    real_node(segment_node).blendData = mesh_obj.data

    if uses_shared_skin:
        modifier = mesh_obj.modifiers.new(name="HAnimSkin", type='ARMATURE')
        modifier.object = armature_obj

    import_displacers(mesh_obj, segment_node, primary_matrix if not uses_shared_skin else Matrix.Identity(4))

    for field_name in SEGMENT_PROPS:
        val = get_field(segment_node, field_name)
        if val:
            mesh_obj[prop(field_name)] = val
    mesh_obj[prop("node_type")] = "Segment"
    mesh_obj[prop("uses_shared_skin")] = uses_shared_skin

    return mesh_obj


def import_segment_own_geometry(mesh_data, segment_node):
    """Import segment geometry, preserving per-Shape materials and X3D UVs."""
    verts = []
    faces = []
    face_materials = []
    face_tex_indices = []
    materials = []
    material_slots = {}
    vertex_offset = 0

    shape_list = []
    _collect_segment_shapes(segment_node, Matrix.Identity(4), shape_list)
    primary_matrix = shape_list[0][1] if shape_list else Matrix.Identity(4)

    for shape, matrix in shape_list:
        geometry = (shape.getChildBySpec('IndexedFaceSet') or
                    shape.getChildBySpec('IndexedTriangleSet') or
                    shape.getChildBySpec('IndexedTriangleStripSet') or
                    shape.getChildBySpec('IndexedTriangleFanSet') or
                    shape.getChildBySpec('TriangleSet'))
        if geometry is None:
            continue

        geo_type = geometry.getSpec()
        coord_node = geometry.getChildBySpec('Coordinate')
        points = get_field(coord_node, "point", []) if coord_node else []
        raw_verts = _grouped(points, 3)

        for pt in raw_verts:
            verts.append((matrix @ Vector(pt)).to_tuple())

        local_faces = []
        local_tex_faces = []

        if geo_type == "IndexedFaceSet":
            coord_index = get_field(geometry, "coordIndex", [])
            local_faces = _split_indexed(coord_index)

            tex_node = geometry.getChildBySpec('TextureCoordinate')
            tex_points = get_field(tex_node, "point", []) if tex_node else []
            tex_points = _grouped(tex_points, 2)

            tex_index = get_field(geometry, "texCoordIndex", [])
            if tex_index:
                local_tex_faces = _split_indexed(tex_index)
            elif tex_points:
                local_tex_faces = [tuple(f) for f in local_faces]
        else:
            index = get_field(geometry, "index", [])
            if index:
                for i in range(0, len(index) - 2, 3):
                    local_faces.append(tuple(index[i:i + 3]))
            else:
                for i in range(0, len(raw_verts) - 2, 3):
                    local_faces.append((i, i + 1, i + 2))
            tex_node = geometry.getChildBySpec('TextureCoordinate')
            tex_points = get_field(tex_node, "point", []) if tex_node else []
            tex_points = _grouped(tex_points, 2)
            if tex_points:
                local_tex_faces = [tuple(f) for f in local_faces]

        for face, tex_face in zip(
                local_faces,
                local_tex_faces if local_tex_faces else [()] * len(local_faces)):
            faces.append(tuple(vertex_offset + i for i in face))
            face_tex_indices.append(tex_face)

        appr = shape.getChildBySpec('Appearance')
        bpymat, _ = _apply_shape_appearance(shape, appr, ())
        mat_key = bpymat.name
        if mat_key not in material_slots:
            material_slots[mat_key] = len(materials)
            materials.append(bpymat)
        slot = material_slots[mat_key]

        face_materials.extend([slot] * len(local_faces))
        vertex_offset += len(raw_verts)

    mesh_data.from_pydata(verts, [], faces)
    mesh_data.update()

    for mat in materials:
        mesh_data.materials.append(mat)

    for poly, slot in zip(mesh_data.polygons, face_materials):
        poly.material_index = slot

    if face_tex_indices:
        uv_layer = mesh_data.uv_layers.new(name="X3D_UV") if not mesh_data.uv_layers else mesh_data.uv_layers[0]
        flat_uv = []
        for shape, matrix in shape_list:
            geometry = shape.getChildBySpec('IndexedFaceSet')
            if geometry is None:
                continue
            tex_node = geometry.getChildBySpec('TextureCoordinate')
            tex_points = _grouped(get_field(tex_node, "point", []) if tex_node else [], 2)
            if not tex_points:
                continue
            local_faces = _split_indexed(get_field(geometry, "coordIndex", []))
            tex_index = get_field(geometry, "texCoordIndex", [])
            local_tex_faces = (_split_indexed(tex_index) if tex_index
                               else [tuple(f) for f in local_faces])
            for tf in local_tex_faces:
                for ti in tf:
                    if 0 <= int(ti) < len(tex_points):
                        flat_uv.append(tuple(tex_points[int(ti)][:2]))
                    else:
                        flat_uv.append((0.0, 0.0))

        for loop, uv in zip(mesh_data.loops, flat_uv):
            uv_layer.data[loop.index].uv = uv

    return primary_matrix


def import_displacers(mesh_obj, segment_node, transform_matrix=Matrix.Identity(4)):
    """Imports HAnimDisplacer child nodes as Blender Shape Keys."""
    displacer_nodes = segment_node.getChildrenBySpec('HAnimDisplacer')
    if not displacer_nodes:
        return

    num_verts = len(mesh_obj.data.vertices)
    if num_verts == 0:
        return

    if not mesh_obj.data.shape_keys:
        mesh_obj.shape_key_add(name="Basis", from_mix=False)

    basis_key = mesh_obj.data.shape_keys.key_blocks[0]
    rot_scale_mat = transform_matrix.to_3x3()

    key = prop("displacers")
    raw = mesh_obj.get(key, None)
    try:
        displacers_meta = json.loads(raw) if raw else {}
    except Exception:
        displacers_meta = {}

    for disp_node in displacer_nodes:
        disp_name = get_field(disp_node, "name", "Displacer")
        disp_weight = get_field(disp_node, "weight", 0.0)
        coord_indices = get_field(disp_node, "coordIndex", [])
        displacements_raw = get_field(disp_node, "displacements", [])
        displacements = _grouped(displacements_raw, 3)

        shape_key = mesh_obj.shape_key_add(name=disp_name, from_mix=False)
        shape_key.value = float(disp_weight)

        for idx, delta in zip(coord_indices, displacements):
            if 0 <= idx < num_verts:
                d_vec = rot_scale_mat @ Vector(delta)
                shape_key.data[idx].co = basis_key.data[idx].co + d_vec

        def_name = disp_node.getDefName()
        displacers_meta[shape_key.name] = {
            "name": disp_name,
            "def_name": def_name,
            "coordIndex": list(coord_indices),
            "displacements": list(displacements_raw),
        }

        disp_node.blendObject = mesh_obj
        disp_node.blendData = shape_key
        real_node(disp_node).blendObject = mesh_obj
        real_node(disp_node).blendData = shape_key

    raw_displacers = json.dumps(displacers_meta)
    mesh_obj[key] = raw_displacers
    if mesh_obj.data.shape_keys is not None:
        mesh_obj.data.shape_keys[key] = raw_displacers


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

    site_node.blendObject = empty
    site_node.blendData = empty
    real_node(site_node).blendObject = empty
    real_node(site_node).blendData = empty

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

        displacers = []
        if mesh_obj.data.shape_keys:
            basis_key = mesh_obj.data.shape_keys.key_blocks[0]
            raw_meta = mesh_obj.get(prop("displacers"), None)
            try:
                displacers_meta = json.loads(raw_meta) if raw_meta else {}
            except Exception:
                displacers_meta = {}

            for key_block in mesh_obj.data.shape_keys.key_blocks[1:]:
                meta = displacers_meta.get(key_block.name, {})
                stored_ci = meta.get("coordIndex")
                stored_disp = meta.get("displacements")
                disp_name = meta.get("name", key_block.name)
                def_name = meta.get("def_name")

                if stored_ci is not None and stored_disp is not None:
                    ci = list(stored_ci)
                    disp = list(stored_disp)
                else:
                    ci = []
                    disp = []
                    for v_idx, (kb_pt, basis_pt) in enumerate(zip(key_block.data, basis_key.data)):
                        delta = kb_pt.co - basis_pt.co
                        if delta.length > 1e-5:
                            ci.append(v_idx)
                            disp.extend(delta[:])

                displacer_dict = {
                    "node_type": "HAnimDisplacer",
                    "name": disp_name,
                    "weight": key_block.value,
                    "coordIndex": ci,
                    "displacements": disp,
                }
                if def_name:
                    displacer_dict["DEF"] = def_name
                displacers.append(displacer_dict)

        if displacers:
            seg["displacers"] = displacers

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
