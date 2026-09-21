"""
Standalone test: walks the nested ProtoInstance chain in rubikFurnace.x3d
(twentyseven -> nine -> three -> anyShape) purely through
ProtoManager.resolve_proto_instance_dom(), recursively expanding any
ProtoInstance elements it finds in a cloned body - exactly what the real
Blender import loop does when x3dNode.parse() encounters a ProtoInstance,
except here we stay in plain minidom so this needs no Blender dependency.
"""
from xml.dom import minidom
import proto_x3d


def recursively_expand(pm, element):
    """Replace every ProtoInstance element under `element` (in place) with
    its fully resolved ProtoBody content, recursing into nested instances."""
    for child in list(element.childNodes):
        if child.nodeType != child.ELEMENT_NODE:
            continue
        if child.tagName == 'ProtoInstance':
            proto_name = child.getAttribute('name')
            resolved = pm.resolve_proto_instance_dom(proto_name, child)
            if resolved is None:
                continue
            cloned_body, instance_def, def_map, suffix = resolved
            # splice the resolved body's children in place of the ProtoInstance
            for body_child in list(cloned_body.childNodes):
                element.insertBefore(body_child, child)
            element.removeChild(child)
            # recurse into what we just spliced in (may contain further
            # nested ProtoInstance elements, e.g. nine -> three -> anyShape)
            recursively_expand(pm, element)
            return  # childNodes list mutated; restart the scan
        else:
            recursively_expand(pm, child)


doc = minidom.parse('rubikFurnace.x3d')
scene = doc.getElementsByTagName('Scene')[0]

pm = proto_x3d.ProtoManager()

top_level_instance = None
for child in list(scene.childNodes):
    if child.nodeType == child.ELEMENT_NODE:
        if child.tagName == 'ProtoDeclare':
            pm.register_proto_declare(child)
        elif child.tagName == 'ProtoInstance':
            top_level_instance = child

assert top_level_instance is not None, "no top-level ProtoInstance found"

# Resolve just the top-level instance (twentyseven), then recurse into
# the resolved body to expand the nested ProtoInstances it contains
# (nine -> three -> anyShape). We deliberately never touch the
# ProtoDeclare template bodies still sitting in <Scene> - those hold
# their own (unexpanded) nested-ProtoInstance "recipes" with default
# Sphere shapes and must be left alone.
resolved = pm.resolve_proto_instance_dom('twentyseven', top_level_instance)
assert resolved is not None
top_cloned_body, _, _, _ = resolved
recursively_expand(pm, top_cloned_body)

xml_out = top_cloned_body.toprettyxml(indent="  ")
sphere_count = xml_out.count('<Sphere')
box_count = xml_out.count('<Box')

print(f"Sphere elements remaining: {sphere_count}")
print(f"Box elements present:      {box_count}")
print()
print("Sample of expanded output:")
print("\n".join(xml_out.splitlines()[:40]))

assert sphere_count == 0, "FAIL: a Sphere survived - override did not propagate"
assert box_count == 27, f"FAIL: expected 27 Box shapes (one per cube cell), got {box_count}"
print("\nPASS: all 27 leaf shapes are Box, no Sphere remains.")
