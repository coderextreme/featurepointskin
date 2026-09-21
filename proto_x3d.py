# SPDX-License-Identifier: GPL-3.0-or-later
"""
proto_x3d.py

X3D Prototype (ProtoDeclare, ProtoInterface, ProtoBody, ProtoInstance)
support for the io_scene_x3d Blender extension.
"""

import logging
from xml.dom import minidom

logger = logging.getLogger("import_x3d.proto")


class ProtoField:
    """Represents a declared field in a ProtoInterface."""

    def __init__(self, name, field_type, access_type='inputOutput', default_value=None, default_nodes=None):
        self.name = name
        self.field_type = field_type
        self.access_type = access_type
        self.default_value = default_value
        self.default_nodes = default_nodes or []


class ProtoDeclare:
    """Represents a prototype declaration with its interface and body."""

    def __init__(self, name, declare_element):
        self.name = name
        self.declare_element = declare_element
        self.fields = {}
        self.body_element = None
        self._parse()

    def _parse(self):
        for child in self.declare_element.childNodes:
            if child.nodeType != child.ELEMENT_NODE:
                continue
            tag = child.tagName
            if tag == 'ProtoInterface':
                for f_node in child.childNodes:
                    if f_node.nodeType == f_node.ELEMENT_NODE and f_node.tagName == 'field':
                        f_name = f_node.getAttribute('name')
                        f_type = f_node.getAttribute('type')
                        f_access = f_node.getAttribute('accessType') or 'inputOutput'
                        f_val = f_node.getAttribute('value') if f_node.hasAttribute('value') else None
                        f_child_nodes = [c for c in f_node.childNodes if c.nodeType == c.ELEMENT_NODE]
                        self.fields[f_name] = ProtoField(f_name, f_type, f_access, f_val, f_child_nodes)
            elif tag == 'ProtoBody':
                self.body_element = child


class ProtoManager:
    """Manages prototype declarations, instance expansions, and adapter clock associations."""

    def __init__(self):
        self.protos = {}
        self.adapter_clocks = {}
        self._instance_count = 0

    def reset(self):
        self.protos.clear()
        self.adapter_clocks.clear()
        self._instance_count = 0

    def register_proto_declare(self, declare_element):
        name = declare_element.getAttribute('name')
        if not name:
            logger.warning("ProtoDeclare without name attribute")
            return None
        proto = ProtoDeclare(name, declare_element)
        self.protos[name] = proto
        return proto

    # ------------------------------------------------------------------
    # Pure-DOM instance resolution (no dependency on Blender's x3dNode
    # tree). Kept separate from expand_proto_instance() so it can be
    # exercised directly in tests, and so nested ProtoInstance elements
    # get resolved the same way whether they are top-level or buried
    # inside another proto's ProtoBody.
    # ------------------------------------------------------------------
    def resolve_proto_instance_dom(self, proto_name, instance_element):
        """Clone the named proto's body, resolve IS/connect wiring against
        the fieldValues carried on `instance_element`, and return
        (cloned_body, instance_def, def_map, suffix).

        Returns None if the proto is unknown or has no body.
        """
        if proto_name not in self.protos:
            logger.warning("ProtoInstance references unknown proto: %s", proto_name)
            return None

        proto = self.protos[proto_name]
        if not proto.body_element:
            logger.warning("Proto %s has no ProtoBody", proto_name)
            return None

        self._instance_count += 1
        inst_id = self._instance_count

        # 1. Collect field values from ProtoInstance <fieldValue> children
        field_values = {}
        field_nodes = {}
        for child in instance_element.childNodes:
            if child.nodeType == child.ELEMENT_NODE and child.tagName == 'fieldValue':
                fv_name = child.getAttribute('name')
                if child.hasAttribute('value'):
                    field_values[fv_name] = child.getAttribute('value')
                elem_children = [c for c in child.childNodes if c.nodeType == c.ELEMENT_NODE]
                if elem_children:
                    field_nodes[fv_name] = elem_children

        # Fallback to interface defaults
        for f_name, f_def in proto.fields.items():
            if f_name not in field_values and f_def.default_value is not None:
                field_values[f_name] = f_def.default_value
            if f_name not in field_nodes and f_def.default_nodes:
                field_nodes[f_name] = f_def.default_nodes

        # Derive a human-readable suffix from menuItemString or description
        suffix = ""
        if 'menuItemString' in field_values:
            suffix = "_" + field_values['menuItemString'].replace('"', '').replace("'", "").strip()
        elif 'description' in field_values:
            suffix = "_" + "".join(c for c in field_values['description'] if c.isalnum())
        if not suffix:
            suffix = f"_{inst_id}"

        # 2. Deep clone ProtoBody DOM
        cloned_body = proto.body_element.cloneNode(deep=True)
        self._set_cloned_positions(cloned_body)

        # 3. Resolve <IS><connect nodeField="..." protoField="..."/></IS>
        #
        # The parent of an <IS> can be either:
        #   (a) an ordinary X3D node (e.g. <Transform>) - field values are
        #       written as XML attributes, node-valued fields as direct
        #       element children, or
        #   (b) another <ProtoInstance> nested inside this proto's body
        #       (this is how a field gets *forwarded* into a deeper proto -
        #       exactly what rubikFurnace.x3d does to push "myShape", a Box
        #       overriding the default Sphere, down through
        #       twentyseven -> nine -> three -> anyShape). ProtoInstance
        #       does not take bare attributes or bare node children for its
        #       fields - it requires <fieldValue name="..."> wrapper
        #       elements, so those must be created (or reused) here rather
        #       than writing straight onto the element.
        is_elements = list(cloned_body.getElementsByTagName('IS'))

        for is_elem in is_elements:
            parent_elem = is_elem.parentNode
            if not parent_elem:
                continue

            forwarding_into_proto_instance = (parent_elem.tagName == 'ProtoInstance')

            for conn in list(is_elem.childNodes):
                if conn.nodeType == conn.ELEMENT_NODE and conn.tagName == 'connect':
                    node_field = conn.getAttribute('nodeField')
                    proto_field = conn.getAttribute('protoField')

                    if forwarding_into_proto_instance:
                        target_fv = self._get_or_create_field_value(parent_elem, node_field)
                        if proto_field in field_values:
                            target_fv.setAttribute('value', field_values[proto_field])
                        if proto_field in field_nodes:
                            for fn in field_nodes[proto_field]:
                                cloned_fn = fn.cloneNode(deep=True)
                                self._set_cloned_positions(cloned_fn)
                                target_fv.appendChild(cloned_fn)
                    else:
                        if proto_field in field_values:
                            parent_elem.setAttribute(node_field, field_values[proto_field])
                        if proto_field in field_nodes:
                            for fn in field_nodes[proto_field]:
                                cloned_fn = fn.cloneNode(deep=True)
                                self._set_cloned_positions(cloned_fn)
                                parent_elem.appendChild(cloned_fn)

            if is_elem.parentNode:
                is_elem.parentNode.removeChild(is_elem)

        # 4. Scope inner DEF names and update internal ROUTEs
        def_map = {}
        for elem in cloned_body.getElementsByTagName('*'):
            if elem.hasAttribute('DEF'):
                old_def = elem.getAttribute('DEF')
                new_def = f"{old_def}{suffix}"
                elem.setAttribute('DEF', new_def)
                def_map[old_def] = new_def

        for elem in cloned_body.getElementsByTagName('ROUTE'):
            from_node = elem.getAttribute('fromNode')
            to_node = elem.getAttribute('toNode')
            if from_node in def_map:
                elem.setAttribute('fromNode', def_map[from_node])
            if to_node in def_map:
                elem.setAttribute('toNode', def_map[to_node])

        # 5. Check for adapter connection (e.g. MenuItem adapter -> Main_Clock)
        if 'adapter' in field_nodes:
            for fn in field_nodes['adapter']:
                use_ref = fn.getAttribute('USE')
                if use_ref:
                    clock_def = def_map.get('Main_Clock', f"Main_Clock{suffix}")
                    self.adapter_clocks[use_ref] = clock_def

        instance_def = instance_element.getAttribute('DEF')

        return cloned_body, instance_def, def_map, suffix

    def _get_or_create_field_value(self, proto_instance_elem, field_name):
        """Find the <fieldValue name="field_name"> child of a ProtoInstance
        element, creating and appending one if it doesn't exist yet."""
        for c in proto_instance_elem.childNodes:
            if c.nodeType == c.ELEMENT_NODE and c.tagName == 'fieldValue' and c.getAttribute('name') == field_name:
                return c
        doc = proto_instance_elem.ownerDocument
        fv = doc.createElement('fieldValue')
        fv.setAttribute('name', field_name)
        proto_instance_elem.appendChild(fv)
        return fv

    def expand_proto_instance(self, parent_x3d_node, instance_element, x3d_node_class, node_normal_type):
        proto_name = instance_element.getAttribute('name')

        resolved = self.resolve_proto_instance_dom(proto_name, instance_element)
        if resolved is None:
            return None
        cloned_body, instance_def, def_map, suffix = resolved

        # 6. Create the x3dNode for the ProtoInstance itself
        instance_node = x3d_node_class(parent_x3d_node, node_normal_type, instance_element)
        if instance_def:
            instance_node.getDefDict()[instance_def] = instance_node

        # 7. Parse the cloned body's elements into the x3dNode tree
        for child_elem in list(cloned_body.childNodes):
            if child_elem.nodeType != child_elem.ELEMENT_NODE:
                continue

            child_x3d = x3d_node_class(instance_node, node_normal_type, child_elem)
            child_x3d.parse()

            if 'Main_Clock' not in instance_node.getDefDict() and 'Main_Clock' in def_map:
                clock_key = def_map['Main_Clock']
                if clock_key in instance_node.getDefDict():
                    instance_node.getDefDict()['Main_Clock'] = instance_node.getDefDict()[clock_key]

        return instance_node

    def _set_cloned_positions(self, node):
        node.parse_position = (-1, -1)
        for child in getattr(node, 'childNodes', []):
            if child.nodeType == child.ELEMENT_NODE:
                self._set_cloned_positions(child)


# Global singleton instance
manager = ProtoManager()


def get_manager():
    global manager
    if manager is None:
        manager = ProtoManager()
    return manager


def reset():
    get_manager().reset()


def register_proto_declare(declare_element):
    return get_manager().register_proto_declare(declare_element)


def expand_proto_instance(parent_x3d_node, instance_element, x3d_node_class, node_normal_type):
    return get_manager().expand_proto_instance(parent_x3d_node, instance_element, x3d_node_class, node_normal_type)


def __getattr__(name):
    if name == "manager":
        return get_manager()
    if name == "adapter_clocks":
        return get_manager().adapter_clocks
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
