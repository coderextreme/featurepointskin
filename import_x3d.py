# SPDX-FileCopyrightText: 2011-2024 Blender Foundation
#
# SPDX-License-Identifier: GPL-3.0-or-later

import logging
from http.cookiejar import debug

logger = logging.getLogger("import_x3d")

DEBUG = False

import os
import shlex
import math
import re
import mathutils
from math import sin, cos, pi
from itertools import chain
from . import mfstring
from . import hanim_x3d

try:
    from . import proto_x3d
except Exception:
    proto_x3d = None

texture_cache = {}
material_cache = {}
font_variants_cache = {}
download_cache = {}
current_file_path = None
conversion_scale = 1.0

EPSILON = 0.0000001


def vrml_find_quote(text, j=0):
    while j < len(text):
        if text[j] == '"':
            return j
        if text[j:j + 2] in {'\\"', '\\\\'}:
            j += 2
        else:
            j += 1
    return -1


def vrml_count_quote(text):
    returnCount = 0
    j = 0
    LOOP_GUARD = 64
    while j < len(text):
        LOOP_GUARD -= 1
        if LOOP_GUARD < 0:
            raise Exception("infinite loop error in vrml_count_quote")

        nj = text.find('"', j)
        if nj == -1:
            break
        returnCount += 1

        nnj = vrml_find_quote(text, nj + 1)
        if nnj == -1:
            break
        returnCount += 1

        j = nnj + 1
    return returnCount


vrml_split_pattern = re.compile(r"(?:,\s*)|(?:\s+,?\s*)")


def vrml_split(text):
    original_text = text
    result = []
    prev_length = None

    while text:
        if prev_length is not None and len(text) >= prev_length:
            raise Exception("Infinite loop detected in vrml_split")
        prev_length = len(text)

        text = text[vrml_split_pattern.match(text).end():] if vrml_split_pattern.match(text) else text
        if not text:
            break

        if text.startswith('"'):
            end_idx = vrml_find_quote(text, 1)
            if end_idx == -1:
                logger.error("Unterminated SFString value: |%s|", text)
                break
            result.append(text[:end_idx + 1])
            text = text[end_idx + 1:]
        else:
            match = vrml_split_pattern.search(text)
            result.append(text[:match.start()] if match else text)
            text = text[match.end():] if match else ''

    logger.debug("vrml_split |%s| --> %s", original_text, result)
    return result


def imageConvertCompat(path):
    if os.sep == '\\':
        return path

    if path.lower().endswith('.gif'):
        path_to = path[:-3] + 'png'
        os.system('convert "%s" "%s"' % (path, path_to))
        if os.path.exists(path_to):
            return path_to

    return path


def vrml_split_fields(value):
    def iskey(k):
        if k[0] != '"' and k[0].isalpha() and k.upper() not in {'TRUE', 'FALSE'}:
            return True
        return False

    field_list = []
    field_context = []

    for v in value:
        if iskey(v):
            if field_context:
                field_context_len = len(field_context)
                if (field_context_len > 2) and (field_context[-2] in {'DEF', 'USE'}):
                    field_context.append(v)
                elif (not iskey(field_context[-1])) or ((field_context_len == 3 and field_context[1] == 'IS')):
                    field_list.append(field_context)
                    field_context = [v]
                else:
                    field_context.append(v)
            else:
                field_context.append(v)
        else:
            field_context.append(v)

    if field_context:
        field_list.append(field_context)

    return field_list


def vrmlFormat(data):
    def strip_comment(l):
        l = l.strip()
        if l.startswith('#'):
            return ''
        i = l.find('#')
        if i == -1:
            return l

        j = l.find('"')
        if j == -1:
            return l[:i].strip()

        q = False
        for idx, c in enumerate(l):
            if c == '"':
                q = not q
            elif c == '#':
                if q is False:
                    return l[:idx - 1]
        return l

    data = '\n'.join([strip_comment(l) for l in data.split('\n')])
    EXTRACT_STRINGS = True

    if EXTRACT_STRINGS:
        string_ls = []
        search = '"'
        ok = True
        last_i = 0

        while ok:
            ok = False
            i = data.find('"', last_i)
            if i != -1:
                start = i + len(search)
                end = vrml_find_quote(data, start)
                if end != -1:
                    item = data[start:end]
                    string_ls.append(item)
                    data = data[:start] + data[end:]
                    ok = True
                    last_i = (end - len(item)) + 1

    data = data.replace('{', '\n{\n')
    data = data.replace('}', '\n}\n')
    data = data.replace('[', '\n[\n')
    data = data.replace(']', '\n]\n')

    data = '\n'.join([' '.join(value) for l in data.split('\n') for value in vrml_split_fields(vrml_split(l))])
    if EXTRACT_STRINGS:
        search = '"'
        ok = True
        last_i = 0
        while ok:
            ok = False
            i = data.find(search + '"', last_i)
            if i != -1:
                start = i + len(search)
                item = string_ls.pop(0)
                data = data[:start] + item + data[start:]
                last_i = start + len(item) + 1
                ok = True

    def non_empty_line_generator(indata):
        for ll in indata.split("\n"):
            sll = ll.strip()
            if sll:
                yield sll

    return list(non_empty_line_generator(data))


NODE_NORMAL = 1
NODE_ARRAY = 2
NODE_REFERENCE = 3

lines = []


def getNodePreText(i, words):
    use_node = False
    while len(words) < 5:
        if i >= len(lines):
            break
        elif lines[i] == '{':
            return NODE_NORMAL, i + 1
        elif vrml_count_quote(lines[i]) % 2 != 0:
            break
        else:
            new_words = vrml_split(lines[i])
            if 'USE' in new_words:
                use_node = True
            words.extend(new_words)
            i += 1

        if use_node:
            words[:] = words[:words.index('USE') + 2]
            if lines[i] == '{' and lines[i + 1] == '}':
                i += 2
            return NODE_REFERENCE, i
    return 0, -1


def is_nodeline(i, words):
    if not lines[i][0].isalpha():
        return 0, 0

    if lines[i].startswith('PROTO'):
        words[:] = vrml_split(lines[i])
        return NODE_NORMAL, i + 1
    if lines[i].startswith('EXTERNPROTO'):
        words[:] = vrml_split(lines[i])
        return NODE_ARRAY, i + 1

    if lines[i + 1] == '[':
        if vrml_count_quote(lines[i]) % 2 == 0:
            words[:] = vrml_split(lines[i])
            return NODE_ARRAY, i + 2

    node_type, new_i = getNodePreText(i, words)
    if not node_type:
        return 0, 0

    for idx, val in enumerate(words):
        if idx != 0 and words[idx - 1] in {'DEF', 'USE'}:
            pass
        elif val[0].isalpha() and val not in {'TRUE', 'FALSE'}:
            pass
        else:
            return 0, 0
    return node_type, new_i


is_numline_init_skip_pattern = re.compile(r"\s*,?\s*")
is_numline_first_break_pattern = re.compile(r"\s|,|$")


def is_numline(i):
    l = lines[i]
    init_skip = is_numline_init_skip_pattern.match(l)
    if init_skip:
        first_break = is_numline_first_break_pattern.search(l, init_skip.end())
        if first_break:
            try:
                float(l[init_skip.end():first_break.start()])
                return True
            except:
                pass
    return False


class vrmlNode(object):
    __slots__ = ('id',
                 'fields',
                 'proto_node',
                 'proto_field_defs',
                 'proto_fields',
                 'node_type',
                 'parent',
                 'children',
                 'array_data',
                 'reference',
                 'lineno',
                 'filename',
                 'blendObject',
                 'blendData',
                 'DEF_NAMESPACE',
                 'ROUTE_IPO_NAMESPACE',
                 'PROTO_NAMESPACE',
                 'x3dNode',
                 'parsed')

    def __init__(self, parent, node_type, lineno):
        self.id = None
        self.node_type = node_type
        self.parent = parent
        self.blendObject = None
        self.blendData = None
        self.x3dNode = None
        self.parsed = None
        if parent:
            parent.children.append(self)

        self.lineno = lineno
        self.filename = None
        self.proto_node = None
        self.DEF_NAMESPACE = None
        self.ROUTE_IPO_NAMESPACE = None
        self.PROTO_NAMESPACE = None
        self.reference = None

        if node_type == NODE_REFERENCE:
            return

        self.fields = []
        self.proto_field_defs = []
        self.proto_fields = []
        self.children = []
        self.array_data = []

    def getProtoDict(self):
        if self.PROTO_NAMESPACE is not None:
            return self.PROTO_NAMESPACE
        return self.parent.getProtoDict()

    def getDefDict(self):
        if self.DEF_NAMESPACE is not None:
            return self.DEF_NAMESPACE
        return self.parent.getDefDict()

    def getRouteIpoDict(self):
        if self.ROUTE_IPO_NAMESPACE is not None:
            return self.ROUTE_IPO_NAMESPACE
        return self.parent.getRouteIpoDict()

    def setRoot(self, filename):
        self.filename = filename
        self.DEF_NAMESPACE = {}
        self.ROUTE_IPO_NAMESPACE = {}
        self.PROTO_NAMESPACE = {}

    def isRoot(self):
        return self.filename is not None

    def getFilename(self):
        if self.filename:
            return self.filename
        elif self.parent:
            return self.parent.getFilename()
        return None

    def getRealNode(self):
        if self.reference:
            return self.reference
        return self

    def getSpec(self):
        self_real = self.getRealNode()
        try:
            return self_real.id[-1]
        except:
            return None

    def findSpecRecursive(self, spec):
        self_real = self.getRealNode()
        if spec == self_real.getSpec():
            return self

        for child in self_real.children:
            if child.findSpecRecursive(spec):
                return child
        return None

    def getPrefix(self):
        if self.id:
            return self.id[0]
        return None

    def getSpecialTypeName(self, typename):
        self_real = self.getRealNode()
        try:
            return self_real.id[list(self_real.id).index(typename) + 1]
        except:
            return None

    def getDefName(self):
        return self.getSpecialTypeName('DEF')

    def getProtoName(self):
        return self.getSpecialTypeName('PROTO')

    def getExternprotoName(self):
        return self.getSpecialTypeName('EXTERNPROTO')

    def getChildrenBySpec(self, node_spec):
        self_real = self.getRealNode()
        if type(node_spec) == str:
            return [child for child in self_real.children if child.getSpec() == node_spec]
        return [child for child in self_real.children if child.getSpec() in node_spec]

    def getChildrenBySpecCondition(self, cond):
        self_real = self.getRealNode()
        return [child for child in self_real.children if cond(child.getSpec())]

    def getChildBySpec(self, node_spec):
        ls = self.getChildrenBySpec(node_spec)
        return ls[0] if ls else None

    def getChildBySpecCondition(self, cond):
        ls = self.getChildrenBySpecCondition(cond)
        return ls[0] if ls else None

    def getChildrenByName(self, node_name):
        self_real = self.getRealNode()
        return [child for child in self_real.children if child.id if child.id[0] == node_name]

    def getChildByName(self, node_name):
        self_real = self.getRealNode()
        for child in self_real.children:
            if child.id and child.id[0] == node_name:
                return child
        return None

    def getSerialized(self, results, ancestry):
        ancestry = ancestry[:]
        results.append((self, tuple(ancestry)))
        ancestry.append(self)

        if self.node_type == NODE_REFERENCE or self.reference is not None:
            return results

        for child in self.children:
            if child not in ancestry:
                if child.getProtoName() is None and child.getExternprotoName() is None:
                    child.getSerialized(results, ancestry)
        return results

    def searchNodeTypeID(self, node_spec, results):
        self_real = self.getRealNode()
        if self_real.id and self_real.id[-1] == node_spec:
            results.append(self_real)
        for child in self_real.children:
            child.searchNodeTypeID(node_spec, results)
        return results

    def getFieldName(self, field, ancestry, AS_CHILD=False, SPLIT_COMMAS=False):
        self_real = self.getRealNode()

        for f in self_real.fields:
            if f and f[0] == field:
                if len(f) >= 3 and f[1] == 'IS':
                    field_id = f[2]
                    f_proto_lookup = None
                    f_proto_child_lookup = None
                    i = len(ancestry)
                    while i:
                        i -= 1
                        node = ancestry[i]
                        node = node.getRealNode()

                        if node.proto_node:
                            if AS_CHILD:
                                for child in node.proto_node.children:
                                    if child.id and ('point' in child.id or 'points' in child.id):
                                        f_proto_child_lookup = child
                            else:
                                for f_def in node.proto_node.proto_field_defs:
                                    if len(f_def) >= 4:
                                        if f_def[0] == 'field' and f_def[2] == field_id:
                                            f_proto_lookup = f_def[3:]

                        if AS_CHILD:
                            for child in node.children:
                                if child.id and child.id[0] == field_id:
                                    f_proto_child_lookup = child
                        else:
                            for f_def in node.fields:
                                if len(f_def) >= 2:
                                    if f_def[0] == field_id:
                                        f_proto_lookup = f_def[1:]

                    if AS_CHILD:
                        if f_proto_child_lookup:
                            return f_proto_child_lookup
                    else:
                        return f_proto_lookup
                else:
                    if AS_CHILD:
                        return None
                    return f[1:]

        if AS_CHILD:
            for child in self_real.children:
                if child.id and len(child.id) == 1 and child.id[0] == field:
                    return child

        return None

    def getFieldAsInt(self, field, default, ancestry):
        self_real = self.getRealNode()
        f = self_real.getFieldName(field, ancestry)
        if f is None:
            return default
        if ',' in f:
            f = f[:f.index(',')]

        if len(f) != 1:
            logger.warning('"%s" wrong length for int conversion for field "%s"' % (f, field))
            return default

        try:
            return int(f[0])
        except:
            logger.warning('value "%s" could not be used as an int for field "%s"' % (f[0], field))
            return default

    def getFieldAsFloat(self, field, default, ancestry, scale_factor=1.0):
        self_real = self.getRealNode()
        f = self_real.getFieldName(field, ancestry)
        if f is None:
            return default
        if ',' in f:
            f = f[:f.index(',')]

        if len(f) != 1:
            logger.warning('"%s" wrong length for float conversion for field "%s"' % (f, field))
            return default

        try:
            return float(f[0]) * scale_factor
        except:
            logger.warning('value "%s" could not be used as a float for field "%s"' % (f[0], field))
            return default

    def getFieldAsFloatTuple(self, field, default, ancestry, scale_factor=1.0):
        self_real = self.getRealNode()
        f = self_real.getFieldName(field, ancestry)
        if f is None:
            return default

        if len(f) < 1:
            logger.warning('"%s" wrong length for float tuple conversion for field "%s"' % (f, field))
            return default

        ret = []
        for v in f:
            if v != ',':
                try:
                    ret.append(float(v.strip('"')) * scale_factor)
                except:
                    break

        if ret:
            if default:
                if len(ret) == len(default):
                    return ret
            else:
                return ret
        logger.warning('value "%s" could not be used as a float tuple for field "%s"' % (f, field))
        return default

    def getFieldAsBool(self, field, default, ancestry):
        self_real = self.getRealNode()
        f = self_real.getFieldName(field, ancestry)
        if f is None:
            return default
        if ',' in f:
            f = f[:f.index(',')]

        if len(f) != 1:
            logger.warning('"%s" wrong length for bool conversion for field "%s"' % (f, field))
            return default

        if f[0].upper() in {'"TRUE"', 'TRUE'}:
            return True
        elif f[0].upper() in {'"FALSE"', 'FALSE'}:
            return False
        else:
            logger.warning('"%s" could not be used as a bool for field "%s"' % (f[1], field))
            return default

    def getFieldAsString(self, field, default, ancestry):
        self_real = self.getRealNode()
        f = self_real.getFieldName(field, ancestry)
        if f is None:
            return default

        if isinstance(f, list):
            if not f:
                return default
            if len(f) == 1 and len(f[0]) > 1 and f[0][0] == '"' and f[0][-1] == '"':
                try:
                    slash_encoded = f[0][1:-1]
                    return mfstring.slash_decode(slash_encoded)
                except mfstring.SlashEncodingError:
                    logger.error("SlashEncodingError for value |%s|" % slash_encoded)
                    return default
            if len(f) == 1:
                return f[0]
            return " ".join(f)

        if isinstance(f, str):
            return f

        logger.error('getFieldAsString : value |%s| could not be used to get string for field %s' % (f, field))
        return default

    def getFieldAsArray(self, field, group, ancestry, scale_factor=1.0):
        def array_as_number(array_string):
            array_data = []
            try:
                array_data = [int(val, 0) for val in array_string]
            except:
                try:
                    array_data = [float(val) for val in array_string]
                except:
                    logger.warning('Could not parse array data from field')
            return array_data

        self_real = self.getRealNode()
        child_array = self_real.getFieldName(field, ancestry, True, SPLIT_COMMAS=True)

        if child_array is None:
            data_split = self.getFieldName(field, ancestry, SPLIT_COMMAS=True)
            if not data_split:
                return []
            array_data = array_as_number(data_split)
        elif type(child_array) == list:
            array_data = array_as_number(child_array)
        else:
            array_data = child_array.array_data

        if group == -1 or len(array_data) == 0:
            return array_data

        flat = True
        for item in array_data:
            if type(item) == list:
                flat = False
                break

        apply_scale = scale_factor != 1.0

        if flat:
            if apply_scale:
                flat_array = [n * scale_factor for n in array_data]
            else:
                flat_array = array_data
        else:
            flat_array = []

            def extend_flat(ls):
                for item in ls:
                    if type(item) == list:
                        extend_flat(item)
                    else:
                        if apply_scale:
                            item *= scale_factor
                        flat_array.append(item)

            extend_flat(array_data)

        if group == 0:
            return flat_array

        new_array = []
        sub_array = []

        for item in flat_array:
            sub_array.append(item)
            if len(sub_array) == group:
                new_array.append(sub_array)
                sub_array = []

        if sub_array:
            logger.warning('warning, array was not aligned to requested grouping %s remaining value %s' % (group, sub_array))

        return new_array

    def getFieldAsStringArray(self, field, ancestry):
        self_real = self.getRealNode()
        child_array = None
        for child in self_real.children:
            if child.id and len(child.id) == 1 and child.id[0] == field:
                child_array = child
                break
        if not child_array:
            return []

        new_array = []
        try:
            new_array = [mfstring.slash_decode(f[1:-1]) for f in child_array.fields]
        except mfstring.SlashEncodingError as exc:
            logger.warning(str(exc))
        except:
            logger.warning('String array could not be made')

        return new_array

    def getFieldAsMFStringArray(self, field, default, ancestry):
        if self.x3dNode:
            field_xml = self.x3dNode.getAttributeNode(field)
            if field_xml is None or not field_xml.value:
                return []
            try:
                return mfstring.decode(field_xml.value)
            except Exception as exc:
                logger.error("getFieldAsMFStringArray error from call to mfstring.decode %s" % str(exc))
                return []

        array = self.getFieldAsString(field, None, ancestry)
        if array is None:
            try:
                array = self.getFieldAsStringArray(field, ancestry)
            except:
                array = default
        else:
            if '" "' in array:
                array = [w.strip('"') for w in array.split('" "')]
            else:
                array = [array]

        return array

    def getLevel(self):
        level = 0
        p = self.parent
        while p:
            level += 1
            p = p.parent
        return level

    def __repr__(self):
        level = self.getLevel()
        ind = '  ' * level
        brackets = '' if self.node_type == NODE_REFERENCE else ('{}' if self.node_type == NODE_NORMAL else '[]')
        text = (ind + brackets[0] + '\n') if brackets else ''
        text += ind + 'ID: ' + str(self.id) + ' ' + str(level) + (' lineno %d\n' % self.lineno)
        if self.node_type == NODE_REFERENCE:
            text += ind + "(reference node)\n"
            return text
        if self.proto_node:
            text += ind + 'PROTO NODE...\n' + str(self.proto_node) + ind + 'PROTO NODE_DONE\n'
        text += ind + 'FIELDS:' + str(len(self.fields)) + '\n'
        for item in self.fields:
            text += ind + 'FIELD:\n' + ind + str(item) + '\n'
        text += ind + 'PROTO_FIELD_DEFS:' + str(len(self.proto_field_defs)) + '\n'
        for item in self.proto_field_defs:
            text += ind + 'PROTO_FIELD:\n' + ind + str(item) + '\n'
        text += ind + 'ARRAY: ' + str(len(self.array_data)) + ' ' + str(self.array_data) + '\n'
        text += ind + 'CHILDREN: ' + str(len(self.children)) + '\n'
        for i, child in enumerate(self.children):
            text += ind + ('CHILD%d:\n' % i) + str(child)
        text += '\n' + ind + (brackets[1] if brackets else '')
        return text

    def parse(self, i, IS_PROTO_DATA=False):
        new_i = self.__parse(i, IS_PROTO_DATA)
        url_ls = []

        if self.node_type == NODE_NORMAL and self.getSpec() == 'Inline':
            url = self.getFieldAsMFStringArray('url', None, [])
            if url:
                url_ls = [(url, None)]

        elif self.getExternprotoName():
            for f in self.fields:
                if type(f) == str:
                    f = [f]
                for ff in f:
                    for f_split in ff.split('"'):
                        if '#' in f_split:
                            f_split, f_split_id = f_split.split('#')
                            url_ls.append((f_split, f_split_id))
                        else:
                            url_ls.append((f_split, None))

        if url_ls:
            for url, extern_key in url_ls:
                urls = [
                    url,
                    bpy.path.resolve_ncase(url),
                    os.path.join(os.path.dirname(self.getFilename()), url),
                    bpy.path.resolve_ncase(os.path.join(os.path.dirname(self.getFilename()), url)),
                    os.path.join(os.path.dirname(self.getFilename()), os.path.basename(url)),
                    bpy.path.resolve_ncase(os.path.join(os.path.dirname(self.getFilename()), os.path.basename(url))),
                ]
                try:
                    url = [u for u in urls if os.path.exists(u)][0]
                    url_found = True
                except:
                    url_found = False

                if not url_found:
                    logger.warning('Inline URL could not be found: %s' % url)
                else:
                    if url == self.getFilename():
                        logger.warning('Can\'t Inline yourself recursively: %s' % url)
                    else:
                        try:
                            data = gzipOpen(url)
                        except:
                            data = None

                        if data:
                            lines_old = lines[:]
                            lines[:] = vrmlFormat(data)
                            lines.insert(0, '{')
                            lines.insert(0, 'root_node____')
                            lines.append('}')

                            child = vrmlNode(self, NODE_NORMAL, -1)
                            child.setRoot(url)
                            child.parse(0)

                            if self.getExternprotoName():
                                if not extern_key:
                                    extern_key = self.getSpec()
                                if extern_key:
                                    self.children.remove(child)
                                    child.parent = None
                                    extern_child = child.findSpecRecursive(extern_key)
                                    if extern_child:
                                        self.children.append(extern_child)
                                        extern_child.parent = self
                                    else:
                                        logger.warning("EXTERNPROTO ID not found!: %s" % extern_key)

                            lines[:] = lines_old

        return new_i

    def __parse(self, i, IS_PROTO_DATA=False):
        l = lines[i]

        if l == '[':
            self.id = None
            i += 1
        else:
            words = []
            node_type, new_i = is_nodeline(i, words)
            if not node_type:
                logger.warning("Failed to parse new node")
                raise ValueError

            if self.node_type == NODE_REFERENCE:
                key = words[words.index('USE') + 1]
                self.id = (words[0],)
                self.reference = self.getDefDict()[key]
                return new_i

            self.id = tuple(words)

            key = self.getDefName()
            if key is not None:
                self.getDefDict()[key] = self

            key = self.getProtoName() or self.getExternprotoName()
            proto_dict = self.getProtoDict()
            if key is not None:
                proto_dict[key] = self
                self.proto_node = vrmlNode(self, NODE_ARRAY, new_i)
                new_i = self.proto_node.parse(new_i)
                self.children.remove(self.proto_node)
                new_i += 1
            else:
                spec = self.getSpec()
                try:
                    self.children.append(proto_dict[spec])
                except:
                    pass

            i = new_i

        ok = True
        while ok:
            if i >= len(lines):
                return len(lines) - 1

            l = lines[i]
            if l == '':
                i += 1
                continue

            if l == '}':
                if self.node_type != NODE_NORMAL:
                    logger.warning('wrong node ending, expected an } ' + str(i) + ' ' + str(self.node_type))
                return i + 1
            if l == ']':
                if self.node_type != NODE_ARRAY:
                    logger.warning('wrong node ending, expected a ] ' + str(i) + ' ' + str(self.node_type))
                    if DEBUG:
                        raise ValueError
                return i + 1

            node_type, new_i = is_nodeline(i, [])
            if node_type:
                child = vrmlNode(self, node_type, i)
                i = child.parse(i)
            elif l == '[':
                child = vrmlNode(self, NODE_ARRAY, i)
                i = child.parse(i)
            elif is_numline(i):
                l_split = l.replace(',', ' ').split()
                values = None
                if l_split:
                    for num_type in (int, float):
                        try:
                            values = [num_type(v) for v in l_split]
                            break
                        except:
                            pass
                    else:
                        logger.warning("unable to parse a numline: %s" % (l,))
                    if values:
                        self.array_data.extend(values)
                i += 1
            else:
                words = vrml_split(l)
                if len(words) > 2 and words[1] == 'USE':
                    vrmlNode(self, NODE_REFERENCE, i)
                else:
                    while 1:
                        stripped_line = l.strip()
                        if stripped_line and stripped_line[0] == '"':
                            for str_item in vrml_split(stripped_line):
                                if str_item[0] == '"' and str_item[-1] == '"':
                                    self.fields.append(str_item)
                                else:
                                    logger.warning("unrecognized |%s| in mfstring list" % str_item)
                                    break
                            else:
                                break

                        value = l
                        quote_count = vrml_count_quote(l)
                        if (quote_count % 2) == 1:
                            accumulated_lines = l
                            LOOP_GUARD = 4
                            while 1:
                                LOOP_GUARD -= 1
                                if LOOP_GUARD < 0:
                                    raise Exception("__parse: infinite loop in handling multiline VRML string")
                                i += 1
                                accumulated_lines = accumulated_lines + "\n" + lines[i]
                                quote_count = vrml_count_quote(accumulated_lines)
                                if (quote_count % 2) == 0:
                                    value = accumulated_lines
                                    break

                        value_all = vrml_split(value)
                        for val in vrml_split_fields(value_all):
                            if val[0] == 'field':
                                self.proto_field_defs.append(val)
                            else:
                                self.fields.append(val)
                        break
                i += 1

    def canHaveReferences(self):
        return self.node_type == NODE_NORMAL and self.getDefName()

    def desc(self):
        if "material" in self.id or "texture" in self.id:
            node = self.reference if self.node_type == NODE_REFERENCE else self
            return frozenset(line.strip() for line in repr(node).strip().split("\n"))
        return None


def gzipOpen(path):
    import gzip
    data = None
    file_ext = os.path.splitext(path)[1].lower()

    try:
        if file_ext in ['.x3dz']:
            with gzip.open(path, 'rb') as file:
                data = file.read()
            data = data.decode(encoding='utf-8', errors='surrogateescape')
        else:
            with open(path, 'r', encoding='utf-8', errors='surrogateescape') as file:
                data = file.read()
    except Exception:
        import traceback
        traceback.print_exc()

    return data


def vrml_parse(path):
    data = gzipOpen(path)
    if data is None:
        return None, 'Failed to open file: ' + path

    lines[:] = vrmlFormat(data)
    lines.insert(0, '{')
    lines.insert(0, 'dymmy_node')
    lines.append('}')

    node_type, new_i = is_nodeline(0, [])
    if not node_type:
        return None, 'Error: VRML file has no starting Node'

    lines.insert(0, '{')
    lines.insert(0, 'root_node____')
    lines.append('}')

    root = vrmlNode(None, NODE_NORMAL, -1)
    root.setRoot(path)
    root.parse(0)

    return root, ''


class x3dNode(vrmlNode):
    def __init__(self, parent, node_type, x3dNode):
        vrmlNode.__init__(self, parent, node_type, -1)
        self.x3dNode = x3dNode

    def parse(self, IS_PROTO_DATA=False):
        self.lineno = getattr(self.x3dNode, 'parse_position', (-1, -1))[0]

        define = self.x3dNode.getAttributeNode('DEF')
        if define:
            self.getDefDict()[define.value] = self
        else:
            use = self.x3dNode.getAttributeNode('USE')
            if use:
                try:
                    self.reference = self.getDefDict()[use.value]
                    self.node_type = NODE_REFERENCE
                except:
                    logger.warning('Reference %s not found' % use.value)
                    self.parent.children.remove(self)
                return

        for x3dChildNode in list(self.x3dNode.childNodes):
            if x3dChildNode.nodeType in {x3dChildNode.TEXT_NODE, x3dChildNode.COMMENT_NODE, x3dChildNode.CDATA_SECTION_NODE}:
                continue

            # Capture XML <ROUTE ... /> statements directly into fields
            if x3dChildNode.nodeType == x3dChildNode.ELEMENT_NODE and x3dChildNode.tagName.upper() == 'ROUTE':
                fn = (x3dChildNode.getAttribute('fromNode') or x3dChildNode.getAttribute('fromnode') or '').strip()
                ff = (x3dChildNode.getAttribute('fromField') or x3dChildNode.getAttribute('fromfield') or '').strip()
                tn = (x3dChildNode.getAttribute('toNode') or x3dChildNode.getAttribute('tonode') or '').strip()
                tf = (x3dChildNode.getAttribute('toField') or x3dChildNode.getAttribute('tofield') or '').strip()
                if fn and tn:
                    self.fields.append(['ROUTE', f"{fn}.{ff}", 'TO', f"{tn}.{tf}"])
                continue

            # Handle X3D ProtoDeclare
            if x3dChildNode.nodeType == x3dChildNode.ELEMENT_NODE and x3dChildNode.tagName == 'ProtoDeclare':
                if proto_x3d is not None and getattr(proto_x3d, 'manager', None) is not None:
                    proto_x3d.manager.register_proto_declare(x3dChildNode)
                elif proto_x3d is not None and hasattr(proto_x3d, 'register_proto_declare'):
                    proto_x3d.register_proto_declare(x3dChildNode)
                continue

            # Handle X3D ProtoInstance
            if x3dChildNode.nodeType == x3dChildNode.ELEMENT_NODE and x3dChildNode.tagName == 'ProtoInstance':
                if proto_x3d is not None and getattr(proto_x3d, 'manager', None) is not None:
                    proto_x3d.manager.expand_proto_instance(self, x3dChildNode, x3dNode, NODE_NORMAL)
                elif proto_x3d is not None and hasattr(proto_x3d, 'expand_proto_instance'):
                    proto_x3d.expand_proto_instance(self, x3dChildNode, x3dNode, NODE_NORMAL)
                continue

            node_type = NODE_NORMAL
            if x3dChildNode.getAttributeNode('USE'):
                node_type = NODE_REFERENCE

            child = x3dNode(self, node_type, x3dChildNode)
            child.parse()

    def getSpec(self):
        return self.x3dNode.tagName

    def getDefName(self):
        node_id = self.x3dNode.getAttributeNode('DEF')
        if node_id:
            return node_id.value
        node_id = self.x3dNode.getAttributeNode('USE')
        if node_id:
            return "USE_" + node_id.value
        return None

    def getFieldName(self, field, ancestry, AS_CHILD=False, SPLIT_COMMAS=False):
        field_xml = self.x3dNode.getAttributeNode(field)
        if field_xml:
            value = field_xml.value
            if SPLIT_COMMAS:
                value = value.replace(",", " ")
            if '"' in value:
                logger.warning("applying str.split to an X3D XML attribute '%s'; that contains SFString |%s|" % (field, value))
            return value.split()
        return None

    def canHaveReferences(self):
        return self.x3dNode.getAttributeNode('DEF')

    def desc(self):
        return self.getRealNode().x3dNode.toxml()


def x3d_parse(path):
    import xml.dom.minidom
    import xml.sax
    from xml.sax import handler

    data = gzipOpen(path)
    if data is None:
        return None, 'Failed to open file: ' + path

    def set_content_handler(dom_handler):
        def startElementNS(name, tagName, attrs):
            orig_start_cb(name, tagName, attrs)
            cur_elem = dom_handler.elementStack[-1]
            cur_elem.parse_position = (parser._parser.CurrentLineNumber, parser._parser.CurrentColumnNumber)

        orig_start_cb = dom_handler.startElementNS
        dom_handler.startElementNS = startElementNS
        orig_set_content_handler(dom_handler)

    parser = xml.sax.make_parser()
    orig_set_content_handler = parser.setContentHandler
    parser.setFeature(handler.feature_external_ges, False)
    parser.setFeature(handler.feature_external_pes, False)
    parser.setContentHandler = set_content_handler

    doc = xml.dom.minidom.parseString(data, parser)

    try:
        x3dnode = doc.getElementsByTagName('X3D')[0]
    except:
        return None, 'Not a valid x3d document, cannot import'

    bpy.ops.object.select_all(action='DESELECT')

    root = x3dNode(None, NODE_NORMAL, x3dnode)
    root.setRoot(path)
    root.parse()

    return root, ''


# -----------------------------------------------------------------------------------
import bpy
from bpy_extras import image_utils, node_shader_utils
from mathutils import Vector, Matrix, Quaternion

GLOBALS = {'CIRCLE_DETAIL': 16}


def translateRotation(rot):
    return Matrix.Rotation(rot[3], 4, Vector(rot[:3]))


def translateScale(sca):
    mat = Matrix()
    mat[0][0] = sca[0]
    mat[1][1] = sca[1]
    mat[2][2] = sca[2]
    return mat


def translateTransform(node, ancestry):
    cent = node.getFieldAsFloatTuple('center', None, ancestry, conversion_scale)
    rot = node.getFieldAsFloatTuple('rotation', None, ancestry)
    sca = node.getFieldAsFloatTuple('scale', None, ancestry)
    scaori = node.getFieldAsFloatTuple('scaleOrientation', None, ancestry)
    tx = node.getFieldAsFloatTuple('translation', None, ancestry, conversion_scale)

    cent_mat = Matrix.Translation(cent) if cent else None
    cent_imat = cent_mat.inverted() if cent_mat else None
    rot_mat = translateRotation(rot) if rot else None
    sca_mat = translateScale(sca) if sca else None
    scaori_mat = translateRotation(scaori) if scaori else None
    scaori_imat = scaori_mat.inverted() if scaori_mat else None
    tx_mat = Matrix.Translation(tx) if tx else None

    new_mat = Matrix()
    mats = [tx_mat, cent_mat, rot_mat, scaori_mat, sca_mat, scaori_imat, cent_imat]
    for mtx in mats:
        if mtx:
            new_mat = new_mat @ mtx
    return new_mat


def translateTexTransform(node, ancestry):
    cent = node.getFieldAsFloatTuple('center', None, ancestry, conversion_scale)
    rot = node.getFieldAsFloat('rotation', None, ancestry)
    sca = node.getFieldAsFloatTuple('scale', None, ancestry)
    tx = node.getFieldAsFloatTuple('translation', None, ancestry, conversion_scale)

    cent_mat = Matrix.Translation(Vector(cent).to_3d()) if cent else None
    cent_imat = cent_mat.inverted() if cent_mat else None
    rot_mat = Matrix.Rotation(rot * (-1), 4, 'Z') if rot else None
    sca_mat = translateScale((sca[0], sca[1], 0.0)) if sca else None
    tx_mat = Matrix.Translation(Vector(tx).to_3d()) if tx else None

    new_mat = Matrix()
    mats = [cent_imat, sca_mat, rot_mat, cent_mat, tx_mat]
    for mtx in mats:
        if mtx:
            new_mat = new_mat @ mtx
    return new_mat


def getFinalMatrix(node, mtx, ancestry, global_matrix):
    transform_nodes = [node_tx for node_tx in ancestry if node_tx.getSpec() == 'Transform']
    if node.getSpec() == 'Transform':
        transform_nodes.append(node)
    transform_nodes.reverse()

    if mtx is None:
        mtx = Matrix()

    for node_tx in transform_nodes:
        mat = translateTransform(node_tx, ancestry)
        mtx = mat @ mtx

    return global_matrix @ mtx


def linear_to_srgb(linear):
    if linear <= 0.0031308:
        return linear * 12.92
    return 1.055 * (linear ** (1.0 / 2.4)) - 0.055


def srgb_to_linear(srgb_value):
    if srgb_value <= 0.04045:
        return srgb_value / 12.92
    return ((srgb_value + 0.055) / 1.055) ** 2.4


def set_new_float_color_attribute(bpymesh, color_data, name: str = "ColorPerCorner", convert_to_linear: bool = True):
    if convert_to_linear:
        color_data = [srgb_to_linear(col_val) for col_val in color_data]
    bpymesh.color_attributes.new(name, 'FLOAT_COLOR', 'CORNER')
    bpymesh.color_attributes[name].data.foreach_set("color", color_data)


def importMesh_ApplyColors(bpymesh, geom, ancestry):
    colors = geom.getChildBySpec(['ColorRGBA', 'Color'])
    if colors:
        if colors.getSpec() == 'ColorRGBA':
            rgb = colors.getFieldAsArray('color', 4, ancestry)
        else:
            rgb = [c + [1.0] for c in colors.getFieldAsArray('color', 3, ancestry)]

        rgb_len = len(rgb)
        vertices_len = len(bpymesh.vertices)
        loops_len = len(bpymesh.loops)

        if rgb_len >= vertices_len and rgb_len != loops_len:
            if rgb_len > vertices_len:
                rgb = rgb[:vertices_len]
            rgb = [rgb[l.vertex_index] for l in bpymesh.loops]
            rgb = tuple(chain(*rgb))
        elif rgb_len >= loops_len:
            if rgb_len > loops_len:
                rgb = rgb[:loops_len]
            rgb = tuple(chain(*rgb))
        else:
            logger.warning(
                "Not applying vertex colors, non matching numbers of vertices or loops (%d vs %d/%d)" %
                (rgb_len, vertices_len, loops_len)
            )
            return

        set_new_float_color_attribute(bpymesh, rgb)


def importMesh_ApplyNormals(bpymesh, geom, ancestry):
    normals = geom.getChildBySpec('Normal')
    if not normals:
        return

    per_vertex = geom.getFieldAsBool('normalPerVertex', True, ancestry)
    vectors = normals.getFieldAsArray('vector', 0, ancestry)
    if per_vertex:
        bpymesh.vertices.foreach_set("normal", vectors)
    else:
        bpymesh.polygons.foreach_set("normal", vectors)


def importMesh_ReadVertices(bpymesh, geom, ancestry):
    coord = geom.getChildBySpec('Coordinate')
    points = coord.getFieldAsArray('point', 0, ancestry, conversion_scale)
    bpymesh.vertices.add(len(points) // 3)
    bpymesh.vertices.foreach_set("co", points)


def importMesh_ApplyUVs(bpymesh, geom, ancestry):
    tex_coord = geom.getChildBySpec('TextureCoordinate')
    if not tex_coord:
        return

    uvs = tex_coord.getFieldAsArray('point', 2, ancestry)
    if not uvs:
        return

    d = bpymesh.uv_layers.new().data
    uvs = [i for poly in bpymesh.polygons
           for vidx in poly.vertices
           for i in uvs[vidx]]
    d.foreach_set('uv', uvs)


def importMesh_FinalizeTriangleMesh(bpymesh, geom, ancestry):
    importMesh_ApplyNormals(bpymesh, geom, ancestry)
    importMesh_ApplyColors(bpymesh, geom, ancestry)
    importMesh_ApplyUVs(bpymesh, geom, ancestry)
    bpymesh.validate()
    bpymesh.update()
    return bpymesh


def importMesh_ApplyTextureToLoops(bpymesh, loops):
    d = bpymesh.uv_layers.new().data
    d.foreach_set('uv', loops)


def flip(r, ccw):
    return r if ccw else r[::-1]


def validate_points_field(coord_index, points):
    for f in coord_index:
        missing_point = False
        for v in f:
            try:
                points[v]
            except IndexError:
                missing_point = True
                points.extend([(0, 0, 0)] * (v - len(points) + 1))
        if missing_point:
            logger.warning("More coordIndex than points found")
    return points


def importMesh_IndexedTriangleSet(geom, ancestry):
    ccw = geom.getFieldAsBool('ccw', True, ancestry)
    bpymesh = bpy.data.meshes.new(name="XXX")
    importMesh_ReadVertices(bpymesh, geom, ancestry)

    index = geom.getFieldAsArray('index', 0, ancestry)
    num_polys = len(index) // 3
    if not ccw:
        index = [index[3 * i + j] for i in range(num_polys) for j in (1, 0, 2)]

    bpymesh.loops.add(num_polys * 3)
    bpymesh.polygons.add(num_polys)
    bpymesh.polygons.foreach_set("loop_start", range(0, num_polys * 3, 3))
    bpymesh.polygons.foreach_set("vertices", index)

    return importMesh_FinalizeTriangleMesh(bpymesh, geom, ancestry)


def importMesh_IndexedTriangleStripSet(geom, ancestry):
    cw = 0 if geom.getFieldAsBool('ccw', True, ancestry) else 1
    bpymesh = bpy.data.meshes.new(name="IndexedTriangleStripSet")
    importMesh_ReadVertices(bpymesh, geom, ancestry)

    index = geom.getFieldAsArray('index', 0, ancestry)
    while index and index[-1] == -1:
        del index[-1]
    ngaps = sum(1 for i in index if i == -1)
    num_polys = len(index) - 2 - 3 * ngaps
    bpymesh.loops.add(num_polys * 3)
    bpymesh.polygons.add(num_polys)
    bpymesh.polygons.foreach_set("loop_start", range(0, num_polys * 3, 3))

    def triangles():
        i = 0
        odd = cw
        while True:
            yield index[i + odd]
            yield index[i + 1 - odd]
            yield index[i + 2]
            odd = 1 - odd
            i += 1
            if i + 2 >= len(index):
                return
            if index[i + 2] == -1:
                i += 3
                odd = cw
    bpymesh.polygons.foreach_set("vertices", [f for f in triangles()])
    return importMesh_FinalizeTriangleMesh(bpymesh, geom, ancestry)


def importMesh_IndexedTriangleFanSet(geom, ancestry):
    cw = 0 if geom.getFieldAsBool('ccw', True, ancestry) else 1
    bpymesh = bpy.data.meshes.new(name="IndexedTriangleFanSet")
    importMesh_ReadVertices(bpymesh, geom, ancestry)

    index = geom.getFieldAsArray('index', 0, ancestry)
    while index and index[-1] == -1:
        del index[-1]

    ngaps = sum(1 for i in index if i == -1)
    num_polys = len(index) - 2 - 3 * ngaps
    bpymesh.loops.add(num_polys * 3)
    bpymesh.polygons.add(num_polys)
    bpymesh.polygons.foreach_set("loop_start", range(0, num_polys * 3, 3))

    def triangles():
        i = 0
        j = 1
        while True:
            yield index[i]
            yield index[i + j + cw]
            yield index[i + j + 1 - cw]
            j += 1
            if i + j + 1 >= len(index):
                return
            if index[i + j + 1] == -1:
                i = j + 2
                j = 1
    bpymesh.polygons.foreach_set("vertices", [f for f in triangles()])
    return importMesh_FinalizeTriangleMesh(bpymesh, geom, ancestry)


def importMesh_TriangleSet(geom, ancestry):
    ccw = geom.getFieldAsBool('ccw', True, ancestry)
    bpymesh = bpy.data.meshes.new(name="TriangleSet")
    importMesh_ReadVertices(bpymesh, geom, ancestry)
    n = len(bpymesh.vertices)
    num_polys = n // 3
    bpymesh.loops.add(num_polys * 3)
    bpymesh.polygons.add(num_polys)
    bpymesh.polygons.foreach_set("loop_start", range(0, num_polys * 3, 3))

    if ccw:
        fv = [i for i in range(n)]
    else:
        fv = [3 * i + j for i in range(n // 3) for j in (1, 0, 2)]
    bpymesh.polygons.foreach_set("vertices", fv)

    return importMesh_FinalizeTriangleMesh(bpymesh, geom, ancestry)


def importMesh_TriangleStripSet(geom, ancestry):
    cw = 0 if geom.getFieldAsBool('ccw', True, ancestry) else 1
    bpymesh = bpy.data.meshes.new(name="TriangleStripSet")
    importMesh_ReadVertices(bpymesh, geom, ancestry)
    counts = geom.getFieldAsArray('stripCount', 0, ancestry)
    num_polys = sum([n - 2 for n in counts])
    bpymesh.loops.add(num_polys * 3)
    bpymesh.polygons.add(num_polys)
    bpymesh.polygons.foreach_set("loop_start", range(0, num_polys * 3, 3))

    def triangles():
        b = 0
        for i in range(0, len(counts)):
            for j in range(0, counts[i] - 2):
                yield b + j + (j + cw) % 2
                yield b + j + 1 - (j + cw) % 2
                yield b + j + 2
            b += counts[i]
    bpymesh.polygons.foreach_set("vertices", [x for x in triangles()])
    return importMesh_FinalizeTriangleMesh(bpymesh, geom, ancestry)


def importMesh_TriangleFanSet(geom, ancestry):
    cw = 0 if geom.getFieldAsBool('ccw', True, ancestry) else 1
    bpymesh = bpy.data.meshes.new(name="TriangleStripSet")
    importMesh_ReadVertices(bpymesh, geom, ancestry)
    counts = geom.getFieldAsArray('fanCount', 0, ancestry)
    num_polys = sum([n - 2 for n in counts])
    bpymesh.loops.add(num_polys * 3)
    bpymesh.polygons.add(num_polys)
    bpymesh.polygons.foreach_set("loop_start", range(0, num_polys * 3, 3))

    def triangles():
        b = 0
        for i in range(0, len(counts)):
            for j in range(1, counts[i] - 1):
                yield b
                yield b + j + cw
                yield b + j + 1 - cw
            b += counts[i]
    bpymesh.polygons.foreach_set("vertices", [x for x in triangles()])
    return importMesh_FinalizeTriangleMesh(bpymesh, geom, ancestry)


def importMesh_IndexedFaceSet(geom, ancestry):
    ccw = geom.getFieldAsBool('ccw', True, ancestry)
    coord = geom.getChildBySpec('Coordinate')
    if coord is None:
        return None

    if coord.reference and coord.getRealNode().parsed:
        points = coord.getRealNode().parsed
    else:
        points = coord.getFieldAsArray('point', 3, ancestry, conversion_scale)
        if coord.canHaveReferences():
            coord.parsed = points

    index = geom.getFieldAsArray('coordIndex', 0, ancestry)
    while index and index[-1] == -1:
        del index[-1]

    if len(points) >= 2 * len(index):
        culled_points = []
        cull = {}
        uncull = []
        new_index = 0
    else:
        uncull = cull = None

    faces = []
    face = []
    for i in index:
        if i == -1:
            if face:
                faces.append(flip(face, ccw))
            face = []
        else:
            if cull is not None:
                if not (i in cull):
                    culled_points.append(points[i])
                    cull[i] = new_index
                    uncull.append(i)
                    i = new_index
                    new_index += 1
                else:
                    i = cull[i]
            face.append(i)
    if face:
        faces.append(flip(face, ccw))

    if cull:
        points = culled_points

    points = validate_points_field(faces, points)

    bpymesh = bpy.data.meshes.new(name="IndexedFaceSet")
    bpymesh.from_pydata(points, [], faces)

    def processPerVertexIndex(ind):
        if ind:
            i = 0
            verts_by_face = []
            for f in faces:
                verts_by_face.append(flip(ind[i:i + len(f)], ccw))
                i += len(f) + 1
            return verts_by_face
        elif uncull:
            return [[uncull[v] for v in f] for f in faces]
        else:
            return faces

    normals = geom.getChildBySpec('Normal')
    if normals:
        per_vertex = geom.getFieldAsBool('normalPerVertex', True, ancestry)
        vectors = normals.getFieldAsArray('vector', 3, ancestry)
        normal_index = geom.getFieldAsArray('normalIndex', 0, ancestry)
        if per_vertex:
            if len(normal_index) == 0:
                normal_index = index
            co = [co for f in processPerVertexIndex(normal_index)
                  for v in f
                  for co in mathutils.Vector(vectors[v]).normalized().to_tuple()]
            bpymesh.vertices.foreach_set("normal", co)
            bpymesh.attributes.new("temp_custom_normals", 'FLOAT_VECTOR', 'CORNER')
            bpymesh.attributes["temp_custom_normals"].data.foreach_set("vector", co)
        else:
            co = [co for (i, f) in enumerate(faces)
                  for j in f
                  for co in mathutils.Vector(vectors[normal_index[i] if normal_index else i]).normalized().to_tuple()]
            bpymesh.polygons.foreach_set("normal", co)

    colors = geom.getChildBySpec(['ColorRGBA', 'Color'])
    if colors:
        if colors.getSpec() == 'ColorRGBA':
            rgb = colors.getFieldAsArray('color', 4, ancestry)
        else:
            rgb = [c + [1.0] for c in colors.getFieldAsArray('color', 3, ancestry)]

        color_per_vertex = geom.getFieldAsBool('colorPerVertex', True, ancestry)
        color_index = geom.getFieldAsArray('colorIndex', 0, ancestry)
        has_color_index = len(color_index) != 0
        has_valid_color_index = index.count(-1) == color_index.count(-1)

        if color_per_vertex and has_color_index and not has_valid_color_index:
            color_index = [x for x in color_index if x != -1]
            for i, v in enumerate(index):
                if v == -1:
                    color_index.insert(i, -1)

        if color_per_vertex and has_color_index:
            cco = [cco for f in processPerVertexIndex(color_index)
                   for v in f
                   for cco in rgb[v]]
        elif color_per_vertex:
            try:
                cco = [cco for f in faces
                       for v in f
                       for cco in rgb[v]]
            except IndexError:
                cco = [cco for f in faces
                       for (i, v) in enumerate(f)
                       for cco in rgb[i]]
        elif color_index:
            cco = [cco for (i, f) in enumerate(faces)
                   for j in f
                   for cco in rgb[color_index[i]]]
        elif len(faces) > len(rgb):
            cco = [cco for (i, f) in enumerate(faces)
                   for j in f
                   for cco in rgb[0]]
        else:
            cco = [cco for (i, f) in enumerate(faces)
                   for j in f
                   for cco in rgb[i]]

        if color_per_vertex:
            set_new_float_color_attribute(bpymesh, cco, name="temp_custom_colors")
        else:
            set_new_float_color_attribute(bpymesh, cco)

    tex_coord = geom.getChildBySpec('TextureCoordinate')
    if tex_coord:
        tex_coord_points = tex_coord.getFieldAsArray('point', 2, ancestry)
        tex_index = geom.getFieldAsArray('texCoordIndex', 0, ancestry)
        tex_index = processPerVertexIndex(tex_index)
        loops = [co for f in tex_index
                 for v in f
                 for co in tex_coord_points[v]]
    else:
        x_min = y_min = z_min = math.inf
        x_max = y_max = z_max = -math.inf
        for f in faces:
            for v in f:
                (x, y, z) = points[v]
                x_min = min(x_min, x)
                x_max = max(x_max, x)
                y_min = min(y_min, y)
                y_max = max(y_max, y)
                z_min = min(z_min, z)
                z_max = max(z_max, z)

        mins = (x_min, y_min, z_min)
        deltas = (x_max - x_min, y_max - y_min, z_max - z_min)
        axes = [0, 1, 2]
        axes.sort(key=lambda a: (-deltas[a], a))
        (s_axis, t_axis) = axes[0:2]
        s_min = mins[s_axis]
        ds = deltas[s_axis] or 1.0
        t_min = mins[t_axis]
        dt = deltas[t_axis] or 1.0

        def generatePointCoords(pt):
            return (pt[s_axis] - s_min) / ds, (pt[t_axis] - t_min) / dt

        loops = [co for f in faces
                 for v in f
                 for co in generatePointCoords(points[v])]

    importMesh_ApplyTextureToLoops(bpymesh, loops)
    bpymesh.validate(clean_customdata=False)

    if normals and per_vertex:
        co2 = [0.0 for _ in range(int(len(bpymesh.attributes["temp_custom_normals"].data) * 3))]
        bpymesh.attributes["temp_custom_normals"].data.foreach_get("vector", co2)
        bpymesh.normals_split_custom_set(tuple(zip(*(iter(co2),) * 3)))
        bpymesh.attributes.remove(bpymesh.attributes["temp_custom_normals"])

    if colors and color_per_vertex:
        cco2 = [0.0 for _ in range(int(len(bpymesh.attributes["temp_custom_colors"].data) * 4))]
        bpymesh.attributes["temp_custom_colors"].data.foreach_get("color", cco2)
        set_new_float_color_attribute(bpymesh, cco2)
        bpymesh.attributes.remove(bpymesh.attributes["temp_custom_colors"])

    bpymesh.update()
    return bpymesh


def importMesh_Rectangle2D(geom, ancestry):
    size = geom.getFieldAsFloatTuple('size', (2.0 * conversion_scale, 2.0 * conversion_scale), ancestry, conversion_scale)
    dx = size[0] / 2.0
    dy = size[1] / 2.0
    bpymesh = bpy.data.meshes.new(name="Rectangle2D")
    verts = [(-dx, -dy, 0.0), (dx, -dy, 0.0), (dx, dy, 0.0), (-dx, dy, 0.0)]
    faces = [(0, 1, 2, 3)]
    bpymesh.from_pydata(verts, [], faces)
    bpymesh.validate()
    d = bpymesh.uv_layers.new().data
    d.foreach_set('uv', (0.0, 0.0, 1.0, 0.0, 1.0, 1.0, 0.0, 1.0))
    bpymesh.update()
    return bpymesh


def importMesh_ElevationGrid(geom, ancestry):
    height = geom.getFieldAsArray('height', 0, ancestry)
    x_dim = geom.getFieldAsInt('xDimension', 0, ancestry)
    x_spacing = geom.getFieldAsFloat('xSpacing', 1, ancestry)
    z_dim = geom.getFieldAsInt('zDimension', 0, ancestry)
    z_spacing = geom.getFieldAsFloat('zSpacing', 1, ancestry)
    ccw = geom.getFieldAsBool('ccw', True, ancestry)

    bpymesh = bpy.data.meshes.new(name="ElevationGrid")
    bpymesh.vertices.add(x_dim * z_dim)
    co = [w for x in range(x_dim) for z in range(z_dim)
          for w in (x * x_spacing, height[x_dim * z + x], z * z_spacing)]
    bpymesh.vertices.foreach_set("co", co)

    num_polys = (x_dim - 1) * (z_dim - 1)
    bpymesh.loops.add(num_polys * 4)
    bpymesh.polygons.add(num_polys)
    bpymesh.polygons.foreach_set("loop_start", range(0, num_polys * 4, 4))
    verts = [i for x in range(x_dim - 1) for z in range(z_dim - 1)
             for i in (z * x_dim + x,
                       z * x_dim + x + 1 if ccw else (z + 1) * x_dim + x,
                       (z + 1) * x_dim + x + 1,
                       (z + 1) * x_dim + x if ccw else z * x_dim + x + 1)]
    bpymesh.polygons.foreach_set("vertices", verts)

    importMesh_ApplyNormals(bpymesh, geom, ancestry)
    colors = geom.getChildBySpec(['ColorRGBA', 'Color'])
    if colors:
        if colors.getSpec() == 'ColorRGBA':
            rgb = [c[:3] for c in colors.getFieldAsArray('color', 4, ancestry)]
        else:
            rgb = colors.getFieldAsArray('color', 3, ancestry)

        if geom.getFieldAsBool('colorPerVertex', True, ancestry):
            set_new_float_color_attribute(bpymesh,
                                          [c for x in range(x_dim - 1)
                                           for z in range(z_dim - 1)
                                           for rgb_idx in (z * x_dim + x,
                                                           z * x_dim + x + 1 if ccw else (z + 1) * x_dim + x,
                                                           (z + 1) * x_dim + x + 1,
                                                           (z + 1) * x_dim + x if ccw else z * x_dim + x + 1)
                                           for c in rgb[rgb_idx]])
        else:
            set_new_float_color_attribute(bpymesh,
                                          [c for x in range(x_dim - 1)
                                           for z in range(z_dim - 1)
                                           for rgb_idx in (z * (x_dim - 1) + x,) * 4
                                           for c in rgb[rgb_idx]])

    tex_coord = geom.getChildBySpec('TextureCoordinate')
    if tex_coord:
        uvs = tex_coord.getFieldAsArray('point', 2, ancestry)
    else:
        uvs = [(i / (x_dim - 1), j / (z_dim - 1))
               for i in range(x_dim)
               for j in range(z_dim)]

    d = bpymesh.uv_layers.new().data
    uvs = [i for poly in bpymesh.polygons
           for vidx in poly.vertices
           for i in uvs[vidx]]
    d.foreach_set('uv', uvs)

    bpymesh.validate()
    bpymesh.update()
    return bpymesh


def importMesh_Extrusion(geom, ancestry):
    ccw = geom.getFieldAsBool('ccw', True, ancestry)
    begin_cap = geom.getFieldAsBool('beginCap', True, ancestry)
    end_cap = geom.getFieldAsBool('endCap', True, ancestry)
    cross = geom.getFieldAsArray('crossSection', 2, ancestry) or ((1, 1), (1, -1), (-1, -1), (-1, 1), (1, 1))
    spine = geom.getFieldAsArray('spine', 3, ancestry) or ((0, 0, 0), (0, 1, 0))
    orient = geom.getFieldAsArray('orientation', 4, ancestry)
    if orient:
        orient = [Quaternion(o[:3], o[3]).to_matrix() if o[3] else None for o in orient]
    scale = geom.getFieldAsArray('scale', 2, ancestry)
    if scale:
        scale = [Matrix(((s[0], 0, 0), (0, 1, 0), (0, 0, s[1])))
                 if s[0] != 1 or s[1] != 1 else None for s in scale]

    cross_closed = cross[0] == cross[-1]
    if cross_closed:
        cross = cross[:-1]
    nc = len(cross)
    cross = [Vector((c[0], 0, c[1])) for c in cross]
    ncf = nc if cross_closed else nc - 1

    spine_closed = spine[0] == spine[-1]
    if spine_closed:
        spine = spine[:-1]
    ns = len(spine)
    spine = [Vector(s) for s in spine]
    nsf = ns if spine_closed else ns - 1

    if scale:
        while len(scale) < len(spine):
            scale.append(scale[-1])

    def findFirstAngleNormal():
        for i in range(1, ns - 1):
            spt = spine[i]
            z = (spine[i + 1] - spt).cross(spine[i - 1] - spt)
            if z.length > EPSILON:
                return z
        v = spine[1] - spine[0]
        orig_y = Vector((0, 1, 0))
        orig_z = Vector((0, 0, 1))
        if v.cross(orig_y).length >= EPSILON:
            orig_z.rotate(orig_y.rotation_difference(v))
        return orig_z

    verts = []
    z = None
    for i, spt in enumerate(spine):
        if (i > 0 and i < ns - 1) or spine_closed:
            snext = spine[(i + 1) % ns]
            sprev = spine[(i - 1 + ns) % ns]
            y = snext - sprev
            vnext = snext - spt
            vprev = sprev - spt
            try_z = vnext.cross(vprev)
            if try_z.length > EPSILON:
                if z is not None and try_z.dot(z) < 0:
                    try_z.negate()
                z = try_z
            elif not z:
                z = findFirstAngleNormal()
        elif i == 0:
            snext = spine[i + 1]
            y = snext - spt
            z = findFirstAngleNormal()
        else:
            sprev = spine[i - 1]
            y = spt - sprev

        x = y.cross(z)
        m = Matrix(((x.x, y.x, z.x), (x.y, y.y, z.y), (x.z, y.z, z.z)))
        m.normalize()
        if orient:
            mrot = orient[i] if len(orient) > 1 else orient[0]
            if mrot:
                m @= mrot
        if scale:
            mscale = scale[i] if len(scale) > 1 else scale[0]
            if mscale:
                m @= mscale
        for cpt in cross:
            verts.append((spt + m @ cpt).to_tuple())

    faces = []
    if begin_cap:
        faces.append(flip([x for x in range(nc - 1, -1, -1)], ccw))

    faces += [flip((
        s * nc + c,
        s * nc + (c + 1) % nc,
        (s + 1) * nc + (c + 1) % nc,
        (s + 1) * nc + c), ccw) for s in range(ns - 1) for c in range(ncf)]

    if spine_closed:
        b = (ns - 1) * nc
        faces += [flip((
            b + c,
            b + (c + 1) % nc,
            (c + 1) % nc,
            c), ccw) for c in range(ncf)]

    if end_cap:
        faces.append(flip([(ns - 1) * nc + x for x in range(0, nc)], ccw))

    bpymesh = bpy.data.meshes.new(name="Extrusion")
    bpymesh.from_pydata(verts, [], faces)

    if begin_cap or end_cap:
        x_min = x_max = z_min = z_max = None
        for c in cross:
            (x, z) = (c.x, c.z)
            if x_min is None or x < x_min:
                x_min = x
            if x_max is None or x > x_max:
                x_max = x
            if z_min is None or z < z_min:
                z_min = z
            if z_max is None or z > z_max:
                z_max = z
        dx = x_max - x_min
        dz = z_max - z_min
        cap_scale = dz if dz > dx else dx

    def scaledLoopVertex(i):
        c = cross[i]
        return (c.x - x_min) / cap_scale, (c.z - z_min) / cap_scale

    loops = []
    mloops = bpymesh.loops
    if begin_cap:
        loops += [co for i in range(nc)
                  for co in scaledLoopVertex(mloops[i].vertex_index)]

    loops += [co for s in range(nsf)
              for c in range(ncf)
              for v in flip(((c / ncf, s / nsf),
                             ((c + 1) / ncf, s / nsf),
                             ((c + 1) / ncf, (s + 1) / nsf),
                             (c / ncf, (s + 1) / nsf)), ccw) for co in v]

    if end_cap:
        lb = ncf * nsf * 4 + (nc if begin_cap else 0)
        loops += [co for i in range(nc) for co
                  in scaledLoopVertex(mloops[lb + i].vertex_index % nc)]

    importMesh_ApplyTextureToLoops(bpymesh, loops)
    bpymesh.validate()
    bpymesh.update()
    return bpymesh


def importMesh_LineSet(geom, ancestry):
    coord = geom.getChildBySpec('Coordinate')
    src_points = coord.getFieldAsArray('point', 3, ancestry, conversion_scale)
    bpycurve = bpy.data.curves.new("LineSet", 'CURVE')
    bpycurve.dimensions = '3D'
    counts = geom.getFieldAsArray('vertexCount', 0, ancestry)
    b = 0
    for n in counts:
        sp = bpycurve.splines.new('POLY')
        sp.points.add(n - 1)

        def points():
            for x in src_points[b:b + n]:
                yield x[0]
                yield x[1]
                yield x[2]
                yield 0
        sp.points.foreach_set('co', [x for x in points()])
        b += n
    return bpycurve


def importMesh_IndexedLineSet(geom, ancestry):
    coord = geom.getChildBySpec('Coordinate')
    points = coord.getFieldAsArray('point', 3, ancestry, conversion_scale) if coord else []
    if not points:
        logger.warning('Warning: IndexedLineSet had no points')
        return None

    ils_lines = geom.getFieldAsArray('coordIndex', 0, ancestry)
    lines_list = []
    line = []
    for il in ils_lines:
        if il == -1:
            lines_list.append(line)
            line = []
        else:
            line.append(int(il))
    lines_list.append(line)

    bpycurve = bpy.data.curves.new('IndexedCurve', 'CURVE')
    bpycurve.dimensions = '3D'

    for line_elem in lines_list:
        if not line_elem:
            continue
        nu = bpycurve.splines.new('POLY')
        nu.points.add(len(line_elem) - 1)
        missing_point = False
        for il, pt in zip(line_elem, nu.points):
            try:
                pt.co[0:3] = points[il]
            except IndexError:
                missing_point = True
        if missing_point:
            logger.warning("More coordIndex than points found")

    return bpycurve


def importMesh_PointSet(geom, ancestry):
    coord = geom.getChildBySpec('Coordinate')
    points = coord.getFieldAsArray('point', 3, ancestry, conversion_scale) if coord else []
    bpymesh = bpy.data.meshes.new("PointSet")
    bpymesh.vertices.add(len(points))
    bpymesh.vertices.foreach_set("co", [a for v in points for a in v])
    bpymesh.update()
    return bpymesh


GLOBALS['CIRCLE_DETAIL'] = 12


def importMesh_Sphere(geom, ancestry):
    r = geom.getFieldAsFloat('radius', 0.5 * conversion_scale, ancestry, conversion_scale)
    subdiv = geom.getFieldAsArray('subdivision', 0, ancestry)
    if subdiv:
        nr = ns = subdiv[0] if len(subdiv) == 1 else subdiv[0]
    else:
        nr = ns = GLOBALS['CIRCLE_DETAIL']

    lau = pi / nr
    lou = 2 * pi / ns

    bpymesh = bpy.data.meshes.new(name="Sphere")
    bpymesh.vertices.add(ns * (nr - 1) + 2)
    co = [0, r, 0, 0, -r, 0]
    co += [r * coe for ring in range(1, nr) for seg in range(ns)
           for coe in (-sin(lou * seg) * sin(lau * ring),
                       cos(lau * ring),
                       -cos(lou * seg) * sin(lau * ring))]
    bpymesh.vertices.foreach_set('co', co)

    num_poly = ns * nr
    num_tri = ns * 2
    num_quad = num_poly - num_tri
    num_loop = num_quad * 4 + num_tri * 3
    tf = bpymesh.polygons
    tf.add(num_poly)
    bpymesh.loops.add(num_loop)
    bpymesh.polygons.foreach_set("loop_start",
                                 tuple(range(0, ns * 3, 3)) +
                                 tuple(range(ns * 3, num_loop - ns * 3, 4)) +
                                 tuple(range(num_loop - ns * 3, num_loop, 3)))

    vb = 2 + (nr - 2) * ns
    fb = (nr - 1) * ns
    tex = bpymesh.uv_layers.new().data

    for seg in range(ns):
        tf[seg].vertices = (0, seg + 2, (seg + 1) % ns + 2)
        tf[fb + seg].vertices = (1, vb + (seg + 1) % ns, vb + seg)
        for lidx, uv in zip(tf[seg].loop_indices,
                            (((seg + 0.5) / ns, 1),
                             (seg / ns, 1 - 1 / nr),
                             ((seg + 1) / ns, 1 - 1 / nr))):
            tex[lidx].uv = uv
        for lidx, uv in zip(tf[fb + seg].loop_indices,
                            (((seg + 0.5) / ns, 0),
                             ((seg + 1) / ns, 1 / nr),
                             (seg / ns, 1 / nr))):
            tex[lidx].uv = uv

    for ring in range(nr - 2):
        tvb = 2 + ring * ns
        bvb = tvb + ns
        rfb = ns * (ring + 1)
        for seg in range(ns):
            nseg = (seg + 1) % ns
            tf[rfb + seg].vertices = (tvb + seg, bvb + seg, bvb + nseg, tvb + nseg)
            for lidx, uv in zip(tf[rfb + seg].loop_indices,
                                ((seg / ns, 1 - (ring + 1) / nr),
                                 (seg / ns, 1 - (ring + 2) / nr),
                                 ((seg + 1) / ns, 1 - (ring + 2) / nr),
                                 ((seg + 1) / ns, 1 - (ring + 1) / nr))):
                tex[lidx].uv = uv

    bpymesh.validate()
    bpymesh.update()
    return bpymesh


def importMesh_Cylinder(geom, ancestry):
    radius = geom.getFieldAsFloat('radius', 1.0 * conversion_scale, ancestry, conversion_scale)
    height = geom.getFieldAsFloat('height', 2.0 * conversion_scale, ancestry, conversion_scale)
    bottom = geom.getFieldAsBool('bottom', True, ancestry)
    side = geom.getFieldAsBool('side', True, ancestry)
    top = geom.getFieldAsBool('top', True, ancestry)
    n = geom.getFieldAsInt('subdivision', GLOBALS['CIRCLE_DETAIL'], ancestry)

    nn = n * 2
    yvalues = (height / 2, -height / 2)
    angle = 2 * pi / n

    verts = [(-radius * sin(angle * i), y, -radius * cos(angle * i))
             for i in range(n) for y in yvalues]
    faces = []
    if side:
        faces += [(i * 2 + 3, i * 2 + 2, i * 2, i * 2 + 1)
                  for i in range(n - 1)] + [(1, 0, nn - 2, nn - 1)]
    if top:
        faces += [[x for x in range(0, nn, 2)]]
    if bottom:
        faces += [[x for x in range(nn - 1, -1, -2)]]

    bpymesh = bpy.data.meshes.new(name="Cylinder")
    bpymesh.from_pydata(verts, [], faces)
    bpymesh.validate()

    loops = []
    if side:
        loops += [co for i in range(n)
                  for co in ((i + 1) / n, 0, (i + 1) / n, 1, i / n, 1, i / n, 0)]
    if top:
        loops += [0.5 + co / 2 for i in range(n)
                  for co in (-sin(angle * i), cos(angle * i))]
    if bottom:
        loops += [0.5 - co / 2 for i in range(n - 1, -1, -1)
                  for co in (sin(angle * i), cos(angle * i))]

    importMesh_ApplyTextureToLoops(bpymesh, loops)
    bpymesh.update()
    return bpymesh


def importMesh_Cone(geom, ancestry):
    n = geom.getFieldAsInt('subdivision', GLOBALS['CIRCLE_DETAIL'], ancestry)
    radius = geom.getFieldAsFloat('bottomRadius', 1.0 * conversion_scale, ancestry, conversion_scale)
    height = geom.getFieldAsFloat('height', 2.0 * conversion_scale, ancestry, conversion_scale)
    bottom = geom.getFieldAsBool('bottom', True, ancestry)
    side = geom.getFieldAsBool('side', True, ancestry)

    d = height / 2
    angle = 2 * pi / n
    verts = [(0, d, 0)] + [(-radius * sin(angle * i), -d, -radius * cos(angle * i)) for i in range(n)]
    faces = []
    if side:
        faces += [(1 + (i + 1) % n, 0, 1 + i) for i in range(n)]
    if bottom:
        faces += [[i for i in range(n, 0, -1)]]

    bpymesh = bpy.data.meshes.new(name="Cone")
    bpymesh.from_pydata(verts, [], faces)
    bpymesh.validate()

    loops = []
    if side:
        loops += [co for i in range(n)
                  for co in ((i + 1) / n, 0, (i + 0.5) / n, 1, i / n, 0)]
    if bottom:
        loops += [0.5 - co / 2 for i in range(n - 1, -1, -1)
                  for co in (sin(angle * i), cos(angle * i))]
    importMesh_ApplyTextureToLoops(bpymesh, loops)
    bpymesh.update()
    return bpymesh


def importMesh_Box(geom, ancestry):
    (dx, dy, dz) = geom.getFieldAsFloatTuple('size', (2.0 * conversion_scale, 2.0 * conversion_scale, 2.0 * conversion_scale), ancestry, conversion_scale)
    dx /= 2
    dy /= 2
    dz /= 2

    bpymesh = bpy.data.meshes.new(name="Box")
    bpymesh.vertices.add(8)
    co = (dx, dy, dz, -dx, dy, dz, -dx, dy, -dz, dx, dy, -dz,
          dx, -dy, dz, -dx, -dy, dz, -dx, -dy, -dz, dx, -dy, -dz)
    bpymesh.vertices.foreach_set('co', co)

    bpymesh.loops.add(6 * 4)
    bpymesh.polygons.add(6)
    bpymesh.polygons.foreach_set('loop_start', range(0, 6 * 4, 4))
    bpymesh.polygons.foreach_set('loop_total', (4,) * 6)
    bpymesh.polygons.foreach_set('vertices', (
        0, 1, 2, 3,
        4, 0, 3, 7,
        7, 3, 2, 6,
        6, 2, 1, 5,
        5, 1, 0, 4,
        7, 6, 5, 4))

    bpymesh.validate()
    d = bpymesh.uv_layers.new().data
    d.foreach_set('uv', (
        1, 0, 0, 0, 0, 1, 1, 1,
        0, 0, 0, 1, 1, 1, 1, 0,
        0, 0, 0, 1, 1, 1, 1, 0,
        0, 0, 0, 1, 1, 1, 1, 0,
        0, 0, 0, 1, 1, 1, 1, 0,
        1, 0, 0, 0, 0, 1, 1, 1))

    bpymesh.flip_normals()
    bpymesh.update()
    return bpymesh


def appearance_CreateMaterial(vrmlname, mat, ancestry, is_vcol):
    if mat:
        mat_name = mat.getDefName()
        diff_color = mat.getFieldAsFloatTuple('diffuseColor', [0.8, 0.8, 0.8], ancestry)
        emit_color = mat.getFieldAsFloatTuple('emissiveColor', [0.0, 0.0, 0.0], ancestry)
        shininess = mat.getFieldAsFloat('shininess', 0.2, ancestry)
        alpha = 1.0 - mat.getFieldAsFloat('transparency', 0.0, ancestry)
    else:
        mat_name = None
        diff_color = [0.8, 0.8, 0.8]
        emit_color = [0.0, 0.0, 0.0]
        shininess = 0.2
        alpha = 1.0

    bpymat = bpy.data.materials.new(mat_name if mat_name else vrmlname)
    bpymat_wrap = node_shader_utils.PrincipledBSDFWrapper(bpymat, is_readonly=False)

    bpymat_wrap.base_color = diff_color
    bpymat_wrap.emission_color = emit_color
    if emit_color != [0.0, 0.0, 0.0]:
        bsdf_node = bpymat.node_tree.nodes.get("Principled BSDF")
        if bsdf_node:
            bsdf_node.inputs["Emission Strength"].default_value = 1.0

    bpymat_wrap.roughness = 1.0 - shininess
    bpymat_wrap.alpha = alpha
    if alpha < 1.0:
        bpymat.surface_render_method = "BLENDED"

    if is_vcol:
        node_vertex_color = bpymat.node_tree.nodes.new("ShaderNodeVertexColor")
        node_vertex_color.location = (-200, 300)
        node_vertex_color.layer_name = "ColorPerCorner"
        bpymat.node_tree.links.new(
            bpymat_wrap.node_principled_bsdf.inputs["Base Color"],
            node_vertex_color.outputs["Color"]
        )

    return bpymat_wrap


def appearance_CreateDefaultMaterial():
    bpymat = bpy.data.materials.new("Material")
    bpymat_wrap = node_shader_utils.PrincipledBSDFWrapper(bpymat, is_readonly=False)
    bpymat_wrap.roughness = 0.8
    bpymat_wrap.base_color = (0.8, 0.8, 0.8)
    bpymat_wrap.alpha = 1.0
    return bpymat_wrap


def web_resource_download_helper(url, default_ext, default_name, output_path=None):
    if url in download_cache:
        return download_cache[url]

    if not bpy.app.online_access:
        logger.warning("Can't download web resource: online access denied by user")
        return None

    import requests
    from tempfile import gettempdir
    from mimetypes import guess_extension

    if not output_path:
        output_path = gettempdir()
    elif not os.path.isdir(output_path):
        raise ValueError("Provided output_path must be a directory.")

    try:
        response = requests.get(url, stream=True)
        response.raise_for_status()
        content_type = response.headers.get('Content-Type', '')
        ext = guess_extension(content_type.split(';')[0].strip()) or default_ext
        filename = os.path.basename(url.split('?')[0]) or default_name
        if '.' not in filename:
            filename += ext

        full_path = os.path.join(output_path, filename)
        with open(full_path, 'wb') as f:
            for chunk in response.iter_content(1024):
                f.write(chunk)

        download_cache[url] = full_path
        return full_path
    except Exception as e:
        logger.warning(f"Failed to download web resource: {e}")
        return None


def download_image(url, output_path=None):
    return web_resource_download_helper(url, '.jpg', "downloaded_image", output_path=output_path)


def appearance_LoadImageTextureFile(ima_urls, node):
    bpyima = None
    for f in ima_urls:
        if f.startswith(('https://', 'http://', 'www.')):
            f = download_image(f, os.path.dirname(current_file_path)) or f
        dirname = os.path.dirname(node.getFilename())
        bpyima = image_utils.load_image(f, dirname,
                                        place_holder=False,
                                        recursive=False,
                                        convert_callback=imageConvertCompat)
        if bpyima:
            break
    return bpyima


def appearance_LoadImageTexture(imageTexture, ancestry, node):
    ima_urls = imageTexture.getFieldAsMFStringArray('url', None, ancestry)
    if ima_urls is None:
        logger.warning("warning, image with no URL, this is odd")
        return None

    bpyima = appearance_LoadImageTextureFile(ima_urls, node)
    if not bpyima:
        logger.warning("ImportX3D : unable to load texture from %s" % ima_urls)
    else:
        if bpyima.depth not in {32, 128}:
            bpyima.alpha_mode = 'NONE'
    return bpyima


def appearance_LoadTexture(tex_node, ancestry, node):
    if tex_node.reference:
        return tex_node.getRealNode().parsed

    desc = tex_node.desc()
    if desc and desc in texture_cache:
        bpyima = texture_cache[desc]
        if tex_node.canHaveReferences():
            tex_node.parsed = bpyima
        return bpyima

    if tex_node.getSpec() in {'ImageTexture', 'MovieTexture'}:
        bpyima = appearance_LoadImageTexture(tex_node, ancestry, node)
    else:
        bpyima = appearance_LoadPixelTexture(tex_node, ancestry)

    if bpyima:
        if desc:
            texture_cache[desc] = bpyima
        if tex_node.canHaveReferences():
            tex_node.parsed = bpyima

    return bpyima


def appearance_ExpandCachedMaterial(bpymat):
    return (bpymat, None, False)


def appearance_MakeDescCacheKey(material, tex_node):
    mat_desc = material.desc() if material else "Default"
    tex_desc = tex_node.desc() if tex_node else "Default"

    if not ((tex_node and tex_desc is None) or (material and mat_desc is None)):
        return (mat_desc, tex_desc)
    elif not tex_node and not material:
        return ("Default", "Default")
    return None


def rotate_image_texture(bpymat_wrap, bpyima):
    node_tree = bpymat_wrap.material.node_tree
    for node in node_tree.nodes:
        if node.type == 'TEX_IMAGE' and node.image == bpyima:
            node_tex_coord = node_tree.nodes.new("ShaderNodeTexCoord")
            node_mapping = node_tree.nodes.new("ShaderNodeMapping")
            node_mapping.vector_type = 'POINT'
            node_mapping.inputs['Rotation'].default_value = (0, 0, 0)
            node_tree.links.new(node_tex_coord.outputs["UV"], node_mapping.inputs["Vector"])
            node_tree.links.new(node_mapping.outputs["Vector"], node.inputs["Vector"])
            node_mapping.location.x -= 500
            node_mapping.location.y += 300
            node_tex_coord.location.x -= 700
            node_tex_coord.location.y += 300
            node.location.y -= 300
            break
    return bpymat_wrap


def apply_video_texture_settings(bpymat_wrap, bpyima, tex_node, ancestry):
    loop = tex_node.getFieldAsBool('loop', False, ancestry)
    start_time_seconds = tex_node.getFieldAsFloat('startTime', 0.0, ancestry)
    stop_time_seconds = tex_node.getFieldAsFloat('stopTime', -1.0, ancestry)

    fps = bpy.context.scene.render.fps
    start_frame = int(start_time_seconds * fps)
    end_frame = bpyima.frame_duration if stop_time_seconds == -1 else int((bpyima.frame_duration / fps) * stop_time_seconds)

    node_tree = bpymat_wrap.material.node_tree
    for node in node_tree.nodes:
        if node.type == 'TEX_IMAGE' and node.image == bpyima:
            image_user = node.image_user
            image_user.use_auto_refresh = True
            image_user.use_cyclic = loop
            image_user.frame_start = start_frame
            image_user.frame_duration = end_frame
            node.location.y -= 300
            break
    return bpymat_wrap


def appearance_Create(vrmlname, material, tex_node, ancestry, node, is_vcol):
    bpyima = None
    tex_has_alpha = False

    if material:
        bpymat_wrap = appearance_CreateMaterial(vrmlname, material, ancestry, is_vcol)
    else:
        bpymat_wrap = appearance_CreateDefaultMaterial()

    if tex_node:
        bpyima = appearance_LoadTexture(tex_node, ancestry, node)

    if bpyima:
        repeatS = tex_node.getFieldAsBool('repeatS', True, ancestry)
        repeatT = tex_node.getFieldAsBool('repeatT', True, ancestry)
        bpymat_wrap.base_color_texture.image = bpyima

        if tex_node.getSpec() == 'ImageTexture':
            bpymat_wrap = rotate_image_texture(bpymat_wrap, bpyima)

        extension = "REPEAT" if repeatS or repeatT else "CLIP"
        bpymat_wrap.base_color_texture.extension = extension

        tex_has_alpha = bpyima.alpha_mode not in {'NONE', 'CHANNEL_PACKED'}
        if tex_has_alpha:
            bpymat_wrap.alpha_texture.image = bpyima
            bpymat_wrap.alpha_texture.extension = extension

        if tex_node.getSpec() == 'MovieTexture':
            bpymat_wrap = apply_video_texture_settings(bpymat_wrap, bpyima, tex_node, ancestry)

    return (bpymat_wrap.material, bpyima, tex_has_alpha)


def importShape_LoadAppearance(vrmlname, appr, ancestry, node, is_vcol):
    if appr.reference and appr.getRealNode().parsed:
        return appearance_ExpandCachedMaterial(appr.getRealNode().parsed)

    tex_node = appr.getChildBySpec(('ImageTexture', 'PixelTexture', 'MovieTexture'))
    material = appr.getChildBySpec('Material')

    if material and material.reference and not tex_node and material.getRealNode().parsed:
        return appearance_ExpandCachedMaterial(material.getRealNode().parsed)

    cache_key = appearance_MakeDescCacheKey(material, tex_node)
    if cache_key and cache_key in material_cache:
        bpymat = material_cache[cache_key]
        if appr.canHaveReferences():
            appr.parsed = bpymat
        if material and material.canHaveReferences() and not tex_node:
            material.parsed = bpymat
        return appearance_ExpandCachedMaterial(bpymat)

    (bpymat, bpyima, tex_has_alpha) = appearance_Create(vrmlname, material, tex_node, ancestry, node, is_vcol)

    if appr.canHaveReferences():
        appr.parsed = bpymat
    if cache_key:
        material_cache[cache_key] = bpymat
    if material and material.canHaveReferences() and not tex_node:
        material.parsed = bpymat

    return (bpymat, bpyima, tex_has_alpha)


def appearance_LoadPixelTexture(pixelTexture, ancestry):
    def extract_pixel_colors(data_string):
        hex_pattern = re.compile(r'0x[0-9a-fA-F]{6}')
        return [int(c, 0) for c in hex_pattern.findall(data_string)]

    image = pixelTexture.getFieldAsArray('image', 0, ancestry)
    (w, h, plane_count) = image[0:3]
    has_alpha = plane_count in {2, 4}
    pixels = extract_pixel_colors(str(pixelTexture))
    if len(pixels) == 0:
        pixels = image[3:]
    if len(pixels) != w * h:
        logger.warning(f"ImportX3D warning: pixel count in PixelTexture is off. Pixels: {len(pixels)}, Width: {w}, Height: {h}")

    bpyima = bpy.data.images.new("PixelTexture", w, h, alpha=has_alpha, float_buffer=True)
    if not has_alpha:
        bpyima.alpha_mode = 'NONE'

    if len(pixels) != 0:
        if plane_count == 3:
            bpyima.pixels = [(cco & 0xff) / 255 for pixel in pixels
                             for cco in (pixel >> 16, pixel >> 8, pixel, 255)]
        elif plane_count == 4:
            bpyima.pixels = [(cco & 0xff) / 255 for pixel in pixels
                             for cco in (pixel >> 24, pixel >> 16, pixel >> 8, pixel)]
        elif plane_count == 1:
            bpyima.pixels = [(cco & 0xff) / 255 for pixel in pixels
                             for cco in (pixel, pixel, pixel, 255)]
        elif plane_count == 2:
            bpyima.pixels = [(cco & 0xff) / 255 for pixel in pixels
                             for cco in (pixel >> 8, pixel >> 8, pixel >> 8, pixel)]
    bpyima.update()
    return bpyima


def importShape_ProcessObject(
        bpycollection, vrmlname, bpydata, geom, geom_spec, node,
        bpymat, has_alpha, texmtx, ancestry,
        global_matrix, solidify, solidify_value):

    vrmlname += "_" + geom_spec
    bpydata.name = vrmlname

    if type(bpydata) == bpy.types.Curve:
        if bpymat:
            bpydata.materials.append(bpymat)

    if type(bpydata) == bpy.types.Mesh:
        creaseAngle = geom.getFieldAsFloat('creaseAngle', None, ancestry)
        if creaseAngle is not None and not bpydata.has_custom_normals:
            bpydata.set_sharp_from_angle(angle=creaseAngle)
        else:
            bpydata.polygons.foreach_set("use_smooth", [False] * len(bpydata.polygons))

        if bpymat:
            bpydata.materials.append(bpymat)

        if bpydata.uv_layers:
            if has_alpha and bpymat:
                bpymat.surface_render_method = "BLENDED"
            if texmtx:
                uv_copy = Vector()
                for l in bpydata.uv_layers.active.data:
                    luv = l.uv
                    uv_copy.x = luv[0]
                    uv_copy.y = luv[1]
                    l.uv[:] = (uv_copy @ texmtx)[0:2]

    elif type(bpydata) == bpy.types.TextCurve:
        if bpymat:
            bpydata.materials.append(bpymat)

    bpyob = node.blendObject = bpy.data.objects.new(vrmlname, bpydata)
    bpyob.matrix_world = getFinalMatrix(node, None, ancestry, global_matrix)
    if solidify and bpyob.type == 'MESH':
        solidify_modifier = bpyob.modifiers.new(name="Solidify", type='SOLIDIFY')
        solidify_modifier.thickness = solidify_value
        solidify_modifier.offset = 0
    bpycollection.objects.link(bpyob)
    bpyob.select_set(True)

    if bpyob.type == 'FONT':
        process_font_object(bpyob)

    if DEBUG:
        bpyob["source_line_no"] = geom.lineno


def process_font_object(bpyob):
    if bpyob.data["bold"] or bpyob.data["italic"]:
        bpy.context.view_layer.objects.active = bpyob
        bpy.ops.object.mode_set(mode='EDIT')
        bpy.ops.font.select_all()
        if bpyob.data["bold"]:
            bpy.ops.font.style_toggle(style='BOLD')
            del bpyob.data["bold"]
        if bpyob.data["italic"]:
            bpy.ops.font.style_toggle(style='ITALIC')
            del bpyob.data["italic"]
        bpy.ops.object.mode_set(mode='OBJECT')


def importText(geom, ancestry):
    fmt = geom.getChildBySpec('FontStyle')
    if fmt:
        size = fmt.getFieldAsFloat("size", 1, ancestry)
        horizontal_alignment = fmt.getFieldAsMFStringArray("justify", [], ancestry)
        line_height = fmt.getFieldAsFloat("spacing", 1, ancestry)
        style = fmt.getFieldAsMFStringArray("style", None, ancestry)
        family = fmt.getFieldAsMFStringArray("family", None, ancestry)
    else:
        size = 1
        horizontal_alignment = "BEGIN"
        line_height = 1
        style = None
        family = None

    body = geom.getFieldAsMFStringArray("string", [], ancestry)
    bpytext = bpy.data.curves.new(name="Text", type='FONT')
    bpytext.offset_y = - size
    bpytext.body = "\n".join(body)
    bpytext.size = size
    bpytext.space_line = line_height
    for align in horizontal_alignment:
        if align == "BEGIN":
            bpytext.align_x = "LEFT"
            break
        elif align == "MIDDLE":
            bpytext.align_x = "CENTER"
            break
        elif align == "END":
            bpytext.align_x = "RIGHT"
            break

    bpytext["bold"] = False
    bpytext["italic"] = False
    if style is not None:
        for s in style:
            if s == "BOLD":
                bpytext["bold"] = True
            elif s == "ITALIC":
                bpytext["italic"] = True
            elif s == "BOLDITALIC":
                bpytext["bold"] = True
                bpytext["italic"] = True

    if family is not None:
        for font in family:
            if font.upper() == "SANS":
                font = "Arial"
            elif font.upper() == "SERIF":
                font = "Times New Roman"
            elif font.upper() == "TYPEWRITER":
                font = "Courier New"
            else:
                for extension in [".ttf", ".otf", ".woff", ".woff2"]:
                    font = ''.join(font.rsplit(extension, maxsplit=1))
            font_path = search_for_font_file(font)
            if font_path:
                font_regular = bpy.data.fonts.load(font_path["regular"]) if font_path["regular"] not in bpy.data.fonts else bpy.data.fonts[font_path["regular"]]
                font_bold = bpy.data.fonts.load(font_path["bold"]) if font_path["bold"] not in bpy.data.fonts else bpy.data.fonts[font_path["bold"]]
                font_italic = bpy.data.fonts.load(font_path["italic"]) if font_path["italic"] not in bpy.data.fonts else bpy.data.fonts[font_path["italic"]]
                font_bolditalic = bpy.data.fonts.load(font_path["bold_italic"]) if font_path["bold_italic"] not in bpy.data.fonts else bpy.data.fonts[font_path["bold_italic"]]
                bpytext.font = font_regular
                bpytext.font_bold = font_bold
                bpytext.font_italic = font_italic
                bpytext.font_bold_italic = font_bolditalic
                break

    return bpytext


def search_for_font_file(font_name_spec):
    if font_name_spec in font_variants_cache:
        return font_variants_cache[font_name_spec]

    import platform
    from pathlib import Path

    def get_font_paths():
        if platform.system() == "Windows":
            return ["C:\\Windows\\Fonts", str(Path.home() / "AppData" / "Local" / "Microsoft" / "Windows" / "Fonts")]
        elif platform.system() == "Darwin":
            return ["/Library/Fonts", "~/Library/Fonts"]
        elif platform.system() == "Linux":
            return ["/usr/share/fonts", "~/.fonts", "~/.local/share/fonts"]
        return []

    def load_all_fonts(font_path):
        valid_extensions = [".ttf", ".otf", ".woff", ".woff2"]
        font_files = []
        for root, _, files in os.walk(os.path.expanduser(font_path)):
            for file in files:
                if any(file.lower().endswith(ext) for ext in valid_extensions):
                    font_files.append(os.path.join(root, file))
        return font_files

    def find_font_variants(font_name, curr_dir):
        style_keywords = {
            "regular": ["regular", "book", "normal"],
            "bold": ["bold", "b", "bd"],
            "italic": ["italic", "oblique", "i"],
            "bold_italic": ["bolditalic", "boldoblique", "bi"]
        }
        font_paths = get_font_paths()

        def find_font_by_style(indexed_font_files, font_name_str, keywords, allow_no_keyword=False):
            lower_font = font_name_str.lower()
            for fuzzy_font in [lower_font, lower_font[:5], lower_font[:4]]:
                if allow_no_keyword:
                    for font in indexed_font_files:
                        if Path(font).stem.lower() == fuzzy_font:
                            return font
                for font in font_files:
                    for keyword in keywords:
                        if Path(font).stem.lower() == (fuzzy_font + keyword):
                            return font
                for font in indexed_font_files:
                    if fuzzy_font in Path(font).stem.lower() and any(k in Path(font).stem.lower() for k in keywords):
                        return font
            return None

        fonts = {"regular": None, "bold": None, "italic": None, "bold_italic": None}
        for font_path in font_paths:
            font_files = load_all_fonts(font_path)
            if not font_files:
                continue
            fonts["regular"] = fonts["regular"] or find_font_by_style(font_files, font_name, style_keywords["regular"], allow_no_keyword=True)
            fonts["bold"] = fonts["bold"] or find_font_by_style(font_files, font_name, style_keywords["bold"])
            fonts["italic"] = fonts["italic"] or find_font_by_style(font_files, font_name, style_keywords["italic"])
            fonts["bold_italic"] = fonts["bold_italic"] or find_font_by_style(font_files, font_name, style_keywords["bold_italic"])
            if any(value is not None for value in fonts.values()):
                break

        if not any(fonts.values()):
            for extension in [".ttf", ".otf", ".woff", ".woff2"]:
                font_file = Path(curr_dir + font_name + extension)
                if font_file.is_file():
                    fonts["regular"] = fonts["bold"] = fonts["italic"] = fonts["bold_italic"] = font_file
                    return fonts

        regular_font = fonts["regular"]
        if regular_font is not None:
            for style in fonts:
                if fonts[style] is None:
                    fonts[style] = regular_font
            return fonts

        return fonts if all(fonts.values()) else None

    try:
        font_variants = find_font_variants(font_name_spec, current_file_path)
    except Exception as e:
        logger.exception(e)
        font_variants = None

    font_variants_cache[font_name_spec] = font_variants
    return font_variants


geometry_importers = {
    'IndexedFaceSet': importMesh_IndexedFaceSet,
    'IndexedTriangleSet': importMesh_IndexedTriangleSet,
    'IndexedTriangleStripSet': importMesh_IndexedTriangleStripSet,
    'IndexedTriangleFanSet': importMesh_IndexedTriangleFanSet,
    'IndexedLineSet': importMesh_IndexedLineSet,
    'TriangleSet': importMesh_TriangleSet,
    'TriangleStripSet': importMesh_TriangleStripSet,
    'TriangleFanSet': importMesh_TriangleFanSet,
    'LineSet': importMesh_LineSet,
    'Rectangle2D': importMesh_Rectangle2D,
    'ElevationGrid': importMesh_ElevationGrid,
    'Extrusion': importMesh_Extrusion,
    'PointSet': importMesh_PointSet,
    'Sphere': importMesh_Sphere,
    'Box': importMesh_Box,
    'Cylinder': importMesh_Cylinder,
    'Cone': importMesh_Cone,
    'Text': importText,
}


def importShape(bpycollection, node, ancestry, global_matrix, solidify, solidify_value):
    def isGeometry(spec):
        return spec != "Appearance" and not spec.startswith("Metadata")

    bpyob = node.getRealNode().blendObject
    if bpyob is not None:
        bpyob = node.blendData = node.blendObject = bpyob.copy()
        bpyob.matrix_world = getFinalMatrix(node, None, ancestry, global_matrix)
        bpycollection.objects.link(bpyob)
        bpyob.select_set(True)
        return

    vrmlname = node.getDefName() or 'Shape'
    appr = node.getChildBySpec('Appearance')
    geom = node.getChildBySpecCondition(isGeometry)
    if not geom:
        return

    bpymat = None
    bpyima = None
    texmtx = None
    tex_has_alpha = False
    is_vcol = (geom.getChildBySpec(['Color', 'ColorRGBA']) is not None)

    if appr:
        (bpymat, bpyima, tex_has_alpha) = importShape_LoadAppearance(vrmlname, appr, ancestry, node, is_vcol)
        textx = appr.getChildBySpec('TextureTransform')
        if textx:
            texmtx = translateTexTransform(textx, ancestry)
    elif is_vcol:
        bpymat = appearance_CreateMaterial(vrmlname, None, ancestry, is_vcol).material

    geom_spec = geom.getSpec()
    geom_fn = geometry_importers.get(geom_spec)
    if geom_fn is not None:
        bpydata = geom_fn(geom, ancestry)
        if bpydata is None:
            logger.warning('ImportX3D warning: empty shape, skipping node "%s"' % vrmlname)
            return

        importShape_ProcessObject(
            bpycollection, vrmlname, bpydata, geom, geom_spec,
            node, bpymat, tex_has_alpha, texmtx,
            ancestry, global_matrix, solidify, solidify_value)
    else:
        logger.warning('ImportX3D warning: unsupported type "%s"' % geom_spec)


def importLamp_PointLight(node, ancestry):
    vrmlname = node.getDefName() or 'PointLight'
    color = node.getFieldAsFloatTuple('color', (1.0, 1.0, 1.0), ancestry)
    intensity = node.getFieldAsFloat('intensity', 1.0, ancestry)
    location = node.getFieldAsFloatTuple('location', (0.0, 0.0, 0.0), ancestry, conversion_scale)
    radius = node.getFieldAsFloat('radius', 100.0, ancestry, conversion_scale)

    bpylamp = bpy.data.lights.new(vrmlname, 'POINT')
    bpylamp.energy = intensity
    bpylamp.cutoff_distance = radius
    bpylamp.color = color
    mtx = Matrix.Translation(Vector(location))
    return bpylamp, mtx


def importLamp_DirectionalLight(node, ancestry):
    vrmlname = node.getDefName() or 'DirectLight'
    color = node.getFieldAsFloatTuple('color', (1.0, 1.0, 1.0), ancestry)
    direction = node.getFieldAsFloatTuple('direction', (0.0, 0.0, -1.0), ancestry)
    intensity = node.getFieldAsFloat('intensity', 1.0, ancestry)

    bpylamp = bpy.data.lights.new(vrmlname, 'SUN')
    bpylamp.energy = intensity
    bpylamp.color = color
    mtx = Vector(direction).to_track_quat('-Z', 'Y').to_matrix().to_4x4()
    return bpylamp, mtx


def importLamp_SpotLight(node, ancestry):
    vrmlname = node.getDefName() or 'SpotLight'
    beamWidth = node.getFieldAsFloat('beamWidth', 1.570796, ancestry)
    color = node.getFieldAsFloatTuple('color', (1.0, 1.0, 1.0), ancestry)
    cutOffAngle = node.getFieldAsFloat('cutOffAngle', 0.785398, ancestry) * 2.0
    direction = node.getFieldAsFloatTuple('direction', (0.0, 0.0, -1.0), ancestry)
    intensity = node.getFieldAsFloat('intensity', 1.0, ancestry)
    location = node.getFieldAsFloatTuple('location', (0.0, 0.0, 0.0), ancestry, conversion_scale)
    radius = node.getFieldAsFloat('radius', 100.0, ancestry, conversion_scale)

    bpylamp = bpy.data.lights.new(vrmlname, 'SPOT')
    bpylamp.energy = intensity
    bpylamp.cutoff_distance = radius
    bpylamp.color = color
    bpylamp.spot_size = cutOffAngle
    bpylamp.spot_blend = 0.0 if beamWidth > cutOffAngle else (0.5 if cutOffAngle == 0.0 else beamWidth / cutOffAngle)
    mtx = Matrix.Translation(location) @ Vector(direction).to_track_quat('-Z', 'Y').to_matrix().to_4x4()
    return bpylamp, mtx


def importLamp(bpycollection, node, spec, ancestry, global_matrix):
    if spec == 'PointLight':
        bpylamp, mtx = importLamp_PointLight(node, ancestry)
    elif spec == 'DirectionalLight':
        bpylamp, mtx = importLamp_DirectionalLight(node, ancestry)
    elif spec == 'SpotLight':
        bpylamp, mtx = importLamp_SpotLight(node, ancestry)
    else:
        logger.warning("Error, not a lamp")
        raise ValueError

    bpyob = node.blendData = node.blendObject = bpy.data.objects.new(bpylamp.name, bpylamp)
    bpycollection.objects.link(bpyob)
    bpyob.select_set(True)
    bpyob.matrix_world = getFinalMatrix(node, mtx, ancestry, global_matrix)


def importViewpoint(bpycollection, node, ancestry, global_matrix):
    name = node.getDefName() or 'Viewpoint'
    fieldOfView = node.getFieldAsFloat('fieldOfView', 0.785398, ancestry)
    orientation = node.getFieldAsFloatTuple('orientation', (0.0, 0.0, 1.0, 0.0), ancestry)
    position = node.getFieldAsFloatTuple('position', (0.0, 0.0, 0.0), ancestry, conversion_scale)

    bpycam = bpy.data.cameras.new(name)
    bpycam.angle = fieldOfView
    mtx = Matrix.Translation(Vector(position)) @ translateRotation(orientation)

    bpyob = node.blendData = node.blendObject = bpy.data.objects.new(name, bpycam)
    bpycollection.objects.link(bpyob)
    bpyob.select_set(True)
    bpyob.matrix_world = getFinalMatrix(node, mtx, ancestry, global_matrix)


def importTransform(bpycollection, node, ancestry, global_matrix):
    name = node.getDefName() or 'Transform'
    bpyob = node.blendData = node.blendObject = bpy.data.objects.new(name, None)
    bpycollection.objects.link(bpyob)
    bpyob.select_set(True)
    bpyob.matrix_world = getFinalMatrix(node, None, ancestry, global_matrix)
    bpyob.empty_display_type = 'PLAIN_AXES'
    bpyob.empty_display_size = 0.2


def importAudio(bpycollection, node, ancestry, global_matrix):
    source = node.getChildBySpec('AudioClip') or node.getChildBySpec('MovieTexture')
    name = node.getDefName() or 'Sound'
    audio_urls = source.getFieldAsMFStringArray('url', None, ancestry)

    if not audio_urls and source:
        logger.warning("warning, Sound source with no URL, this is odd")
        return None

    bpyaudio = load_audio_file(audio_urls, node)
    if not bpyaudio and source:
        logger.warning("warning, Sound source failed to load")
        return None

    location = node.getFieldAsFloatTuple('location', (0.0, 0.0, 0.0), ancestry, conversion_scale)
    direction = node.getFieldAsFloatTuple('direction', (0.0, 0.0, 0.0), ancestry, conversion_scale)
    volume = node.getFieldAsFloat('intensity', 1.0, ancestry, conversion_scale)
    max_distance = max(
        node.getFieldAsFloat('maxBack', None, ancestry, conversion_scale),
        node.getFieldAsFloat('maxFront', None, ancestry, conversion_scale)
    )
    ref_distance = max(
        node.getFieldAsFloat('minBack', None, ancestry, conversion_scale),
        node.getFieldAsFloat('minFront', None, ancestry, conversion_scale)
    )

    bpy.ops.object.speaker_add(location=location)
    bpyspeaker = node.blendData = bpy.context.object
    local_axis = mathutils.Vector((0, 0, 0))
    bpyspeaker.rotation_mode = 'QUATERNION'
    bpyspeaker.rotation_quaternion = local_axis.rotation_difference(direction)
    bpyspeaker.data.name = name
    bpyspeaker.data.volume = volume
    if max_distance:
        bpyspeaker.data.distance_max = max_distance
    if ref_distance:
        bpyspeaker.data.distance_reference = ref_distance

    if source:
        pitch = source.getFieldAsFloat('pitch', 1.0, ancestry, conversion_scale)
        description = source.getFieldAsString('description', None, ancestry)
        start_time_seconds = source.getFieldAsFloat('startTime', 0.0, ancestry, conversion_scale)
        stop_time_seconds = source.getFieldAsFloat('stopTime', 0.0, ancestry, conversion_scale)

        bpyspeaker.data.sound = bpyaudio
        bpyspeaker.data.pitch = pitch
        if description:
            bpyspeaker["description"] = description

        fps = bpy.context.scene.render.fps
        start_frame = int(start_time_seconds * fps)
        if start_time_seconds > 0.0 and bpyspeaker.animation_data:
            for track in bpyspeaker.animation_data.nla_tracks:
                for strip in track.strips:
                    strip.frame_start_ui = start_frame

        if stop_time_seconds > 0.0 and stop_time_seconds > start_time_seconds:
            end_frame = int(stop_time_seconds * fps)
            bpyspeaker.data.keyframe_insert(data_path="volume", frame=start_frame)
            bpyspeaker.data.keyframe_insert(data_path="volume", frame=end_frame - 1)
            bpyspeaker.data.volume = 0.0
            bpyspeaker.data.keyframe_insert(data_path="volume", frame=end_frame)

    bpyspeaker.data.update_tag()
    bpycollection.objects.unlink(bpyspeaker)
    bpycollection.objects.link(bpyspeaker)


def load_audio_file(audio_urls, node):
    bpyaudio = None
    for f in audio_urls:
        file_path = os.path.dirname(current_file_path)
        if f.startswith(('https://', 'http://', 'www.')):
            f = download_audio(f, file_path) or f
        else:
            if not os.path.isabs(f):
                f = os.path.join(os.path.dirname(current_file_path), f)

        if os.path.exists(f):
            bpyaudio = bpy.data.sounds.load(f, check_existing=True)
            if bpyaudio:
                break
    return bpyaudio


def download_audio(url, output_path=None):
    return web_resource_download_helper(url, '.wav', "downloaded_audio", output_path=output_path)


# -----------------------------------------------------------------------------------
# Animation / ROUTE resolution helpers
# -----------------------------------------------------------------------------------

def fcurve_set_loop(fcu, loop=True):
    """Applies cyclic repetition to an F-Curve via a CYCLES modifier if loop is True."""
    if not loop or fcu is None or not hasattr(fcu, "modifiers"):
        return
    if not any(mod.type == 'CYCLES' for mod in fcu.modifiers):
        fcu.modifiers.new(type='CYCLES')


def action_fcurve_ensure(action, data_path, array_index, datablock=None):
    """
    Ensures an F-Curve exists on an Action for a given data_path and index.
    Fully supports Blender 5.0+ / 5.2+ Slotted Actions as well as older versions.
    """
    # 1. Blender 4.4+ / 5.x official API when datablock is supplied
    if hasattr(action, "fcurve_ensure_for_datablock") and datablock is not None:
        try:
            fcu = action.fcurve_ensure_for_datablock(datablock, data_path, index=array_index)
            if fcu:
                return fcu
        except Exception:
            pass

    # 2. Slotted actions (Blender 4.4 / 5.0 / 5.2+)
    if hasattr(action, "slots"):
        slot = None
        if len(action.slots) > 0:
            slot = action.slots[0]
        else:
            id_type = 'OBJECT'
            name = "Slot"
            if datablock is not None:
                id_type = getattr(datablock, "id_type", 'OBJECT')
                name = getattr(datablock, "name", "Slot")
            elif "key_blocks" in data_path:
                id_type = 'KEY'
                name = "ShapeKeys"

            for candidate in (id_type, 'OBJECT', 'KEY'):
                try:
                    slot = action.slots.new(id_type=candidate, name=name)
                    break
                except Exception:
                    pass
                try:
                    slot = action.slots.new(candidate, name)
                    break
                except Exception:
                    pass
            if slot is None:
                try:
                    slot = action.slots.new(name=name)
                except Exception:
                    pass
            if slot is None:
                try:
                    slot = action.slots.new()
                except Exception:
                    pass

        if slot is not None:
            # Try anim_utils helper
            try:
                from bpy_extras import anim_utils
                channelbag = anim_utils.action_ensure_channelbag_for_slot(action, slot)
                if channelbag is not None:
                    for fcu in channelbag.fcurves:
                        if fcu.data_path == data_path and fcu.array_index == array_index:
                            return fcu
                    try:
                        return channelbag.fcurves.new(data_path=data_path, index=array_index)
                    except TypeError:
                        return channelbag.fcurves.new(data_path, array_index)
            except Exception:
                pass

            # Manual layer -> strip -> channelbag fallback
            try:
                if not hasattr(action, "layers") or len(action.layers) == 0:
                    layer = action.layers.new("MainLayer")
                else:
                    layer = action.layers[0]

                if len(layer.strips) == 0:
                    try:
                        strip = layer.strips.new(type='KEYFRAME')
                    except Exception:
                        strip = layer.strips.new()
                else:
                    strip = layer.strips[0]

                channelbag = strip.channelbag(slot, ensure=True) if hasattr(strip, "channelbag") else None
                if channelbag is not None:
                    for fcu in channelbag.fcurves:
                        if fcu.data_path == data_path and fcu.array_index == array_index:
                            return fcu
                    try:
                        return channelbag.fcurves.new(data_path=data_path, index=array_index)
                    except TypeError:
                        return channelbag.fcurves.new(data_path, array_index)
            except Exception:
                pass

    # 3. Legacy actions (Blender <= 4.3)
    if hasattr(action, "fcurves"):
        for fcu in action.fcurves:
            if fcu.data_path == data_path and fcu.array_index == array_index:
                return fcu
        return action.fcurves.new(data_path=data_path, index=array_index)

    raise AttributeError(
        f"Unable to create or access F-Curve on Action '{action.name}' for data_path '{data_path}'"
    )


def _bind_action_to_datablock(datablock, action):
    """
    Safely binds an Action and its appropriate ActionSlot to an ID datablock.
    Fully compatible with Blender 5.x Slotted Actions and legacy Blender versions.
    """
    if datablock is None or action is None:
        return

    if datablock.animation_data is None:
        try:
            datablock.animation_data_create()
        except Exception:
            return

    anim_data = datablock.animation_data
    if anim_data is None:
        return

    # 1. Assign the action to animation_data
    try:
        if anim_data.action != action:
            anim_data.action = action
    except Exception:
        return

    # 2. Assign action_slot (Blender 4.4+ / 5.x)
    if hasattr(anim_data, "action_slot"):
        try:
            suitable = getattr(anim_data, "action_suitable_slots", None)
            if suitable and len(suitable) > 0:
                anim_data.action_slot = suitable[0]
                return
        except Exception:
            pass

        if hasattr(action, "slots") and len(action.slots) > 0:
            target_id_type = getattr(datablock, "id_type", None)
            candidate_slot = None

            for slot in action.slots:
                slot_id_type = getattr(slot, "target_id_type", None)
                if target_id_type and slot_id_type == target_id_type:
                    candidate_slot = slot
                    break
                elif slot_id_type in (None, 'UNSPECIFIED') and candidate_slot is None:
                    candidate_slot = slot

            if candidate_slot is None:
                candidate_slot = action.slots[0]

            try:
                anim_data.action_slot = candidate_slot
            except Exception:
                pass


def get_clock_timing(clock_node, default_clock=None, ancestry=()):
    ref_clock = clock_node or default_clock
    fps = bpy.context.scene.render.fps
    if ref_clock is not None:
        cycle_interval = ref_clock.getFieldAsFloat('cycleInterval', 1.0, ancestry)
        start_time = ref_clock.getFieldAsFloat('startTime', 0.0, ancestry)
        loop = ref_clock.getFieldAsBool('loop', False, ancestry)
    else:
        cycle_interval = 1.0
        start_time = 0.0
        loop = False

    duration = cycle_interval if cycle_interval > 0 else 1.0
    start_frame = 1.0 + start_time * fps
    return duration, start_frame, fps, loop


def translatePositionInterpolator(node, action, ancestry, target_node=None, target_field="", clock_node=None, default_clock=None):
    key = node.getFieldAsArray('key', 0, ancestry)
    key_value = node.getFieldAsArray('keyValue', 3, ancestry)
    if not key or not key_value:
        return

    duration, start_frame, fps, loop = get_clock_timing(clock_node, default_clock, ancestry)
    real_target = target_node.getRealNode() if (target_node and hasattr(target_node, 'getRealNode')) else target_node

    # 1. Target is HAnimJoint (PoseBone)
    if target_node is not None and target_node.getSpec() == 'HAnimJoint':
        bone_name = getattr(target_node, 'blendData', None) or getattr(real_target, 'blendData', None)
        if not bone_name or not isinstance(bone_name, str):
            bone_name = target_node.getFieldAsString('name', 'Joint', ancestry)

        armature_obj = getattr(target_node, 'blendObject', None) or getattr(real_target, 'blendObject', None)
        rest_tx = Vector(target_node.getFieldAsFloatTuple('translation', (0.0, 0.0, 0.0), ancestry))

        loc_x = action_fcurve_ensure(action, f'pose.bones["{bone_name}"].location', 0, datablock=armature_obj)
        loc_y = action_fcurve_ensure(action, f'pose.bones["{bone_name}"].location', 1, datablock=armature_obj)
        loc_z = action_fcurve_ensure(action, f'pose.bones["{bone_name}"].location', 2, datablock=armature_obj)

        for i, frac in enumerate(key):
            if i >= len(key_value):
                break
            x, y, z = key_value[i]
            frame = start_frame + frac * duration * fps
            loc_x.keyframe_points.insert(frame, x - rest_tx.x)
            loc_y.keyframe_points.insert(frame, y - rest_tx.y)
            loc_z.keyframe_points.insert(frame, z - rest_tx.z)

        for fcu in (loc_x, loc_y, loc_z):
            for kf in fcu.keyframe_points:
                kf.interpolation = 'LINEAR'
            fcurve_set_loop(fcu, loop)
        return

    # 2. General Object location
    obj = (getattr(target_node, 'blendObject', None) or getattr(real_target, 'blendObject', None)) if target_node else None
    loc_x = action_fcurve_ensure(action, "location", 0, datablock=obj)
    loc_y = action_fcurve_ensure(action, "location", 1, datablock=obj)
    loc_z = action_fcurve_ensure(action, "location", 2, datablock=obj)

    for i, frac in enumerate(key):
        if i >= len(key_value):
            break
        x, y, z = key_value[i]
        frame = start_frame + frac * duration * fps
        loc_x.keyframe_points.insert(frame, x)
        loc_y.keyframe_points.insert(frame, y)
        loc_z.keyframe_points.insert(frame, z)

    for fcu in (loc_x, loc_y, loc_z):
        for kf in fcu.keyframe_points:
            kf.interpolation = 'LINEAR'
        fcurve_set_loop(fcu, loop)


def translateOrientationInterpolator(node, action, ancestry, target_node=None, target_field="", clock_node=None, default_clock=None):
    key = node.getFieldAsArray('key', 0, ancestry)
    key_value = node.getFieldAsArray('keyValue', 4, ancestry)
    if not key or not key_value:
        return

    duration, start_frame, fps, loop = get_clock_timing(clock_node, default_clock, ancestry)
    real_target = target_node.getRealNode() if (target_node and hasattr(target_node, 'getRealNode')) else target_node

    # 1. Target is HAnimJoint (PoseBone rotation_quaternion)
    if target_node is not None and target_node.getSpec() == 'HAnimJoint':
        bone_name = getattr(target_node, 'blendData', None) or getattr(real_target, 'blendData', None)
        if not bone_name or not isinstance(bone_name, str):
            bone_name = target_node.getFieldAsString('name', 'Joint', ancestry)

        armature_obj = getattr(target_node, 'blendObject', None) or getattr(real_target, 'blendObject', None)
        if armature_obj and bone_name in armature_obj.pose.bones:
            armature_obj.pose.bones[bone_name].rotation_mode = 'QUATERNION'

        rest_rot = target_node.getFieldAsFloatTuple('rotation', (0.0, 0.0, 1.0, 0.0), ancestry)
        rest_axis = Vector(rest_rot[:3])
        rest_quat = (Quaternion(rest_axis.normalized(), rest_rot[3])
                     if rest_axis.length > 1e-6 else Quaternion())

        rot_w = action_fcurve_ensure(action, f'pose.bones["{bone_name}"].rotation_quaternion', 0, datablock=armature_obj)
        rot_x = action_fcurve_ensure(action, f'pose.bones["{bone_name}"].rotation_quaternion', 1, datablock=armature_obj)
        rot_y = action_fcurve_ensure(action, f'pose.bones["{bone_name}"].rotation_quaternion', 2, datablock=armature_obj)
        rot_z = action_fcurve_ensure(action, f'pose.bones["{bone_name}"].rotation_quaternion', 3, datablock=armature_obj)

        for i, frac in enumerate(key):
            if i >= len(key_value):
                break
            ax, ay, az, angle = key_value[i]
            axis = Vector((ax, ay, az))
            quat = Quaternion(axis.normalized(), angle) if axis.length > 1e-6 else Quaternion()
            delta_quat = quat @ rest_quat.inverted()
            frame = start_frame + frac * duration * fps
            rot_w.keyframe_points.insert(frame, delta_quat.w)
            rot_x.keyframe_points.insert(frame, delta_quat.x)
            rot_y.keyframe_points.insert(frame, delta_quat.y)
            rot_z.keyframe_points.insert(frame, delta_quat.z)

        for fcu in (rot_w, rot_x, rot_y, rot_z):
            for kf in fcu.keyframe_points:
                kf.interpolation = 'LINEAR'
            fcurve_set_loop(fcu, loop)
        return

    # 2. General Object rotation
    obj = (getattr(target_node, 'blendObject', None) or getattr(real_target, 'blendObject', None)) if target_node else None
    if obj and obj.rotation_mode == 'QUATERNION':
        rot_w = action_fcurve_ensure(action, "rotation_quaternion", 0, datablock=obj)
        rot_x = action_fcurve_ensure(action, "rotation_quaternion", 1, datablock=obj)
        rot_y = action_fcurve_ensure(action, "rotation_quaternion", 2, datablock=obj)
        rot_z = action_fcurve_ensure(action, "rotation_quaternion", 3, datablock=obj)

        for i, frac in enumerate(key):
            if i >= len(key_value):
                break
            ax, ay, az, angle = key_value[i]
            axis = Vector((ax, ay, az))
            quat = Quaternion(axis.normalized(), angle) if axis.length > 1e-6 else Quaternion()
            frame = start_frame + frac * duration * fps
            rot_w.keyframe_points.insert(frame, quat.w)
            rot_x.keyframe_points.insert(frame, quat.x)
            rot_y.keyframe_points.insert(frame, quat.y)
            rot_z.keyframe_points.insert(frame, quat.z)

        for fcu in (rot_w, rot_x, rot_y, rot_z):
            for kf in fcu.keyframe_points:
                kf.interpolation = 'LINEAR'
            fcurve_set_loop(fcu, loop)
    else:
        rot_x = action_fcurve_ensure(action, "rotation_euler", 0, datablock=obj)
        rot_y = action_fcurve_ensure(action, "rotation_euler", 1, datablock=obj)
        rot_z = action_fcurve_ensure(action, "rotation_euler", 2, datablock=obj)

        for i, frac in enumerate(key):
            if i >= len(key_value):
                break
            mtx = translateRotation(key_value[i])
            eul = mtx.to_euler()
            frame = start_frame + frac * duration * fps
            rot_x.keyframe_points.insert(frame, eul.x)
            rot_y.keyframe_points.insert(frame, eul.y)
            rot_z.keyframe_points.insert(frame, eul.z)

        for fcu in (rot_x, rot_y, rot_z):
            for kf in fcu.keyframe_points:
                kf.interpolation = 'LINEAR'
            fcurve_set_loop(fcu, loop)


def translateScalarInterpolator(node, action, ancestry, target_node=None, target_field="", clock_node=None, default_clock=None):
    key = node.getFieldAsArray('key', 0, ancestry)
    key_value = node.getFieldAsArray('keyValue', 0, ancestry)
    if not key or not key_value:
        return

    duration, start_frame, fps, loop = get_clock_timing(clock_node, default_clock, ancestry)
    real_target = target_node.getRealNode() if (target_node and hasattr(target_node, 'getRealNode')) else target_node

    # 1. Target is HAnimDisplacer (Shape Key value)
    if target_node is not None and (target_node.getSpec() == 'HAnimDisplacer' or target_field in {'weight', 'set_weight'}):
        mesh_obj = getattr(target_node, 'blendObject', None) or getattr(real_target, 'blendObject', None)
        shape_keys = mesh_obj.data.shape_keys if (mesh_obj and mesh_obj.data) else None
        shape_key = getattr(target_node, 'blendData', None) or getattr(real_target, 'blendData', None)

        key_name = shape_key.name if (shape_key and hasattr(shape_key, 'name')) else target_node.getFieldAsString('name', '', ancestry)
        if not key_name:
            key_name = target_node.getDefName() or (real_target.getDefName() if real_target else None) or "Displacer"

        data_path = f'key_blocks["{key_name}"].value'
        fcu = action_fcurve_ensure(action, data_path, 0, datablock=shape_keys)
        for i, frac in enumerate(key):
            if i >= len(key_value):
                break
            frame = start_frame + frac * duration * fps
            fcu.keyframe_points.insert(frame, key_value[i])
        for kf in fcu.keyframe_points:
            kf.interpolation = 'LINEAR'
        fcurve_set_loop(fcu, loop)
        return

    # 2. Target is scale or uniform scale
    if target_field in {'scale', 'set_scale'}:
        obj = (getattr(target_node, 'blendObject', None) or getattr(real_target, 'blendObject', None)) if target_node else None
        sca_x = action_fcurve_ensure(action, "scale", 0, datablock=obj)
        sca_y = action_fcurve_ensure(action, "scale", 1, datablock=obj)
        sca_z = action_fcurve_ensure(action, "scale", 2, datablock=obj)
        for i, frac in enumerate(key):
            if i >= len(key_value):
                break
            val = key_value[i]
            frame = start_frame + frac * duration * fps
            sca_x.keyframe_points.insert(frame, val)
            sca_y.keyframe_points.insert(frame, val)
            sca_z.keyframe_points.insert(frame, val)
        for fcu in (sca_x, sca_y, sca_z):
            for kf in fcu.keyframe_points:
                kf.interpolation = 'LINEAR'
            fcurve_set_loop(fcu, loop)


def translateTimeSensor(node, action, ancestry):
    return


# Maps a Blender ID datablock's id_type to the bpy.data collection that
# holds it, so a tagged Action can be traced back to its target datablock
# after import without keeping a live Python reference around.
_ID_TYPE_COLLECTIONS = {
    'OBJECT': 'objects',
    'ARMATURE': 'armatures',
    'KEY': 'shape_keys',
    'MESH': 'meshes',
}


def _clock_def_name(clock_node, default_clock=None):
    """Best-effort DEF name for the TimeSensor driving an animation, used to
    key/tag Actions so distinct clocks never get merged together."""
    ref = clock_node or default_clock
    if ref is not None and hasattr(ref, 'getDefName'):
        try:
            name = ref.getDefName()
        except Exception:
            name = None
        if name:
            return name
    return "DefaultClock"


def _id_type_name(datablock):
    return getattr(datablock, "id_type", None) or type(datablock).__name__


def _tag_action_target(action, clock_def, target_datablock=None):
    """Stamp an Action with the TimeSensor DEF that drives it and (when known)
    the datablock it is meant to be assigned to, so later UI code (e.g. the
    X3D animation sidebar) can offer it as a selectable, independently
    playable entry without re-parsing the source X3D."""
    action["x3d_timesensor"] = clock_def
    if target_datablock is not None:
        action["x3d_target_id_name"] = getattr(target_datablock, "name", "")
        action["x3d_target_id_type"] = _id_type_name(target_datablock)


def process_all_routes(all_nodes, root_node, bpycollection):
    routeIpoDict = root_node.getRouteIpoDict()
    defDict = root_node.getDefDict()

    def getIpo(act_id):
        try:
            action = routeIpoDict[act_id]
        except KeyError:
            action = routeIpoDict[act_id] = bpy.data.actions.new(act_id)
            action.use_fake_user = True
        return action

    # 1. Collect all ROUTE statements and identify scene default TimeSensors
    raw_routes = []
    default_clock = None

    for node, ancestry in all_nodes:
        if node.getSpec() == 'TimeSensor' and default_clock is None:
            default_clock = node
        if hasattr(node, 'fields'):
            for field in node.fields:
                if field and field[0] == 'ROUTE':
                    raw_routes.append((field, ancestry))

    # 2. Pass 1: map TimeSensor -> Interpolator routes
    interpolator_clocks = {}
    for field, ancestry in raw_routes:
        try:
            from_parts = field[1].split('.')
            to_parts = field[3].split('.')
            from_id = from_parts[0]
            to_id = to_parts[0]
        except Exception:
            continue

        from_node = defDict.get(from_id)
        if from_node and from_node.getSpec() == 'TimeSensor':
            interpolator_clocks[to_id] = from_node

    # Include clocks associated via ProtoInstances (e.g. MenuItem adapter -> Main_Clock)
    mgr = getattr(proto_x3d, 'manager', None)
    adapter_clocks = getattr(mgr, 'adapter_clocks', None) or getattr(proto_x3d, 'adapter_clocks', {})
    for adapter_def, clock_def in adapter_clocks.items():
        clock_node = defDict.get(clock_def) or defDict.get('Main_Clock')
        if clock_node and adapter_def not in interpolator_clocks:
            interpolator_clocks[adapter_def] = clock_node

    # 3. Pass 2: process Interpolator -> Target routes
    for field, ancestry in raw_routes:
        try:
            from_parts = field[1].split('.')
            to_parts = field[3].split('.')
            from_id, from_type = from_parts[0], from_parts[1] if len(from_parts) > 1 else ''
            to_id, to_type = to_parts[0], to_parts[1] if len(to_parts) > 1 else ''
        except Exception:
            logger.warning("Invalid ROUTE %s" % field)
            continue

        from_node = defDict.get(from_id)
        to_node = defDict.get(to_id)
        if not from_node:
            continue

        clock = interpolator_clocks.get(from_id, default_clock)
        clock_def = _clock_def_name(clock, default_clock)

        # Identify target datablock (Mesh ShapeKeys, Armature, or Object)
        target_datablock = None
        if to_node is not None:
            real_to_node = to_node.getRealNode() if hasattr(to_node, 'getRealNode') else to_node
            to_spec = to_node.getSpec()
            if to_spec == 'HAnimDisplacer':
                mesh_obj = getattr(to_node, 'blendObject', None) or getattr(real_to_node, 'blendObject', None)
                if mesh_obj and mesh_obj.data and mesh_obj.data.shape_keys:
                    target_datablock = mesh_obj.data.shape_keys
            elif to_spec == 'HAnimJoint':
                target_datablock = getattr(to_node, 'blendObject', None) or getattr(real_to_node, 'blendObject', None)
            else:
                target_datablock = getattr(to_node, 'blendObject', None) or getattr(real_to_node, 'blendObject', None)

        # Key the Action by (target datablock, driving clock) rather than by
        # target datablock alone, so two distinct TimeSensors animating the
        # same object (e.g. two alternate pose loops on one armature) end up
        # as two separately selectable Actions instead of being merged.
        if target_datablock is not None:
            if target_datablock.animation_data is None:
                target_datablock.animation_data_create()
            action_name = f"{getattr(target_datablock, 'name', from_id)}_{clock_def}"
            action = getIpo(action_name)
            _tag_action_target(action, clock_def, target_datablock)
            _bind_action_to_datablock(target_datablock, action)
        else:
            action = getIpo(from_id)
            _tag_action_target(action, clock_def)

        # Translate Interpolators
        from_spec = from_node.getSpec()
        if from_type in {'value_changed', 'fraction_changed'} or from_spec.endswith('Interpolator'):
            if from_spec == 'PositionInterpolator' or to_type in {'set_position', 'set_translation', 'translation', 'position'}:
                translatePositionInterpolator(from_node, action, ancestry, target_node=to_node, target_field=to_type, clock_node=clock, default_clock=default_clock)

            elif from_spec == 'OrientationInterpolator' or to_type in {'set_orientation', 'set_rotation', 'rotation', 'orientation'}:
                translateOrientationInterpolator(from_node, action, ancestry, target_node=to_node, target_field=to_type, clock_node=clock, default_clock=default_clock)

            elif from_spec == 'ScalarInterpolator' or to_type in {'set_fraction', 'set_scale', 'scale', 'weight', 'set_weight'}:
                translateScalarInterpolator(from_node, action, ancestry, target_node=to_node, target_field=to_type, clock_node=clock, default_clock=default_clock)

        elif from_type == 'bindTime' and to_node:
            translateTimeSensor(to_node, action, ancestry)

        # Ensure slot binding is refreshed now that curves/slots exist
        if target_datablock is not None:
            _bind_action_to_datablock(target_datablock, action)

    # 4. Bind orphan target actions created directly by DEF keys if any
    for key, action in routeIpoDict.items():
        if key not in defDict:
            continue
        node = defDict[key]
        if node.blendObject is None and node.blendData is None:
            if node.getSpec() not in {'HAnimDisplacer', 'HAnimJoint', 'HAnimSegment', 'HAnimSite'}:
                bpyob = node.blendData = node.blendObject = bpy.data.objects.new('AnimOb', None)
                bpycollection.objects.link(bpyob)
                bpyob.select_set(True)
                if action.get("x3d_timesensor") and not action.get("x3d_target_id_name"):
                    _tag_action_target(action, action["x3d_timesensor"], bpyob)
                _bind_action_to_datablock(bpyob, action)


def importRoute(node, ancestry):
    """Backwards-compatibility stub; route processing is handled in process_all_routes."""
    return


# -----------------------------------------------------------------------------------
# Main entry points
# -----------------------------------------------------------------------------------

def load_web3d(
        bpycontext,
        filepath,
        *,
        PREF_FLAT=False,
        PREF_CIRCLE_DIV=16,
        file_unit='M',
        global_scale=1.0,
        global_matrix=None,
        HELPER_FUNC=None,
        as_collection=False,
        solidify=False,
        solidify_value=0.1
):
    global current_file_path, conversion_scale, material_cache
    current_file_path = filepath
    GLOBALS['CIRCLE_DETAIL'] = PREF_CIRCLE_DIV
    conversion_scale = global_scale
    material_cache = {}

    if proto_x3d is not None and getattr(proto_x3d, "manager", None) is not None:
        proto_x3d.manager.reset()
    elif proto_x3d is not None and hasattr(proto_x3d, "reset"):
        proto_x3d.reset()

    if as_collection:
        active_collection = bpy.context.view_layer.active_layer_collection.collection
        bpycollection = bpy.data.collections.new(os.path.basename(filepath))
        active_collection.children.link(bpycollection)
    else:
        bpycollection = bpy.context.view_layer.active_layer_collection.collection

    if filepath.lower().endswith(('.x3d', '.x3dz')):
        root_node, msg = x3d_parse(filepath)
    else:
        root_node, msg = vrml_parse(filepath)

    if not root_node:
        logger.warning(msg)
        return

    if global_matrix is None:
        global_matrix = Matrix()

    all_nodes = root_node.getSerialized([], [])
    hanim_consumed_ids = set()

    for node, ancestry in all_nodes:
        if id(node) in hanim_consumed_ids:
            continue

        # Skip any node inside an HAnimHumanoid subtree; handled by import_humanoid()
        if any(a.getSpec() == 'HAnimHumanoid' for a in ancestry):
            continue

        spec = node.getSpec()
        if HELPER_FUNC and HELPER_FUNC(node, ancestry):
            pass
        if spec == 'Shape':
            importShape(bpycollection, node, ancestry, global_matrix, solidify, solidify_value)
        elif spec in {'PointLight', 'DirectionalLight', 'SpotLight'}:
            importLamp(bpycollection, node, spec, ancestry, global_matrix)
        elif spec == 'Viewpoint':
            importViewpoint(bpycollection, node, ancestry, global_matrix)
        elif spec == 'Transform':
            if not PREF_FLAT:
                importTransform(bpycollection, node, ancestry, global_matrix)
        elif spec == 'HAnimHumanoid':
            hanim_consumed_ids.update(
                hanim_x3d.import_humanoid(bpycollection, node, ancestry,
                                           global_matrix, bpycontext))
        elif spec == 'Sound':
            importAudio(bpycollection, node, ancestry, global_matrix)

    # Process all ROUTE, TimeSensor, and Interpolator animations. This is
    # what tags each resulting Action with the DEF name of the TimeSensor
    # that drives it (see _tag_action_target), so it must run before the
    # HAnim sidebar menu is finalized below.
    process_all_routes(all_nodes, root_node, bpycollection)

    # Now that every X3D-driven Action has been created and tagged, fold in
    # any TimeSensor not already exposed through a MenuItem (e.g. a bare
    # looping clock driving an armature directly) as its own selectable
    # entry in the HAnim sidebar menu.
    finalize_fn = getattr(hanim_x3d, "finalize_animation_menu", None)
    if callable(finalize_fn):
        finalize_fn()

    if PREF_FLAT is False:
        child_dict = {}
        for node, ancestry in all_nodes:
            if node.blendObject:
                blendObject = None
                i = len(ancestry)
                while i:
                    i -= 1
                    blendObject = ancestry[i].blendObject
                    if blendObject:
                        break

                if blendObject:
                    try:
                        child_dict[blendObject].append(node.blendObject)
                    except:
                        child_dict[blendObject] = [node.blendObject]

        for parent, children in child_dict.items():
            for c in children:
                c.parent = parent

        bpycontext.view_layer.update()
        del child_dict


def load_with_profiler(context, filepath, *, global_matrix=None):
    import cProfile
    import pstats
    pro = cProfile.Profile()
    pro.runctx("load_web3d(context, filepath, PREF_FLAT=True, "
               "PREF_CIRCLE_DIV=16, global_matrix=global_matrix)",
               globals(), locals())
    st = pstats.Stats(pro)
    st.sort_stats("time")
    st.print_stats(0.1)


def load(context,
         filepath,
         *,
         files=None,
         directory=None,
         global_scale=1.0,
         global_matrix=None,
         as_collection=False,
         solidify=False,
         solidify_value=0.1
         ):
    paths = [os.path.join(directory, name.name) for name in files] if files else [filepath]

    for file in paths:
        load_web3d(context, file,
                   PREF_FLAT=True,
                   PREF_CIRCLE_DIV=16,
                   global_scale=global_scale,
                   global_matrix=global_matrix,
                   as_collection=as_collection,
                   solidify=solidify,
                   solidify_value=solidify_value)

    return {'FINISHED'}

