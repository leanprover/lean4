# -*- coding: utf-8 -*-
#
# Copyright (c) 2016 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Authors: Sebastian Ullrich, Gabriel Ebner
#

import gdb
import gdb.printing

def is_scalar(ref):
    return ref['m_obj'].cast(gdb.lookup_type('uintptr_t')) & 1 == 1

def box(n):
    return gdb.Value(n << 1 | 1).cast(gdb.lookup_type('lean::object_ref'))

def unbox(ref):
    return ref['m_obj'].cast(gdb.lookup_type('uintptr_t')) >> 1

def to_cnstr(ref):
    return ref['m_obj'].cast(gdb.lookup_type('lean::constructor_object').pointer())

def get_cnstr_tag(ref):
    return to_cnstr(ref).dereference()['m_tag']

def get_cnstr_obj_arg(ref, i):
    return (ref['m_obj'].cast(gdb.lookup_type('char').pointer()) + gdb.lookup_type('lean::constructor_object').sizeof).cast(gdb.lookup_type('lean::object_ref').pointer())[i]

def get_c_str(ref):
    return (ref['m_obj'].cast(gdb.lookup_type('char').pointer()) + gdb.lookup_type('lean::string_object').sizeof)

class LeanOptionalPrinter:
    """Print a lean::optional object."""

    def __init__(self, val):
        self.val = val

    def get_val(self):
        if hasattr(self.val, 'm_some'):
            if not self.val['m_some']:
                return None
        elif not self.val['m_value'].cast(gdb.lookup_type('char').pointer()):
            return None
        return self.val['m_value']

    def children(self):
        val = self.get_val()
        return [('', val)] if val else []

    def to_string(self):
        return str(self.val.type)

class LeanNamePrinter:
    """Print a lean::name object."""

    def __init__(self, val):
        self.val = val

    def to_string(self):
        def rec(ref):
            prefix = get_cnstr_obj_arg(ref, 0)
            part = get_cnstr_obj_arg(ref, 1)
            s = ("'%s'" % get_c_str(part).string()) if get_cnstr_tag(ref) == 1 else str(unbox(part))
            if not is_scalar(prefix):
                return "%s.%s" % (rec(prefix), s)
            else:
                return s

        if is_scalar(self.val):
            return ""
        else:
            return rec(self.val)

class LeanExprPrinter:
    """Print a lean::expr object."""

    expr_kinds = [
        ('bvar', [('idx', 'nat')]),
        ('fvar', ['name']),
        ('mvar', ['name', ('type', 'expr')]),
        ('sort', ['level']),
        ('const', ['name', ('levels', 'list_ref<lean::level>')]),
        ('app', [('fn', 'expr'), ('arg', 'expr')]),
        ('lam', ['name', ('type', 'expr'), ('body', 'expr')]),
        ('pi', ['name', ('type', 'expr'), ('body', 'expr')]),
        ('let', ['name', ('type', 'expr'), ('val', 'expr'), ('body', 'expr')]),
        ('lit', ['literal']),
        ('mdata', ['kvmap', 'expr']),
        ('proj', ['name', 'nat', 'expr']),
    ]


    def __init__(self, val):
        self.val = val

    def to_string(self):
        return 'lean::expr[{}]'.format(LeanExprPrinter.expr_kinds[get_cnstr_tag(self.val)][0])

    def children(self):
        _, fields = LeanExprPrinter.expr_kinds[get_cnstr_tag(self.val)]
        for i, f in enumerate(fields):
            if isinstance(f, tuple):
                name, typ = f
            else:
                name, typ = f, f
            yield (name, get_cnstr_obj_arg(self.val, i).cast(gdb.lookup_type('lean::' + typ)))

class LeanLevelPrinter:
    """Print a lean::level object."""

    level_kinds = [
        ('lean::level_cell', 'zero', []),
        ('lean::level_succ', 'succ', ['m_l']),
        ('lean::level_max_core', 'max', ['m_lhs', 'm_rhs']),
        ('lean::level_max_core', 'imax', ['m_lhs', 'm_rhs']),
        ('lean::level_param_core', 'param', ['m_id']),
        ('lean::level_param_core', 'meta', ['m_id']),
    ]

    def __init__(self, val):
        self.val = val

    def to_string(self):
        kind = int(self.val['m_ptr']['m_kind'])
        (subtype, name, fields) = LeanLevelPrinter.level_kinds[kind]
        subtype = gdb.lookup_type(subtype)
        val = self.val['m_ptr'].cast(subtype.pointer()).dereference()
        return "({})".format(" ".join([name] + [str(val[field]) for field in fields]))

class LeanListPrinter:
    """Print a lean::list object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        l = self.val
        i = 0
        while l['m_ptr']:
            cell = l['m_ptr'].dereference()
            yield ('[%s]' % i, cell['m_head'])
            l = cell['m_tail']
            i += 1

    def to_string(self):
        return str(self.val.type)

    def display_hint(self):
        return 'array'

class LeanBufferPrinter:
    """Print a lean::buffer object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        p = self.val['m_buffer']
        for i in range(int(self.val['m_pos'])):
            yield ('[%s]' % i, p.dereference())
            p += 1

    def to_string(self):
        return str(self.val.type)

    def display_hint(self):
        return 'array'

class LeanListRefPrinter:
    """Print a lean::list_ref object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        l = self.val
        i = 0
        while not is_scalar(l):
            yield ('[%s]' % i, get_cnstr_obj_arg(l, 0).cast(self.val.type.template_argument(0)))
            l = get_cnstr_obj_arg(l, 1)
            i += 1

    def to_string(self):
        return str(self.val.type)

    def display_hint(self):
        return 'array'

class LeanRBTreePrinter:
    """Print a lean::rb_tree object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        def rec(node):
            if node['m_ptr']:
                cell = node['m_ptr'].dereference()
                for i in rec(cell['m_left']): yield i
                yield ('', cell['m_value'])
                for i in rec(cell['m_right']): yield i
        return rec(self.val['m_root'])

    def to_string(self):
        return 'lean::rb_tree' # full type is way too verbose

    def display_hint(self):
        return 'array'

class LeanRBMapPrinter:
    """Print a lean::rb_map object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        for (_, child) in LeanRBTreePrinter(self.val['m_map']).children():
            yield ('', child['first'])
            yield ('', child['second'])

    def to_string(self):
        return 'lean::rb_map' # full type is way too verbose

    def display_hint(self):
        return 'map'

def build_pretty_printer():
    pp = gdb.printing.RegexpCollectionPrettyPrinter("lean")
    pp.add_printer('optional', '^lean::optional', LeanOptionalPrinter)
    pp.add_printer('name', '^lean::name$', LeanNamePrinter)
    pp.add_printer('expr', '^lean::expr$', LeanExprPrinter)
    #pp.add_printer('level', '^lean::level$', LeanLevelPrinter)
    #pp.add_printer('list', '^lean::list', LeanListPrinter)
    pp.add_printer('buffer', '^lean::buffer', LeanBufferPrinter)
    pp.add_printer('list_ref', '^lean::list_ref', LeanListRefPrinter)
    pp.add_printer('rb_tree', '^lean::rb_tree', LeanRBTreePrinter)
    pp.add_printer('rb_map', '^lean::rb_map', LeanRBMapPrinter)
    return pp

def register():
    gdb.printing.register_pretty_printer(
        gdb.current_objfile(),
        build_pretty_printer(),
        replace=True)

register()
