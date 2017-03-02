# -*- coding: utf-8 -*-
#
# Copyright (c) 2016 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Authors: Sebastian Ullrich, Gabriel Ebner
#

import gdb
import gdb.printing

class LeanNamePrinter:
    """Print a lean::name object."""

    def __init__(self, val):
        self.val = val

    def to_string(self):
        def rec(imp):
            s = ("'%s'" % imp['m_str'].string()) if imp['m_is_string'] else str(imp['m_k'])
            if imp['m_prefix']:
                return "%s.%s" % (rec(imp['m_prefix'].dereference()), s)
            else:
                return s

        if not self.val['m_ptr']:
            return ""
        else:
            return rec(self.val['m_ptr'].dereference())

class LeanExprPrinter:
    """Print a lean::expr object."""

    expr_kinds = [
        ('lean::expr_var', ['m_vidx']),
        ('lean::expr_sort', ['m_level']),
        ('lean::expr_const', ['m_name', 'm_levels']),
        ('lean::expr_mlocal', ['m_name', 'm_type']),
        ('lean::expr_local', ['m_pp_name', 'm_name', 'm_bi', 'm_type']),
        ('lean::expr_app', ['m_fn', 'm_arg']),
        ('lean::expr_binding', ['m_binder', 'm_body']),
        ('lean::expr_binding', ['m_binder', 'm_body']),
        ('lean::expr_let', ['m_name', 'm_type', 'm_value', 'm_body']),
        ('lean::expr_macro', ['m_definition']),
    ]


    def __init__(self, val):
        self.kind = int(val['m_ptr']['m_kind'])
        subtype = gdb.lookup_type(LeanExprPrinter.expr_kinds[self.kind][0])
        self.val = val['m_ptr'].cast(subtype.pointer()).dereference()

    def to_string(self):
        return str(self.val.type)

    def children(self):
        for f in LeanExprPrinter.expr_kinds[self.kind][1]:
            yield (f, self.val[f])
        if self.kind == 'lean::expr_macro':
            p = self.val.cast(gdb.lookup_type('char').pointer())
            p += gdb.lookup_type('lean::expr_macro').sizeof
            p = p.cast(gdb.lookup_type('lean::expr').pointer())
            for i in range(self.val['m_num_args']):
                yield (p + i).dereference()

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
    pp.add_printer('name', '^lean::name$', LeanNamePrinter)
    pp.add_printer('expr', '^lean::expr$', LeanExprPrinter)
    pp.add_printer('list', '^lean::list', LeanListPrinter)
    pp.add_printer('buffer', '^lean::buffer', LeanBufferPrinter)
    pp.add_printer('rb_tree', '^lean::rb_tree', LeanRBTreePrinter)
    pp.add_printer('rb_map', '^lean::rb_map', LeanRBMapPrinter)
    return pp

def register():
    gdb.printing.register_pretty_printer(
        gdb.current_objfile(),
        build_pretty_printer(),
        replace=True)

register()
