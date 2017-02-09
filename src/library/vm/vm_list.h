/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/vm/vm.h"

namespace lean {
list<name> to_list_name(vm_obj const & o);
/* Given an object o : list name, store its contents at \c r */
void to_buffer_name(vm_obj const & o, buffer<name> & r);
vm_obj to_obj(buffer<name> const & ls);
vm_obj to_obj(list<name> const & ls);

list<level> to_list_level(vm_obj const & o);
/* Given an object o : list level, store its contents at \c r */
void to_buffer_level(vm_obj const & o, buffer<level> & r);
vm_obj to_obj(buffer<level> const & ls);
vm_obj to_obj(list<level> const & ls);

list<expr> to_list_expr(vm_obj const & o);
/* Given an object o : list expr, store its contents at \c r */
void to_buffer_expr(vm_obj const & o, buffer<expr> & r);
vm_obj to_obj(buffer<expr> const & ls);
vm_obj to_obj(list<expr> const & ls);
vm_obj to_obj(list<list<expr>> const & ls);

template<typename A, typename F>
vm_obj to_vm_list(list<A> const & ls, F const & fn) {
    if (empty(ls)) return mk_vm_simple(0);
    else return mk_vm_constructor(1, fn(head(ls)), to_vm_list(tail(ls), fn));
}

vm_obj to_obj(list<unsigned> const & ls);
vm_obj to_obj(buffer<vm_obj> const & ls);

/* Helper functions for accessing (list A) when A is not expr, name nor level */
inline bool is_nil(vm_obj const & o) { return is_simple(o); }
inline vm_obj head(vm_obj const & o) { lean_assert(!is_nil(o)); return cfield(o, 0); }
inline vm_obj tail(vm_obj const & o) { lean_assert(!is_nil(o)); return cfield(o, 1); }

inline vm_obj mk_vm_nil() { return mk_vm_simple(0); }
inline vm_obj mk_vm_cons(vm_obj const & h, vm_obj const & t) { return mk_vm_constructor(1, h, t); }

template<typename A, typename F>
list<A> to_list(vm_obj const & o, F const & fn) {
    if (is_simple(o)) {
        return list<A>();
    } else if (is_constructor(o)) {
        return list<A>(fn(cfield(o, 0)), to_list<A>(cfield(o, 1), fn));
    } else {
        lean_unreachable();
    }
}

void initialize_vm_list();
void finalize_vm_list();
}
