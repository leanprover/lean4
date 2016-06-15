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

/* Helper functions for accessing (list A) when A is not expr, name nor level */
inline bool is_nil(vm_obj const & o) { return is_simple(o); }
inline vm_obj head(vm_obj const & o) { lean_assert(!is_nil(o)); return cfield(o, 0); }
inline vm_obj tail(vm_obj const & o) { lean_assert(!is_nil(o)); return cfield(o, 1); }



void initialize_vm_list();
void finalize_vm_list();
}
