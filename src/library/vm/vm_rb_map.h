/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
bool is_name_set(vm_obj const & o);
name_set const & to_name_set(vm_obj const & o);
vm_obj to_obj(name_set const & n);

void initialize_vm_rb_map();
void finalize_vm_rb_map();
}
