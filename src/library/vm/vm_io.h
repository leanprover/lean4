/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <vector>
#include "library/vm/vm.h"
#include "library/handle.h"

namespace lean {
/* `(r : α) → (α × real_world)` */
vm_obj mk_io_result(vm_obj const & r);
/* `(st : α × real_world) → α` */
vm_obj get_io_result(vm_obj const & st);
/* `(act : io α) → α` */
vm_obj run_io(vm_obj const & act);
/* `(r : α) → (except ε α × real_world)` */
vm_obj mk_ioe_result(vm_obj const & r);
/* `(e : ε) → (except ε α × real_world)` */
vm_obj mk_ioe_failure(vm_obj const & e);
/* `(s : string) → (except io.error α × real_world)` */
vm_obj mk_ioe_failure(std::string const & s);
/* `ioe` produces a result object, or an error.
   If `o` is a result, then we return the result value. */
optional<vm_obj> is_ioe_result(vm_obj const & o);
/* `ioe` produces a result object, or an error.
   If `o` is an error, then we return the io.error value. */
optional<vm_obj> is_ioe_error(vm_obj const & o);
/* Convert an io.error object into a string */
std::string io_error_to_string(vm_obj const & o);

void initialize_vm_io();
void finalize_vm_io();
}
