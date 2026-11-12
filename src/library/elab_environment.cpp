/*
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#include "runtime/interrupt.h"
#include "kernel/kernel_exception.h"
#include "library/elab_environment.h"

namespace lean {
extern "C" obj_res lean_elab_environment_to_kernel_env(obj_arg);
environment elab_environment::to_kernel_env() const {
    return environment(lean_elab_environment_to_kernel_env(to_obj_arg()));
}

/* `lean_add_decl`, `lean_add_decl_without_checking`, `lean_elab_add_decl`,
   `lean_elab_add_decl_without_checking` and `lean_kernel_{is_def_eq,whnf,check}` are
   implemented in Lean by the InLean kernel (`src/Lean/Kernel/InLean/AddDecl.lean`). */

/* getBelieverTrustLevel (_ : Unit) : UInt32 */
extern "C" LEAN_EXPORT uint32 lean_internal_get_believer_trust_level(obj_arg) {
   return LEAN_BELIEVER_TRUST_LEVEL;
}
}
