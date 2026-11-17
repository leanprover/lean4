/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Joachim Breitner
*/
#pragma once
#include <functional>
#include "util/nat.h"
#include "kernel/environment.h"

namespace lean {
/* Native evaluation of `Lean.KernelVM.run p inputs fuel` (see `src/Init/KernelVM.lean`).
   `e` is an application of `Lean.KernelVM.run` to three arguments and `whnf` is the type
   checker's weak head normalization. Returns `none` if the program is not a closed term built
   from constructors, or the inputs or fuel do not reduce to numerals; the caller then unfolds
   `run` instead. Throws a kernel exception when the program exceeds the resource limits. */
optional<bool> kernel_vm_run(environment const & env, expr const & e,
                             std::function<expr(expr const &)> const & whnf);

/* `Nat.getUInt64 n i`: the 64-bit word at bytes `i` to `i + 7` of `n`, little-endian. */
uint64 nat_get_uint64(nat const & n, nat const & i);

void initialize_kernel_vm();
void finalize_kernel_vm();
}
