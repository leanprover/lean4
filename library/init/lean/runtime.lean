/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core

namespace Lean

@[extern "lean_closure_max_args"]
constant closureMaxArgsFn : Unit → Nat := default _

def closureMaxArgs : Nat :=
closureMaxArgsFn ()

end Lean
