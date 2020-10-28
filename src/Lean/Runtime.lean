/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

namespace Lean

@[extern "lean_closure_max_args"]
constant closureMaxArgsFn : Unit → Nat

@[extern "lean_max_small_nat"]
constant maxSmallNatFn : Unit → Nat

def closureMaxArgs : Nat :=
  closureMaxArgsFn ()

def maxSmallNat : Nat :=
  maxSmallNatFn ()

end Lean
