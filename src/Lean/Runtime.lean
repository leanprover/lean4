/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Prelude

namespace Lean

@[extern "lean_closure_max_args"]
opaque closureMaxArgsFn : Unit → Nat

@[extern "lean_max_small_nat"]
opaque maxSmallNatFn : Unit → Nat

@[extern "lean_libuv_version"]
opaque libUVVersionFn : Unit → Nat

def closureMaxArgs : Nat :=
  closureMaxArgsFn ()

def maxSmallNat : Nat :=
  maxSmallNatFn ()

def libUVVersion : Nat :=
  libUVVersionFn ()

end Lean
