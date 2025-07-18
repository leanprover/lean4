/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
module

prelude
public import Init.NotationExtra
public import Init.Data.Hashable

@[expose] public section

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

def PosFin (n : Nat) := {x : Nat // 0 < x ∧ x < n}

instance : DecidableEq (PosFin n) :=
  inferInstanceAs (DecidableEq {x : Nat // 0 < x ∧ x < n})

instance : CoeOut (PosFin n) Nat where
  coe p := p.val

instance {n} : Hashable (PosFin n) where
  hash p := hash p.val

instance : ToString (PosFin n) where
  toString p := toString p.val

end Internal
end LRAT
end Std.Tactic.BVDecide
