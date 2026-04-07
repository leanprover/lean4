/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
module

prelude
public import Init.Data.Hashable

@[expose] public section

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

abbrev PosFin (n : Nat) := {x : Nat // 0 < x ∧ x < n}

end Internal
end LRAT
end Std.Tactic.BVDecide
