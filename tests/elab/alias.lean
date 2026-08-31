def Set (α : Type) := α → Prop

def Set.union (s₁ s₂ : Set α) : Set α :=
  fun a => s₁ a ∨ s₂ a

def FinSet (n : Nat) := Set (Fin n)

/-!
The type of `x` is unfolded to find `Set.union`
-/
example (x y : FinSet 10) : FinSet 10 :=
  x.union y

namespace FinSet
export Set (union)
end FinSet

/-!
Since the types are defeq, this alias works:
-/
example (x y : FinSet 10) : FinSet 10 :=
  FinSet.union x y

/-!
However, this dot notation fails since there is no `FinSet` argument.
However, unfolding is the preferred method.
-/
/--
error: Invalid field notation: Function `Set.union` does not have a usable parameter of type `FinSet ...` for which to substitute `x`

Note: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation
-/
#guard_msgs in
example (x y : FinSet 10) : FinSet 10 :=
  x.union y
