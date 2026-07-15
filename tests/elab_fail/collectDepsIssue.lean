

variable {α : Type} in
def f (a : α) : List α :=
_

variable (P : List Nat → List Nat → Prop) in
theorem foo (xs : List Nat) : (ns : List Nat) → P xs ns
| []      => sorry
| (n::ns) => by {
  cases xs;
  exact sorry;
  exact sorry
}
