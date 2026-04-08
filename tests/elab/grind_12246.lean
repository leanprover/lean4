import Std.Do
import Std.Tactic.Do

def Matrix' (α β γ : Type) : Type := α → β → γ

namespace Matrix'

variable {α : Type} {m n : Nat} {M : Matrix' (Fin m) (Fin n) α}
variable {i i' : Fin m} {j j' : Fin n}

def shuffleRows (M : Matrix' (Fin m) (Fin n) α) (j : Fin n) :
    Matrix' (Fin m) (Fin n) α := sorry

def altColSort (M : Matrix' (Fin m) (Fin n) α) :
    Matrix' (Fin m) (Fin n) α := Id.run do
  let mut M' : Matrix' (Fin m) (Fin n) α := M
  for hj : j in [:n] do M' := M'.shuffleRows ⟨j, by sorry⟩
  return M'

open Std.Do

variable [LE α] [Std.IsLinearOrder α]

set_option mvcgen.warning false

def Monotone' {α : Type} [LE α] (f : Fin n → α) : Prop := ∀ i j, i ≤ j → f i ≤ f j

attribute [grind =] Fin.le_def Monotone'

theorem altColSort_rowSorted' (hM : ∀ i, Monotone' (M i)) (i : Fin m) :
    Monotone' (M.altColSort i) := by
  generalize h : M.altColSort = x
  apply Id.of_wp_run_eq h
  mvcgen invariants
  | inv1 => ⇓⟨cur, M'⟩ => ⌜(∀ j : Fin n, j < cur.pos → Monotone' (M' · j))⌝
  case vc2 => grind
  case vc3 => sorry
  case vc1 =>
    fail_if_success grind -verbose
    sorry

end Matrix'
