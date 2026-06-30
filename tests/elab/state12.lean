/- Enumerable and the Decidable instance may already be in Mathlib -/

class Enumerable (α : Type u) where
  elems    : List α
  complete : ∀ a : α, a ∈ elems

def List.allTrue (p : α → Prop) [(a : α) → Decidable (p a)] : List α → Bool
  | [] => true
  | a :: as => p a && allTrue p as

theorem List.of_allTrue [(a : α) → Decidable (p a)] (hc : allTrue p as) (hin : a ∈ as) : p a := by
  induction as with
  | nil => contradiction
  | cons b bs ih =>
    cases hin with simp [allTrue] at hc
    | head => simp [*]
    | tail _ h => exact ih hc.2 h

theorem List.allTrue_of_forall [(a : α) → Decidable (p a)] (h : ∀ a, p a) : allTrue p as := by
  induction as <;> simp [allTrue, *]

instance [Enumerable α] (p : α → Prop) [(a : α) → Decidable (p a)] : Decidable (∀ a, p a) :=
  have : List.allTrue p Enumerable.elems → (a : α) → p a :=
    fun h a => List.of_allTrue h (Enumerable.complete a)
  decidable_of_decidable_of_iff (Iff.intro this List.allTrue_of_forall)

inductive States | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11
deriving DecidableEq

/- We can add a `deriving` for `Enumerable` in the future. -/
open States in
instance : Enumerable States where
  elems := [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  complete a := by cases a <;> decide

open States
def f : States → States → States
| s0, s0 => s0
| s0, s1 => s0
| s0, s2 => s0
| s0, s3 => s0
| s0, s4 => s0
| s0, s5 => s0
| s0, s6 => s0
| s0, s7 => s0
| s0, s8 => s0
| s0, s9 => s0
| s0, s10 => s0
| s0, s11 => s0
| s1, s0 => s0
| s1, s1 => s0
| s1, s2 => s0
| s1, s3 => s0
| s1, s4 => s0
| s1, s5 => s0
| s1, s6 => s0
| s1, s7 => s0
| s1, s8 => s0
| s1, s9 => s0
| s1, s10 => s0
| s1, s11 => s0
| s2, s0 => s0
| s2, s1 => s0
| s2, s2 => s0
| s2, s3 => s0
| s2, s4 => s0
| s2, s5 => s0
| s2, s6 => s0
| s2, s7 => s0
| s2, s8 => s0
| s2, s9 => s0
| s2, s10 => s0
| s2, s11 => s0
| s3, s0 => s0
| s3, s1 => s0
| s3, s2 => s0
| s3, s3 => s0
| s3, s4 => s0
| s3, s5 => s0
| s3, s6 => s0
| s3, s7 => s0
| s3, s8 => s0
| s3, s9 => s0
| s3, s10 => s0
| s3, s11 => s0
| s4, s0 => s0
| s4, s1 => s0
| s4, s2 => s0
| s4, s3 => s0
| s4, s4 => s0
| s4, s5 => s0
| s4, s6 => s0
| s4, s7 => s0
| s4, s8 => s0
| s4, s9 => s0
| s4, s10 => s0
| s4, s11 => s0
| s5, s0 => s0
| s5, s1 => s0
| s5, s2 => s0
| s5, s3 => s0
| s5, s4 => s0
| s5, s5 => s0
| s5, s6 => s0
| s5, s7 => s0
| s5, s8 => s0
| s5, s9 => s0
| s5, s10 => s0
| s5, s11 => s0
| s6, s0 => s0
| s6, s1 => s0
| s6, s2 => s0
| s6, s3 => s0
| s6, s4 => s0
| s6, s5 => s0
| s6, s6 => s0
| s6, s7 => s0
| s6, s8 => s0
| s6, s9 => s0
| s6, s10 => s0
| s6, s11 => s0
| s7, s0 => s0
| s7, s1 => s0
| s7, s2 => s0
| s7, s3 => s0
| s7, s4 => s0
| s7, s5 => s0
| s7, s6 => s0
| s7, s7 => s0
| s7, s8 => s0
| s7, s9 => s0
| s7, s10 => s0
| s7, s11 => s0
| s8, s0 => s0
| s8, s1 => s0
| s8, s2 => s0
| s8, s3 => s0
| s8, s4 => s0
| s8, s5 => s0
| s8, s6 => s0
| s8, s7 => s0
| s8, s8 => s0
| s8, s9 => s0
| s8, s10 => s0
| s8, s11 => s0
| s9, s0 => s0
| s9, s1 => s0
| s9, s2 => s0
| s9, s3 => s0
| s9, s4 => s0
| s9, s5 => s0
| s9, s6 => s0
| s9, s7 => s0
| s9, s8 => s0
| s9, s9 => s0
| s9, s10 => s0
| s9, s11 => s0
| s10, s0 => s0
| s10, s1 => s0
| s10, s2 => s0
| s10, s3 => s0
| s10, s4 => s0
| s10, s5 => s0
| s10, s6 => s0
| s10, s7 => s0
| s10, s8 => s0
| s10, s9 => s0
| s10, s10 => s0
| s10, s11 => s0
| s11, s0 => s0
| s11, s1 => s0
| s11, s2 => s0
| s11, s3 => s0
| s11, s4 => s0
| s11, s5 => s0
| s11, s6 => s0
| s11, s7 => s0
| s11, s8 => s0
| s11, s9 => s0
| s11, s10 => s0
| s11, s11 => s0

set_option maxHeartbeats 0
example : ∀ x y z, f (f (f s0 x) y) z = f (f x z) (f y z) := by
 native_decide -- This is fast, but the TCB is much bigger
