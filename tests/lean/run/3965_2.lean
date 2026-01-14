section Mathlib.Init.Order.Defs

universe u

variable {α : Type u}

class PartialOrder (α : Type u) extends LE α, LT α where

theorem le_antisymm [PartialOrder α] : ∀ {a b : α}, a ≤ b → b ≤ a → a = b := sorry

end Mathlib.Init.Order.Defs

section Mathlib.Init.Data.Nat.Lemmas

namespace Nat

instance : PartialOrder Nat where
  le := Nat.le
  lt := Nat.lt

section Find

variable {p : Nat → Prop}

private def lbp (m n : Nat) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

private def wf_lbp {p : Nat → Prop} (H : ∃ n, p n) : WellFounded (@lbp p) := sorry

protected noncomputable def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    sorry 0 sorry

protected noncomputable def find {p : Nat → Prop} [DecidablePred p] (H : ∃ n, p n) : Nat :=
  (Nat.findX H).1

protected theorem find_spec : p (Nat.find H) := sorry

protected theorem find_min' {m : Nat} (h : p m) : Nat.find H ≤ m := sorry

end Find

end Nat

end Mathlib.Init.Data.Nat.Lemmas

section Mathlib.Logic.Basic

theorem Exists.fst {b : Prop} {p : b → Prop} : Exists p → b
  | ⟨h, _⟩ => h

end Mathlib.Logic.Basic

section Mathlib.Order.Basic

open Function

def PartialOrder.lift {α β} [PartialOrder β] (f : α → β) : PartialOrder α where
  le x y := f x ≤ f y
  lt x y := f x < f y

end Mathlib.Order.Basic

section Mathlib.Data.Fin.Basic

instance {n : Nat} : PartialOrder (Fin n) :=
  PartialOrder.lift Fin.val

end Mathlib.Data.Fin.Basic

section Mathlib.Data.Fin.Tuple.Basic

universe u v

namespace Fin

variable {n : Nat}

def find : ∀ {n : Nat} (p : Fin n → Prop) [DecidablePred p], Option (Fin n)
  | 0, _p, _ => none
  | n + 1, p, _ => by
    exact
      Option.casesOn (@find n (fun i ↦ p (i.castLT sorry)) _)
        (if _ : p (Fin.last n) then some (Fin.last n) else none) fun i ↦
        some (i.castLT sorry)

theorem nat_find_mem_find {p : Fin n → Prop} [DecidablePred p]
    (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) :
    (⟨Nat.find h, (Nat.find_spec h).fst⟩ : Fin n) ∈ find p := by
  rcases hf : find p with f | f
  · sorry
  · exact Option.some_inj.2 (le_antisymm sorry (Nat.find_min' _ ⟨f.2, sorry⟩))

end Fin

end Mathlib.Data.Fin.Tuple.Basic
