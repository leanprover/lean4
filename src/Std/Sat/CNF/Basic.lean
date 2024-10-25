/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Lemmas
import Init.Data.List.Impl
import Std.Sat.CNF.Literal

namespace Std
namespace Sat

/--
A clause in a CNF.

The literal `(i, b)` is satisfied if the assignment to `i` agrees with `b`.
-/
abbrev CNF.Clause (α : Type u) : Type u := List (Literal α)

/--
A CNF formula.

Literals are identified by members of `α`.
-/
abbrev CNF (α : Type u) : Type u := List (CNF.Clause α)

namespace CNF

/--
Evaluating a `Clause` with respect to an assignment `a`.
-/
def Clause.eval (a : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => a i == n

@[simp] theorem Clause.eval_nil (a : α → Bool) : Clause.eval a [] = false := rfl
@[simp] theorem Clause.eval_cons (a : α → Bool) :
    Clause.eval a (i :: c) = (a i.1 == i.2 || Clause.eval a c) := rfl

/--
Evaluating a `CNF` formula with respect to an assignment `a`.
-/
def eval (a : α → Bool) (f : CNF α) : Bool := f.all fun c => c.eval a

@[simp] theorem eval_nil (a : α → Bool) : eval a [] = true := rfl
@[simp] theorem eval_cons (a : α → Bool) : eval a (c :: f) = (c.eval a && eval a f) := rfl

@[simp] theorem eval_append (a : α → Bool) (f1 f2 : CNF α) :
    eval a (f1 ++ f2) = (eval a f1 && eval a f2) := List.all_append

def Sat (a : α → Bool) (f : CNF α) : Prop := eval a f = true
def Unsat (f : CNF α) : Prop := ∀ a, eval a f = false

theorem sat_def (a : α → Bool) (f : CNF α) : Sat a f ↔ (eval a f = true) := by rfl
theorem unsat_def (f : CNF α) : Unsat f ↔ (∀ a, eval a f = false) := by rfl


@[simp] theorem not_unsat_nil : ¬Unsat ([] : CNF α) :=
  fun h => by simp [unsat_def] at h

@[simp] theorem sat_nil {assign : α → Bool} : Sat assign ([] : CNF α) := by
  simp [sat_def]

@[simp] theorem unsat_nil_cons {g : CNF α} : Unsat ([] :: g) := by
  simp [unsat_def]

namespace Clause

/--
Variable `v` occurs in `Clause` `c`.
-/
def Mem (v : α) (c : Clause α) : Prop := (v, false) ∈ c ∨ (v, true) ∈ c

instance {v : α} {c : Clause α} [DecidableEq α] : Decidable (Mem v c) :=
  inferInstanceAs <| Decidable (_ ∨ _)

@[simp] theorem not_mem_nil {v : α} : ¬Mem v ([] : Clause α) := by simp [Mem]
@[simp] theorem mem_cons {v : α} : Mem v (l :: c : Clause α) ↔ (v = l.1 ∨ Mem v c) := by
  rcases l with ⟨b, (_|_)⟩
  · simp [Mem, or_assoc]
  · simp [Mem]
    rw [or_left_comm]

theorem mem_of (h : (v, p) ∈ c) : Mem v c := by
  cases p
  · left; exact h
  · right; exact h

theorem eval_congr (a1 a2 : α → Bool) (c : Clause α) (hw : ∀ i, Mem i c → a1 i = a2 i) :
    eval a1 c = eval a2 c := by
  induction c
  case nil => rfl
  case cons i c ih =>
    simp only [eval_cons]
    rw [ih, hw]
    · rcases i with ⟨b, (_|_)⟩ <;> simp [Mem]
    · intro j h
      apply hw
      rcases h with h | h
      · left
        apply List.mem_cons_of_mem _ h
      · right
        apply List.mem_cons_of_mem _ h

end Clause

/--
Variable `v` occurs in `CNF` formula `f`.
-/
def Mem (v : α) (f : CNF α) : Prop := ∃ c, c ∈ f ∧ c.Mem v

instance {v : α} {f : CNF α} [DecidableEq α] : Decidable (Mem v f) :=
  inferInstanceAs <| Decidable (∃ _, _)

theorem any_not_isEmpty_iff_exists_mem {f : CNF α} :
    (List.any f fun c => !List.isEmpty c) = true ↔ ∃ v, Mem v f := by
  simp only [List.any_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, Mem,
    Clause.Mem]
  constructor
  · intro h
    rcases h with ⟨clause, ⟨hclause1, hclause2⟩⟩
    rcases hclause2 with ⟨lit, hlit⟩
    exists lit.fst, clause
    constructor
    · assumption
    · rcases lit with ⟨_, ⟨_ | _⟩⟩ <;> simp_all
  · intro h
    rcases h with ⟨lit, clause, ⟨hclause1, hclause2⟩⟩
    exists clause
    constructor
    · assumption
    · cases hclause2 with
      | inl hl => exact Exists.intro _ hl
      | inr hr => exact Exists.intro _ hr

theorem not_exists_mem : (¬ ∃ v, Mem v f) ↔ ∃ n, f = List.replicate n [] := by
  simp only [← any_not_isEmpty_iff_exists_mem]
  simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and, Bool.not_eq_false]
  induction f with
  | nil =>
    simp only [List.not_mem_nil, List.isEmpty_iff, false_implies, forall_const, true_iff]
    exact ⟨0, rfl⟩
  | cons c f ih =>
    simp_all [ih, List.isEmpty_iff]
    constructor
    · rintro ⟨rfl, n, rfl⟩
      exact ⟨n+1, rfl⟩
    · rintro ⟨n, h⟩
      cases n
      · simp at h
      · simp_all only [List.replicate, List.cons.injEq, true_and]
        exact ⟨_, rfl⟩

instance {f : CNF α} [DecidableEq α] : Decidable (∃ v, Mem v f) :=
  decidable_of_iff (f.any fun c => !c.isEmpty) any_not_isEmpty_iff_exists_mem

theorem not_mem_nil {v : α} : ¬Mem v ([] : CNF α) := by simp [Mem]
@[local simp] theorem mem_cons {v : α} {c} {f : CNF α} :
    Mem v (c :: f : CNF α) ↔ (Clause.Mem v c ∨ Mem v f) := by simp [Mem]

theorem mem_of (h : c ∈ f) (w : Clause.Mem v c) : Mem v f := by
  apply Exists.intro c
  constructor <;> assumption

@[simp] theorem mem_append {v : α} {f1 f2 : CNF α} : Mem v (f1 ++ f2) ↔ Mem v f1 ∨ Mem v f2 := by
  simp [Mem, List.mem_append]
  constructor
  · rintro ⟨c, (mf1 | mf2), mc⟩
    · left
      exact ⟨c, mf1, mc⟩
    · right
      exact ⟨c, mf2, mc⟩
  · rintro (⟨c, mf1, mc⟩ | ⟨c, mf2, mc⟩)
    · exact ⟨c, Or.inl mf1, mc⟩
    · exact ⟨c, Or.inr mf2, mc⟩

theorem eval_congr (a1 a2 : α → Bool) (f : CNF α) (hw : ∀ v, Mem v f → a1 v = a2 v) :
    eval a1 f = eval a2 f := by
  induction f
  case nil => rfl
  case cons c x ih =>
    simp only [eval_cons]
    rw [ih, Clause.eval_congr] <;>
    · intro i h
      apply hw
      simp [h]

end CNF

end Sat
end Std
