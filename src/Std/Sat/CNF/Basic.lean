/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
prelude
import Init.Data.List.Lemmas
import Std.Sat.CNF.Literal

namespace Std
namespace Sat

/--
A clause in a CNF.

The literal `(i, b)` is satisfied is the assignment to `i` agrees with `b`.
-/
abbrev CNF.Clause (α : Type u) : Type u := List (Literal α)

/--
A CNF formula.

Literals are identified by members of `α`.
-/
abbrev CNF (α : Type u) : Type u := List (CNF.Clause α)

namespace CNF

/--
Evaluating a `Clause` with respect to an assignment `f`.
-/
def Clause.eval (f : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => f i == n

@[simp] theorem Clause.eval_nil (f : α → Bool) : Clause.eval f [] = false := rfl
@[simp] theorem Clause.eval_succ (f : α → Bool) :
    Clause.eval f (i :: c) = (f i.1 == i.2 || Clause.eval f c) := rfl

/--
Evaluating a `CNF` formula with respect to an assignment `f`.
-/
def eval (f : α → Bool) (g : CNF α) : Bool := g.all fun c => c.eval f

@[simp] theorem eval_nil (f : α → Bool) : eval f [] = true := rfl
@[simp] theorem eval_succ (f : α → Bool) : eval f (c :: g) = (c.eval f && eval f g) := rfl

@[simp] theorem eval_append (f : α → Bool) (g h : CNF α) :
    eval f (g ++ h) = (eval f g && eval f h) := List.all_append

instance : HSat α (Clause α) where
  eval assign clause := Clause.eval assign clause

instance : HSat α (CNF α) where
  eval assign cnf := eval assign cnf

@[simp] theorem unsat_nil_iff_false : unsatisfiable α ([] : CNF α) ↔ False :=
  ⟨fun h => by simp [unsatisfiable, (· ⊨ ·)] at h, by simp⟩

@[simp] theorem sat_nil {assign : α → Bool} : assign ⊨ ([] : CNF α) ↔ True := by
  simp [(· ⊨ ·)]

@[simp] theorem unsat_nil_cons {g : CNF α} : unsatisfiable α ([] :: g) ↔ True := by
  simp [unsatisfiable, (· ⊨ ·)]

namespace Clause

/--
Literal `a` occurs in `Clause` `c`.
-/
def mem (a : α) (c : Clause α) : Prop := (a, false) ∈ c ∨ (a, true) ∈ c

instance {a : α} {c : Clause α} [DecidableEq α] : Decidable (mem a c) :=
  inferInstanceAs <| Decidable (_ ∨ _)

@[simp] theorem not_mem_nil {a : α} : mem a ([] : Clause α) ↔ False := by simp [mem]
@[simp] theorem mem_cons {a : α} : mem a (i :: c : Clause α) ↔ (a = i.1 ∨ mem a c) := by
  rcases i with ⟨b, (_|_)⟩
  · simp [mem, or_assoc]
  · simp [mem]
    rw [or_left_comm]

theorem mem_of (h : (a, b) ∈ c) : mem a c := by
  cases b
  · left; exact h
  · right; exact h

theorem eval_congr (f g : α → Bool) (c : Clause α) (w : ∀ i, mem i c → f i = g i) :
    eval f c = eval g c := by
  induction c
  case nil => rfl
  case cons i c ih =>
    simp only [eval_succ]
    rw [ih, w]
    · rcases i with ⟨b, (_|_)⟩ <;> simp [mem]
    · intro j h
      apply w
      rcases h with h | h
      · left
        apply List.mem_cons_of_mem _ h
      · right
        apply List.mem_cons_of_mem _ h

end Clause

/--
Literal `a` occurs in `CNF` formula `g`.
-/
def mem (a : α) (g : CNF α) : Prop := ∃ c, c ∈ g ∧ c.mem a

instance {a : α} {g : CNF α} [DecidableEq α] : Decidable (mem a g) :=
  inferInstanceAs <| Decidable (∃ _, _)

theorem any_nonEmpty_iff_exists_mem {g : CNF α} :
    (List.any g fun c => !List.isEmpty c) = true ↔ ∃ a, mem a g := by
  simp only [List.any_eq_true, Bool.not_eq_true', List.isEmpty_false_iff_exists_mem, mem,
    Clause.mem]
  constructor
  . intro h
    rcases h with ⟨clause, ⟨hclause1, hclause2⟩⟩
    rcases hclause2 with ⟨lit, hlit⟩
    exists lit.fst, clause
    constructor
    . assumption
    . rcases lit with ⟨_, ⟨_ | _⟩⟩ <;> simp_all
  . intro h
    rcases h with ⟨lit, clause, ⟨hclause1, hclause2⟩⟩
    exists clause
    constructor
    . assumption
    . cases hclause2 with
      | inl hl => exact Exists.intro _ hl
      | inr hr => exact Exists.intro _ hr

@[simp] theorem not_mem_cons : (¬ ∃ a, mem a g) ↔ ∃ n, g = List.replicate n [] := by
  simp only [← any_nonEmpty_iff_exists_mem]
  simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and, Bool.not_eq_false]
  induction g with
  | nil =>
    simp only [List.not_mem_nil, List.isEmpty_iff, false_implies, forall_const, true_iff]
    exact ⟨0, rfl⟩
  | cons c g ih =>
    simp_all [ih, List.isEmpty_iff]
    constructor
    · rintro ⟨rfl, n, rfl⟩
      exact ⟨n+1, rfl⟩
    · rintro ⟨n, h⟩
      cases n
      · simp at h
      · simp_all only [List.replicate, List.cons.injEq, true_and]
        exact ⟨_, rfl⟩

instance {g : CNF α} [DecidableEq α] : Decidable (∃ a, mem a g) :=
  decidable_of_iff (g.any fun c => !c.isEmpty) any_nonEmpty_iff_exists_mem

@[simp] theorem not_mem_nil {a : α} : mem a ([] : CNF α) ↔ False := by simp [mem]
@[simp] theorem mem_cons {a : α} {i} {c : CNF α} :
    mem a (i :: c : CNF α) ↔ (Clause.mem a i ∨ mem a c) := by simp [mem]

theorem mem_of (h : c ∈ g) (w : Clause.mem a c) : mem a g := by
  apply Exists.intro c
  constructor <;> assumption

@[simp] theorem mem_append {a : α} {x y : CNF α} : mem a (x ++ y) ↔ mem a x ∨ mem a y := by
  simp [mem, List.mem_append]
  constructor
  · rintro ⟨c, (mx | my), mc⟩
    · left
      exact ⟨c, mx, mc⟩
    · right
      exact ⟨c, my, mc⟩
  · rintro (⟨c, mx, mc⟩ | ⟨c, my, mc⟩)
    · exact ⟨c, Or.inl mx, mc⟩
    · exact ⟨c, Or.inr my, mc⟩

theorem eval_congr (f g : α → Bool) (x : CNF α) (w : ∀ i, mem i x → f i = g i) :
    eval f x = eval g x := by
  induction x
  case nil => rfl
  case cons c x ih =>
    simp only [eval_succ]
    rw [ih, Clause.eval_congr] <;>
    · intro i h
      apply w
      simp [h]

end CNF

end Sat
end Std
