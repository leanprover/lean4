/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Std.Sat.CNF.Literal
public import Init.Data.Prod  -- shake: keep (proof instance elab'd in public scope, fix?)
public import Init.Data.Array.Lemmas

@[expose] public section

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
structure CNF (α : Type u) where
  clauses : Array (CNF.Clause α)

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
def eval (a : α → Bool) (f : CNF α) : Bool := f.clauses.all fun c => c.eval a

@[inline]
def empty : CNF α := { clauses := #[] }

@[inline]
def emptyWithCapacity (n : Nat) : CNF α := { clauses := .emptyWithCapacity n }

@[inline]
def add (c : CNF.Clause α) (f : CNF α) : CNF α := { f with clauses := f.clauses.push c }

@[inline]
def append (f1 f2 : CNF α) : CNF α :=
  { clauses := f1.clauses ++ f2.clauses }

instance : Append (CNF α) where
  append := append

@[simp] theorem eval_empty (a : α → Bool) : eval a .empty = true := by simp [eval, empty]
@[simp] theorem eval_add (a : α → Bool) : eval a (f.add c) = (c.eval a && eval a f) := by
  rw [Bool.and_comm]
  simp [add, eval]

@[simp] theorem eval_append (a : α → Bool) (f1 f2 : CNF α) :
    eval a (f1 ++ f2) = (eval a f1 && eval a f2) := Array.all_append

def Sat (a : α → Bool) (f : CNF α) : Prop := eval a f = true
def Unsat (f : CNF α) : Prop := ∀ a, eval a f = false

theorem sat_def (a : α → Bool) (f : CNF α) : Sat a f ↔ (eval a f = true) := by rfl
theorem unsat_def (f : CNF α) : Unsat f ↔ (∀ a, eval a f = false) := by rfl


@[simp] theorem not_unsat_empty : ¬Unsat (.empty : CNF α) :=
  fun h => by simp [unsat_def] at h

@[simp] theorem sat_empty {assign : α → Bool} : Sat assign (.empty : CNF α) := by
  simp [sat_def]

@[simp] theorem unsat_add_nil {g : CNF α} : Unsat (g.add []) := by
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
`Clause` `c` occurs in `CNF` formula `f`.
-/
def Mem (f : CNF α) (c : Clause α) : Prop := c ∈ f.clauses

instance : Membership (Clause α) (CNF α) where
  mem := Mem

instance {c : Clause α} {f : CNF α} [DecidableEq α] : Decidable (c ∈ f) :=
    inferInstanceAs <| Decidable (c ∈ f.clauses)

/--
Variable `v` occurs in `CNF` formula `f`.
-/
def VarMem (v : α) (f : CNF α) : Prop := ∃ c, c ∈ f.clauses ∧ c.Mem v

instance {v : α} {f : CNF α} [DecidableEq α] : Decidable (VarMem v f) :=
  inferInstanceAs <| Decidable (∃ _, _)

theorem Internal.any_not_isEmpty_iff_exists_mem {f : CNF α} :
    (f.clauses.any fun c => !List.isEmpty c) = true ↔ ∃ v, VarMem v f := by
  simp only [Array.any_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, VarMem,
    Clause.Mem]
  constructor
  · intro h
    rcases h with ⟨idx, ⟨hclause1, hclause2⟩⟩
    rcases hclause2 with ⟨lit, hlit⟩
    exists lit.fst, f.clauses[idx]
    constructor
    · simp
    · rcases lit with ⟨_, ⟨_ | _⟩⟩ <;> simp_all
  · intro h
    rcases h with ⟨lit, clause, ⟨hclause1, hclause2⟩⟩
    rw [Array.mem_iff_getElem] at hclause1
    rcases hclause1 with ⟨i, h, hi⟩
    cases hclause2 with
    | inl hl =>
      exists i, h, (lit, false)
      rw [hi]
      assumption
    | inr hr =>
      exists i, h, (lit, true)
      rw [hi]
      assumption

@[no_expose]
instance {f : CNF α} [DecidableEq α] : Decidable (∃ v, VarMem v f) :=
  decidable_of_iff (f.clauses.any fun c => !c.isEmpty) Internal.any_not_isEmpty_iff_exists_mem

theorem not_VarMem_empty {v : α} : ¬VarMem v (.empty : CNF α) := by simp [VarMem, empty]

@[local simp] theorem VarMem_add {v : α} {c} {f : CNF α} :
    VarMem v (f.add c : CNF α) ↔ (Clause.Mem v c ∨ VarMem v f) := by
  simp only [VarMem, add, Array.mem_push]
  constructor
  · intro h
    rcases h with ⟨c, ⟨hc1 | hc1, hc2⟩⟩
    · right
      exists c
    · simp_all
  · intro h
    rcases h with hc1 | ⟨c, hc1, hc2⟩
    · exists c
      simp [hc1]
    · exists c
      simp [hc1, hc2]

theorem VarMem_of (h : c ∈ f) (w : Clause.Mem v c) : VarMem v f := by
  apply Exists.intro c
  constructor <;> assumption

theorem Internal.mem_iff {f : CNF α} : c ∈ f ↔ c ∈ f.clauses := by
  rfl

theorem Internal.clauses_append {f1 f2 : CNF α} : (f1 ++ f2).clauses = f1.clauses ++ f2.clauses := rfl

theorem Internal.ext_iff {f1 f2 : CNF α} : f1 = f2 ↔ f1.clauses = f2.clauses := by
  cases f1; cases f2; simp

@[simp]
theorem emptyWithCapacity_eq_empty (n : Nat) :
    CNF.emptyWithCapacity n = (CNF.empty : CNF α) := by
  simp [empty, emptyWithCapacity]

@[simp] theorem VarMem_append {v : α} {f1 f2 : CNF α} :
    VarMem v (f1 ++ f2) ↔ VarMem v f1 ∨ VarMem v f2 := by
  simp [VarMem, Array.mem_append, Internal.clauses_append]
  constructor
  · rintro ⟨c, (mf1 | mf2), mc⟩
    · left
      exact ⟨c, mf1, mc⟩
    · right
      exact ⟨c, mf2, mc⟩
  · rintro (⟨c, mf1, mc⟩ | ⟨c, mf2, mc⟩)
    · exact ⟨c, Or.inl mf1, mc⟩
    · exact ⟨c, Or.inr mf2, mc⟩

theorem eval_congr (a1 a2 : α → Bool) (f : CNF α) (hw : ∀ v, VarMem v f → a1 v = a2 v) :
    eval a1 f = eval a2 f := by
  rcases f with ⟨clauses⟩
  simp only [eval]
  rw [Bool.eq_iff_iff, Array.all_eq_true, Array.all_eq_true]
  constructor
  · intro h x hx
    rw [Clause.eval_congr a2 a1 clauses[x]]
    · exact h x hx
    · intro i hi
      symm
      exact hw _ (VarMem_of (by simp [Internal.mem_iff]) hi)
  · intro h x hx
    rw [Clause.eval_congr a1 a2 clauses[x]]
    · exact h x hx
    · intro i hi
      exact hw _ (VarMem_of (by simp [Internal.mem_iff]) hi)

end CNF

end Sat
end Std
