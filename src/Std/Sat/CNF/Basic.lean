/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Literal
public import Init.Data.Prod  -- shake: keep (proof instance elab'd in public scope, fix?)
public import Init.Data.Array.Lemmas
import Init.Data.Array.Bootstrap
import Init.ByCases

@[expose] public section

namespace Std
namespace Sat

/--
A clause in a CNF.

The literal `(i, b)` is satisfied if the assignment to `i` agrees with `b`.
-/
structure CNF.Clause (α : Type u) where
  literals : List (Literal α)
  deriving DecidableEq, Inhabited

/--
A CNF formula.

Literals are identified by members of `α`.
-/
structure CNF (α : Type u) where
  clauses : Array (CNF.Clause α)

namespace CNF

namespace Clause

@[inline]
def empty : Clause α := ⟨[]⟩

@[inline]
def add (c : Clause α) (atom : α) (pol : Bool) : Clause α :=
  { c with literals := (atom, pol) :: c.literals }

@[simp]
theorem add_ne_empty (c : Clause α) (atom : α) (pol : Bool) : c.add atom pol ≠ empty := by
  simp [empty, add]

/--
Evaluating a `Clause` with respect to an assignment `a`.
-/
def eval (a : α → Bool) (c : Clause α) : Bool := c.literals.any fun (i, n) => a i == n

@[simp] theorem eval_empty (a : α → Bool) : Clause.eval a .empty = false := rfl
@[simp] theorem eval_add (a : α → Bool) :
    Clause.eval a (c.add atom pol) = (a atom == pol || Clause.eval a c) := rfl

instance : Membership (Literal α) (Clause α) where
  mem clause lit := lit ∈ clause.literals

instance [Monad m] : ForIn' m (Clause α) (Literal α) inferInstance where
  forIn' clause b f := forIn' clause.literals b f

theorem mem_literals_iff {c : Clause α} {l : Literal α} : l ∈ c.literals ↔ l ∈ c := Iff.rfl

@[simp]
theorem not_mem_empty {l : Literal α} : l ∉ (empty : Clause α) := by
  simp [← mem_literals_iff, empty]

@[simp]
theorem mem_add {c : Clause α} {l1 : Literal α} : l1 ∈ c.add atom pol ↔ l1 = (atom, pol) ∨ l1 ∈ c := by
  simp [← mem_literals_iff, add]

theorem forIn'_eq_forIn'_literals [Monad m] {c : Clause α} {init : β}
    {f : (l : Literal α) → l ∈ c → β → m (ForInStep β)} :
    forIn' c init f = forIn' c.literals init (fun l h b => f l (mem_literals_iff.mp h) b) :=
  rfl

def Sat (a : α → Bool) (f : Clause α) : Prop := eval a f = true
def Unsat (f : Clause α) : Prop := ∀ a, eval a f = false

theorem sat_def (a : α → Bool) (f : Clause α) : Sat a f ↔ (eval a f = true) := by rfl
theorem unsat_def (f : Clause α) : Unsat f ↔ (∀ a, eval a f = false) := by rfl

@[simp] theorem unsat_empty : Unsat (.empty : Clause α) := by
  simp [unsat_def]

@[simp] theorem not_sat_empty {a : α → Bool} : ¬ Sat a (.empty : Clause α) := by
  simp [sat_def]

@[simp] theorem sat_add {a : α → Bool} {c : Clause α} :
    Sat a (c.add atom pol) ↔ a atom = pol ∨ Sat a c := by
  simp [sat_def]

theorem unsat_iff_not_sat {c : Clause α} : Unsat c ↔ ∀ a, ¬Sat a c := by
  rw [unsat_def]
  constructor
  · intro h1 a h2
    rw [sat_def] at h2
    simp_all
  · intro h1 a
    specialize h1 a
    rw [sat_def] at h1
    simp_all

theorem sat_iff_exists_mem_eq {c : Clause α} :
    Sat a c ↔ (∃ lit ∈ c, a lit.1 = lit.2) := by
  simp [sat_def, Membership.mem, eval]

theorem sat_of_mem_of_eq {c : Clause α} {lit : Literal α} (h1 : lit ∈ c) (h2 : a lit.1 = lit.2) :
    Sat a c :=
  sat_iff_exists_mem_eq.mpr ⟨lit, h1, h2⟩

theorem not_sat_iff_forall_mem_ne {c : Clause α} :
    (¬ Sat a c) ↔ (∀ lit ∈ c, a lit.1 ≠ lit.2) := by
  rw [sat_iff_exists_mem_eq]
  simp only [not_exists, not_and, ne_eq]

theorem sat_of_mem_of_mem_neg {c : Clause α} {atom : α} (h1 : (atom, pol) ∈ c)
    (h2 : (atom, !pol) ∈ c) : ∀ a, Sat a c := by
  intro a
  rw [sat_iff_exists_mem_eq]
  by_cases h3 : a atom = pol
  · exists (atom, pol)
  · exists (atom, !pol)
    cases pol <;> simp_all

open Classical in
theorem unsat_iff_eq_empty {c : Clause α} : Unsat c ↔ c = .empty := by
  constructor
  · intro h
    rcases c with ⟨_ | ⟨lit, lits⟩⟩
    · rfl
    · exfalso
      have hmem : lit ∈ (⟨lit :: lits⟩ : Clause α) := by simp [← mem_literals_iff]
      have hsat := sat_of_mem_of_eq (a := fun v => if v = lit.1 then lit.2 else true) hmem (by simp)
      exact unsat_iff_not_sat.mp h _ hsat
  · rintro rfl
    exact unsat_empty

end Clause

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

@[simp]
theorem sat_add {assign : α → Bool} {f : CNF α} :
    Sat assign (f.add c : CNF α) ↔ (Clause.Sat assign c ∧ Sat assign f) := by
  simp [sat_def, Clause.sat_def]

@[simp]
theorem sat_append {assign : α → Bool} :
    Sat assign (f1 ++ f2 : CNF α) ↔ (Sat assign f1 ∧ Sat assign f2) := by
  simp [sat_def]

@[simp] theorem unsat_add_empty {g : CNF α} : Unsat (g.add .empty) := by
  simp [unsat_def]

theorem unsat_iff_not_sat {f : CNF α} : Unsat f ↔ ∀ a, ¬Sat a f := by
  rw [unsat_def]
  constructor
  · intro h1 a h2
    rw [sat_def] at h2
    simp_all
  · intro h1 a
    specialize h1 a
    rw [sat_def] at h1
    simp_all

namespace Clause

/--
Variable `v` occurs in `Clause` `c`.
-/
def VarMem (v : α) (c : Clause α) : Prop := (v, false) ∈ c.literals ∨ (v, true) ∈ c.literals

instance {v : α} {c : Clause α} [DecidableEq α] : Decidable (VarMem v c) :=
  inferInstanceAs <| Decidable (_ ∨ _)

@[simp] theorem not_VarMem_empty {v : α} : ¬VarMem v .empty := by simp [VarMem, empty]

theorem VarMem_add_self {c : Clause α} : VarMem atom (c.add atom pol) := by
  cases pol <;> simp [VarMem, add]

theorem VarMem_add_ne_self {c : Clause α} {atom1 atom2 : α} (h : atom1 ≠ atom2) :
    VarMem atom1 (c.add atom2 pol) ↔ VarMem atom1 c := by
  simp [VarMem, add, h]

@[simp] theorem VarMem_add {v : α} : VarMem v (c.add atom pol) ↔ (v = atom ∨ VarMem v c) := by
  by_cases h : v = atom
  · simp [VarMem_add_self, h]
  · simp [VarMem_add_ne_self, h]

@[elab_as_elim]
theorem induct {motive : Clause α → Prop} (empty : motive .empty)
    (add : (c : Clause α) → (atom : α) → (pol : Bool) → motive c → motive (c.add atom pol))
    (c : Clause α) : motive c := by
  rcases c with ⟨ls⟩
  induction ls with
  | nil => exact empty
  | cons l ls ih =>
    specialize add ⟨ls⟩ l.1 l.2 ih
    exact add

theorem eval_congr (a1 a2 : α → Bool) (c : Clause α) (hw : ∀ i, VarMem i c → a1 i = a2 i) :
    eval a1 c = eval a2 c := by
  induction c using induct with
  | empty => simp
  | add c atom pol ih =>
    simp
    rw [ih, hw]
    · simp
    · intro i hm
      apply hw
      simp [hm]

end Clause

/--
`Clause` `c` occurs in `CNF` formula `f`.
-/
def Mem (f : CNF α) (c : Clause α) : Prop := c ∈ f.clauses

instance : Membership (Clause α) (CNF α) where
  mem := Mem

instance {c : Clause α} {f : CNF α} [DecidableEq α] : Decidable (c ∈ f) :=
    inferInstanceAs <| Decidable (c ∈ f.clauses)

theorem Internal.mem_iff {f : CNF α} : c ∈ f ↔ c ∈ f.clauses := by
  rfl

theorem Internal.clauses_append {f1 f2 : CNF α} : (f1 ++ f2).clauses = f1.clauses ++ f2.clauses := rfl

@[simp]
theorem not_mem_empty {c : Clause α} : c ∉ (empty : CNF α) := by
  simp [Internal.mem_iff, empty]

@[simp]
theorem mem_add {f : CNF α} {c1 c2 : Clause α} : c1 ∈ f.add c2 ↔ c1 = c2 ∨ c1 ∈ f := by
  simp [Internal.mem_iff, add, or_comm]

@[simp]
theorem mem_append {f1 f2 : CNF α} {c : Clause α} : c ∈ (f1 ++ f2) ↔ c ∈ f1 ∨ c ∈ f2 := by
  simp [Internal.mem_iff, Internal.clauses_append]

theorem sat_iff_all_mem_sat {f : CNF α} {a : α → Bool} : Sat a f ↔ ∀ c ∈ f, Clause.Sat a c := by
  simp only [sat_def, Clause.sat_def, eval]
  rw [Array.all_eq_true_iff_forall_mem]
  rfl

theorem sat_of_mem {f : CNF α} (h1 : Sat a f) (h2 : c ∈ f) : Clause.Sat a c :=
  sat_iff_all_mem_sat.mp h1 c h2

theorem not_sat_iff_exists_mem_not_sat {f : CNF α} :
    (¬Sat a f) ↔ (∃ c ∈ f, ¬Clause.Sat a c) := by
  simp only [sat_def, Clause.sat_def, eval, Bool.not_eq_true, Array.all_eq_false',
    Internal.mem_iff]

theorem unsat_of_mem_unsat {f : CNF α} (h1 : c ∈ f) (h2 : Clause.Unsat c) : Unsat f := by
  rw [unsat_iff_not_sat]
  intro a hsat
  exact Clause.unsat_iff_not_sat.mp h2 a (sat_of_mem hsat h1)

theorem unsat_add_of_clause_unsat {f : CNF α} (h : Clause.Unsat c) : Unsat (f.add c) :=
  unsat_of_mem_unsat (by simp) h

theorem unsat_add_of_unsat {f : CNF α} (h : Unsat f) : Unsat (f.add c) := by
  rw [unsat_iff_not_sat] at h ⊢
  intro a hsat
  exact h a (sat_add.mp hsat).right

theorem unsat_append_left {f1 f2 : CNF α} (h : Unsat f1) : Unsat (f1 ++ f2) := by
  rw [unsat_iff_not_sat] at h ⊢
  intro a hsat
  exact h a (sat_append.mp hsat).left

theorem unsat_append_right {f1 f2 : CNF α} (h : Unsat f2) : Unsat (f1 ++ f2) := by
  rw [unsat_iff_not_sat] at h ⊢
  intro a hsat
  exact h a (sat_append.mp hsat).right

/--
Variable `v` occurs in `CNF` formula `f`.
-/
def VarMem (v : α) (f : CNF α) : Prop := ∃ c, c ∈ f.clauses ∧ c.VarMem v

instance {v : α} {f : CNF α} [DecidableEq α] : Decidable (VarMem v f) :=
  inferInstanceAs <| Decidable (∃ _, _)

theorem Internal.any_not_isEmpty_iff_exists_mem {f : CNF α} :
    (f.clauses.any fun c => !List.isEmpty c.literals) = true ↔ ∃ v, VarMem v f := by
  simp only [Array.any_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, VarMem,
    Clause.VarMem]
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
  decidable_of_iff (f.clauses.any fun c => !c.literals.isEmpty) Internal.any_not_isEmpty_iff_exists_mem

theorem not_VarMem_empty {v : α} : ¬VarMem v (.empty : CNF α) := by simp [VarMem, empty]

@[local simp] theorem VarMem_add {v : α} {c} {f : CNF α} :
    VarMem v (f.add c : CNF α) ↔ (Clause.VarMem v c ∨ VarMem v f) := by
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

theorem VarMem_of (h : c ∈ f) (w : Clause.VarMem v c) : VarMem v f := by
  apply Exists.intro c
  constructor <;> assumption

theorem Internal.ext_iff {f1 f2 : CNF α} : f1 = f2 ↔ f1.clauses = f2.clauses := by
  cases f1; cases f2; simp

@[simp]
theorem append_empty {f : CNF α} : f ++ (empty : CNF α) = f := by
  rw [Internal.ext_iff, Internal.clauses_append]
  simp [empty]

@[simp]
theorem empty_append {f : CNF α} : (empty : CNF α) ++ f = f := by
  rw [Internal.ext_iff, Internal.clauses_append]
  simp [empty]

@[simp]
theorem append_assoc {f1 f2 f3 : CNF α} : (f1 ++ f2) ++ f3 = f1 ++ (f2 ++ f3) := by
  simp [Internal.ext_iff, Internal.clauses_append, Array.append_assoc]

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
