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
import Init.Data.List.Range
import Init.Data.List.Nat.Range
import Init.Data.ByteArray.Lemmas
import Init.Data.List.Sublist
import Init.Data.List.TakeDrop
import Init.Omega
import Init.ByCases

@[expose] public section

namespace Std
namespace Sat

/--
A clause in a CNF.

The literal `(i, b)` is satisfied if the assignment to `i` agrees with `b`.
-/
structure CNF.Clause (α : Type u) where
  atoms : Array α
  polarities : ByteArray
  size_polarities : polarities.size = atoms.size
  isBool_polarities : ∀ (i : Nat) (h : i < polarities.size), polarities[i] = 0 ∨ polarities[i] = 1

/--
A CNF formula.

Literals are identified by members of `α`.
-/
structure CNF (α : Type u) where
  clauses : Array (CNF.Clause α)

namespace CNF

namespace Clause

instance [DecidableEq α] : DecidableEq (Clause α) := fun c1 c2 =>
  if h : c1.atoms = c2.atoms ∧ c1.polarities = c2.polarities then
    isTrue <| by cases c1; cases c2; obtain ⟨rfl, rfl⟩ := h; rfl
  else
    isFalse <| by rintro rfl; simp at h

@[inline]
def empty : Clause α where
  atoms := #[]
  polarities := .empty
  size_polarities := by simp [ByteArray.size_empty]
  isBool_polarities := by intro i h; simp [ByteArray.size_empty] at h

instance : Inhabited (Clause α) := ⟨empty⟩

@[inline]
def add (c : Clause α) (atom : α) (pol : Bool) : Clause α where
  atoms := c.atoms.push atom
  polarities := c.polarities.push (if pol then 1 else 0)
  size_polarities := by rw [ByteArray.size_push, Array.size_push, c.size_polarities]
  isBool_polarities := by
    intro i h
    simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_push, Array.getElem_push]
    split
    · next h' =>
      have := c.isBool_polarities i (by simpa using h')
      simpa [ByteArray.getElem_eq_getElem_data] using this
    · cases pol <;> simp

@[simp]
theorem add_ne_empty (c : Clause α) (atom : α) (pol : Bool) : c.add atom pol ≠ empty := by
  simp [empty, add]

/--
The polarity of the literal at index `i` of `c`; `false` if `i` is out of bounds.
-/
def polarity (c : Clause α) (i : Nat) : Bool :=
  if h : i < c.polarities.size then c.polarities[i] == 1 else false

theorem polarity_eq_data {c : Clause α} {i : Nat} :
    c.polarity i = (c.polarities.data[i]?.getD 0 == 1) := by
  rw [polarity]
  split
  · next h =>
    rw [Array.getElem?_eq_getElem (by simp only [ByteArray.size_data]; exact h),
      Option.getD_some, ByteArray.getElem_eq_getElem_data]
  · next h =>
    rw [Array.getElem?_eq_none (by simp only [ByteArray.size_data]; omega), Option.getD_none]
    rfl

@[simp]
theorem atoms_add {c : Clause α} : (c.add atom pol).atoms = c.atoms.push atom := rfl

theorem polarity_add {c : Clause α} {i : Nat} :
    (c.add atom pol).polarity i = if i = c.atoms.size then pol else c.polarity i := by
  have hsize : c.polarities.data.size = c.atoms.size := by simp [c.size_polarities]
  simp only [polarity_eq_data, add, ByteArray.data_push, Array.getElem?_push, hsize]
  by_cases h : i = c.atoms.size
  · subst h
    cases pol <;> simp
  · simp [h]

/--
The literals of a `Clause` as a list of atom/polarity pairs, used to state specifications.
-/
def literals (c : Clause α) : List (Literal α) :=
  c.atoms.toList.zipIdx.map fun (x, i) => (x, c.polarity i)

@[simp]
theorem literals_empty : (empty : Clause α).literals = [] := rfl

@[simp]
theorem literals_add {c : Clause α} :
    (c.add atom pol).literals = c.literals ++ [(atom, pol)] := by
  simp only [literals, atoms_add, Array.toList_push, List.zipIdx_append, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro ⟨x, i⟩ h
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp h)
    have hne : i ≠ c.atoms.size := Nat.ne_of_lt (by simpa using hi)
    simp [polarity_add, hne]
  · simp [polarity_add]

theorem length_literals {c : Clause α} : c.literals.length = c.atoms.size := by
  simp [literals]

theorem map_fst_literals {c : Clause α} : c.literals.map Prod.fst = c.atoms.toList := by
  simp only [literals, List.map_map]
  exact List.zipIdx_map_fst 0 c.atoms.toList

theorem getElem_literals {c : Clause α} {i : Nat} (h : i < c.literals.length) :
    c.literals[i] = (c.atoms[i]'(by simpa [length_literals] using h), c.polarity i) := by
  simp [literals, List.getElem_zipIdx]

protected theorem ext {c1 c2 : Clause α} (h : c1.literals = c2.literals) : c1 = c2 := by
  rcases c1 with ⟨a1, p1, hs1, hb1⟩
  rcases c2 with ⟨a2, p2, hs2, hb2⟩
  obtain rfl : a1 = a2 := by
    have h1 := congrArg (List.map Prod.fst) h
    rw [map_fst_literals, map_fst_literals] at h1
    exact Array.toList_inj.mp h1
  suffices hp : p1 = p2 by cases hp; rfl
  apply ByteArray.ext_getElem (by rw [hs1, hs2])
  intro i hi hi'
  have hl : i < (⟨a1, p1, hs1, hb1⟩ : Clause α).literals.length := by
    rw [length_literals]
    exact hs1 ▸ hi
  have hget := List.getElem_of_eq h hl
  rw [getElem_literals, getElem_literals] at hget
  have hpol := congrArg Prod.snd hget
  simp only [polarity_eq_data] at hpol
  rw [Array.getElem?_eq_getElem (by simpa using hi), Array.getElem?_eq_getElem (by simpa using hi'),
    Option.getD_some, Option.getD_some] at hpol
  have h1 := hb1 i hi
  have h2 := hb2 i hi'
  simp only [ByteArray.getElem_eq_getElem_data] at h1 h2 ⊢
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/--
Build a `Clause` from a list of literals.
-/
def ofLiterals (l : List (Literal α)) : Clause α :=
  l.foldl (fun c (atom, pol) => c.add atom pol) empty

theorem literals_foldl_add {l : List (Literal α)} {init : Clause α} :
    (l.foldl (fun c (atom, pol) => c.add atom pol) init).literals = init.literals ++ l := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    rcases x with ⟨atom, pol⟩
    simp [ih]

@[simp]
theorem literals_ofLiterals {l : List (Literal α)} : (ofLiterals l).literals = l := by
  simp [ofLiterals, literals_foldl_add]

@[simp]
theorem ofLiterals_literals {c : Clause α} : ofLiterals c.literals = c :=
  Clause.ext literals_ofLiterals

@[simp]
theorem literals_eq_nil_iff {c : Clause α} : c.literals = [] ↔ c = empty := by
  constructor
  · intro h
    exact Clause.ext (h.trans literals_empty.symm)
  · rintro rfl
    rfl

theorem exists_eq_add_of_ne_empty {c : Clause α} (h : c ≠ empty) :
    ∃ (c' : Clause α) (atom : α) (pol : Bool), c = c'.add atom pol := by
  have hne : c.literals ≠ [] := by simp [h]
  refine ⟨ofLiterals c.literals.dropLast, (c.literals.getLast hne).1,
    (c.literals.getLast hne).2, ?_⟩
  apply Clause.ext
  simp [List.dropLast_concat_getLast hne]

/--
Evaluating a `Clause` with respect to an assignment `a`.
-/
def eval (a : α → Bool) (c : Clause α) : Bool := c.literals.any fun (i, n) => a i == n

@[simp] theorem eval_empty (a : α → Bool) : Clause.eval a .empty = false := rfl
@[simp] theorem eval_add (a : α → Bool) :
    Clause.eval a (c.add atom pol) = (a atom == pol || Clause.eval a c) := by
  simp [eval, Bool.or_comm]

instance : Membership (Literal α) (Clause α) where
  mem clause lit := lit ∈ clause.literals

theorem mem_literals_iff {c : Clause α} {l : Literal α} : l ∈ c.literals ↔ l ∈ c := Iff.rfl

theorem getElem_mem {c : Clause α} {i : Nat} (h : i < c.atoms.size) :
    (c.atoms[i], c.polarity i) ∈ c := by
  rw [← mem_literals_iff]
  have hl : i < c.literals.length := by simpa [length_literals] using h
  rw [← getElem_literals hl]
  exact List.getElem_mem hl

/-- See comment at `Array.forIn'Unsafe`. -/
@[inline]
unsafe def forIn'ImplUnsafe [Monad m] (c : Clause α) (b : β)
    (f : (l : Literal α) → l ∈ c → β → m (ForInStep β)) : m β :=
  let sz := c.atoms.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      match ← f (c.atoms.uget i lcProof, c.polarities.uget i lcProof == 1) lcProof b with
      | .done b => pure b
      | .yield b => loop (i + 1) b
    else
      pure b
  loop 0 b

/-- Reference implementation for `forIn'` on `Clause`, iterating directly over the packed
representation without materializing `literals`. -/
@[implemented_by forIn'ImplUnsafe]
def forIn'Impl [Monad m] (c : Clause α) (b : β)
    (f : (l : Literal α) → l ∈ c → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ c.atoms.size) (b : β) : m β := do
    match i, h with
    | 0, _ => pure b
    | i + 1, h =>
      have h' : c.atoms.size - 1 - i < c.atoms.size := by omega
      match ← f (c.atoms[c.atoms.size - 1 - i], c.polarity (c.atoms.size - 1 - i))
          (getElem_mem h') b with
      | .done b => pure b
      | .yield b => loop i (by omega) b
  loop c.atoms.size (Nat.le_refl _) b

instance [Monad m] : ForIn' m (Clause α) (Literal α) inferInstance where
  forIn' := forIn'Impl

@[simp]
theorem not_mem_empty {l : Literal α} : l ∉ (empty : Clause α) := by
  simp [← mem_literals_iff]

@[simp]
theorem mem_add {c : Clause α} {l1 : Literal α} : l1 ∈ c.add atom pol ↔ l1 = (atom, pol) ∨ l1 ∈ c := by
  simp [← mem_literals_iff, or_comm]

private theorem forIn'Impl_loop_eq_forIn'_drop [Monad m] {c : Clause α}
    {f : (l : Literal α) → l ∈ c → β → m (ForInStep β)} (i : Nat) (h : i ≤ c.atoms.size)
    (b : β) :
    forIn'Impl.loop c f i h b =
      forIn' (c.literals.drop (c.atoms.size - i)) b
        (fun l hl b => f l (mem_literals_iff.mp (List.mem_of_mem_drop hl)) b) := by
  induction i generalizing b with
  | zero =>
    rw [forIn'Impl.loop]
    have hd : c.literals.drop (c.atoms.size - 0) = [] :=
      List.drop_of_length_le (by simp [length_literals])
    simp only [hd, List.forIn'_nil]
  | succ i ih =>
    have hlt : c.atoms.size - (i + 1) < c.literals.length := by
      simp only [length_literals]; omega
    rw [forIn'Impl.loop]
    have harith : c.atoms.size - 1 - i = c.atoms.size - (i + 1) := by omega
    simp only [harith, List.drop_eq_getElem_cons hlt, List.forIn'_cons, getElem_literals hlt]
    apply bind_congr
    intro step
    cases step with
    | done b' => rfl
    | yield b' =>
      dsimp only
      rw [ih (by omega)]
      have harith2 : c.atoms.size - (i + 1) + 1 = c.atoms.size - i := by omega
      simp only [harith2]

theorem forIn'_eq_forIn'_literals [Monad m] {c : Clause α} {init : β}
    {f : (l : Literal α) → l ∈ c → β → m (ForInStep β)} :
    forIn' c init f = forIn' c.literals init (fun l h b => f l (mem_literals_iff.mp h) b) := by
  show forIn'Impl c init f = _
  rw [forIn'Impl, forIn'Impl_loop_eq_forIn'_drop _ (Nat.le_refl _)]
  simp

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
    by_cases hc : c = .empty
    · exact hc
    · exfalso
      rcases exists_eq_add_of_ne_empty hc with ⟨c', atom, pol, rfl⟩
      apply unsat_iff_not_sat.mp h (fun v => if v = atom then pol else true)
      exact sat_add.mpr (Or.inl (by simp))
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

@[simp] theorem not_VarMem_empty {v : α} : ¬VarMem v .empty := by simp [VarMem]

theorem VarMem_add_self {c : Clause α} : VarMem atom (c.add atom pol) := by
  cases pol <;> simp [VarMem]

theorem VarMem_add_ne_self {c : Clause α} {atom1 atom2 : α} (h : atom1 ≠ atom2) :
    VarMem atom1 (c.add atom2 pol) ↔ VarMem atom1 c := by
  simp [VarMem, h]

@[simp] theorem VarMem_add {v : α} : VarMem v (c.add atom pol) ↔ (v = atom ∨ VarMem v c) := by
  by_cases h : v = atom
  · simp [VarMem_add_self, h]
  · simp [VarMem_add_ne_self, h]

@[elab_as_elim]
theorem induct {motive : Clause α → Prop} (empty : motive .empty)
    (add : (c : Clause α) → (atom : α) → (pol : Bool) → motive c → motive (c.add atom pol))
    (c : Clause α) : motive c := by
  have key : ∀ (l : List (Literal α)) (init : Clause α), motive init →
      motive (l.foldl (fun c (atom, pol) => c.add atom pol) init) := by
    intro l
    induction l with
    | nil => intro init h; simpa using h
    | cons x xs ih => intro init hinit; exact ih _ (add init x.1 x.2 hinit)
  have h : motive (ofLiterals c.literals) := key c.literals .empty empty
  rwa [ofLiterals_literals] at h

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

theorem Internal.any_atoms_size_ne_zero_iff_exists_mem {f : CNF α} :
    (f.clauses.any fun c => c.atoms.size != 0) = true ↔ ∃ v, VarMem v f := by
  have h : ∀ c : Clause α, (c.atoms.size != 0) = !c.literals.isEmpty := by
    intro c
    rw [← Clause.length_literals]
    cases c.literals <;> simp
  simp only [h]
  exact Internal.any_not_isEmpty_iff_exists_mem

@[no_expose]
instance {f : CNF α} [DecidableEq α] : Decidable (∃ v, VarMem v f) :=
  decidable_of_iff (f.clauses.any fun c => c.atoms.size != 0)
    Internal.any_atoms_size_ne_zero_iff_exists_mem

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
