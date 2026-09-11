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

public section

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
def size (c : Clause α) : Nat := c.atoms.size

theorem Internal.size_eq_size_atoms {c : Clause α} : c.size = c.atoms.size := by
  simp [size]

theorem Internal.size_eq_size_polarities {c : Clause α} : c.size = c.polarities.size := by
  simp [size, c.size_polarities]

@[simp]
theorem size_empty : Clause.size (Clause.empty : Clause α) = 0 := by
  simp [Internal.size_eq_size_atoms, Clause.empty]

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

@[simp]
theorem Internal.atoms_add {c : Clause α} : (c.add atom pol).atoms = c.atoms.push atom := by
  rfl

@[simp]
theorem size_add (c : Clause α) (atom : α) (pol : Bool) :
    (c.add atom pol).size = c.size + 1 := by
  simp [Internal.size_eq_size_atoms]

/--
The polarity of the literal at index `i` of `c`; `false` if `i` is out of bounds.
-/
@[expose]
def polarity (c : Clause α) (i : Nat) : Bool :=
  if h : i < c.polarities.size then c.polarities[i] == 1 else false

theorem Internal.polarity_eq_data {c : Clause α} {i : Nat} :
    c.polarity i = (c.polarities.data[i]?.getD 0 == 1) := by
  rw [polarity]
  split
  · next h =>
    rw [Array.getElem?_eq_getElem (by simp only [ByteArray.size_data]; exact h),
      Option.getD_some, ByteArray.getElem_eq_getElem_data]
  · next h =>
    rw [Array.getElem?_eq_none (by simp only [ByteArray.size_data]; omega), Option.getD_none]
    rfl

theorem Internal.polarity_eq_getElem {c : Clause α} {i : Nat} (h : i < c.polarities.size) :
    c.polarity i = (c.polarities[i] == 1) := by
  rw [polarity, dite_eq_left h]

@[simp]
theorem polarity_empty : (Clause.empty : Clause α).polarity i = false := by
  simp [Internal.polarity_eq_data, Clause.empty]

theorem polarity_add {c : Clause α} {i : Nat} :
    (c.add atom pol).polarity i = if i = c.size then pol else c.polarity i := by
  simp only [add, Internal.polarity_eq_data, ByteArray.data_push, Array.getElem?_push,
    ByteArray.size_data, Internal.size_eq_size_polarities]
  by_cases h : i = c.polarities.size
  · cases pol <;> simp [h]
  · simp [h]

-- TODO: noncomputable test
/--
The literals of a `Clause` as a list of atom/polarity pairs, used to state specifications.
This function runs in O(n) and allocates all of the `List` and the `Literal` objects fresh.
For this reason it is not useful for performance sensitive contexts.
-/
@[expose]
def literals (c : Clause α) : List (Literal α) :=
  c.atoms.toList.zipIdx.map fun (x, i) => (x, c.polarity i)

@[simp]
theorem literals_empty : (empty : Clause α).literals = [] := by
  rfl

@[simp]
theorem literals_add {c : Clause α} :
    (c.add atom pol).literals = c.literals ++ [(atom, pol)] := by
  simp only [literals, Internal.atoms_add, Array.toList_push, List.zipIdx_append, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro ⟨x, i⟩ h
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp h)
    have hne : i ≠ c.size := Nat.ne_of_lt (by simpa [Internal.size_eq_size_atoms] using hi)
    simp [polarity_add, hne]
  · simp [polarity_add, Internal.size_eq_size_atoms]

theorem length_literals {c : Clause α} : c.literals.length = c.size := by
  simp [literals, Internal.size_eq_size_atoms]

theorem Internal.map_fst_literals {c : Clause α} : c.literals.map Prod.fst = c.atoms.toList := by
  simp only [literals, List.map_map]
  exact List.zipIdx_map_fst 0 c.atoms.toList

theorem Internal.getElem_literals {c : Clause α} {i : Nat} (h : i < c.literals.length) :
    c.literals[i] = (c.atoms[i]'(by simpa [length_literals, Internal.size_eq_size_atoms] using h), c.polarity i) := by
  simp [literals, List.getElem_zipIdx]

protected theorem ext {c1 c2 : Clause α} (h : c1.literals = c2.literals) : c1 = c2 := by
  rcases c1 with ⟨a1, p1, hs1, hb1⟩
  rcases c2 with ⟨a2, p2, hs2, hb2⟩
  obtain rfl : a1 = a2 := by
    have h1 := congrArg (List.map Prod.fst) h
    rw [Internal.map_fst_literals, Internal.map_fst_literals] at h1
    exact Array.toList_inj.mp h1
  suffices hp : p1 = p2 by cases hp; rfl
  apply ByteArray.ext_getElem (by rw [hs1, hs2])
  intro i hi hi'
  have hl : i < (⟨a1, p1, hs1, hb1⟩ : Clause α).literals.length := by
    rw [length_literals]
    simp [Internal.size_eq_size_polarities, hi]
  have hget := List.getElem_of_eq h hl
  rw [Internal.getElem_literals, Internal.getElem_literals] at hget
  have hpol := congrArg Prod.snd hget
  simp only [Internal.polarity_eq_data] at hpol
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

instance : Membership (Literal α) (Clause α) where
  mem clause lit := lit ∈ clause.literals

theorem mem_literals_iff {c : Clause α} {l : Literal α} : l ∈ c.literals ↔ l ∈ c := Iff.rfl

theorem Internal.getElem_mem {c : Clause α} {i : Nat} (h : i < c.atoms.size) :
    (c.atoms[i], c.polarity i) ∈ c := by
  rw [← mem_literals_iff]
  have hl : i < c.literals.length := by simpa [length_literals, Internal.size_eq_size_atoms] using h
  rw [← Internal.getElem_literals hl]
  exact List.getElem_mem hl

theorem Internal.mem_iff_exists_getElem {c : Clause α} {l : Literal α} :
    l ∈ c ↔ ∃ (i : Nat) (h : i < c.atoms.size), (c.atoms[i], c.polarity i) = l := by
  rw [← mem_literals_iff, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, by simpa [length_literals, Internal.size_eq_size_atoms] using h, by rw [Internal.getElem_literals]⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, by simpa [length_literals, Internal.size_eq_size_atoms] using h, by rw [Internal.getElem_literals]⟩

theorem ne_of_mem_of_negate_mem {c : Clause α} (h1 : l ∈ c) (h2 : l' ∉ c)
    (h3 : l'.negate ∉ c) : l.1 ≠ l'.1 := by
  intro h4
  rcases l with ⟨latom, lpol⟩
  rcases l' with ⟨latom', lpol'⟩
  simp only [Internal.mem_iff_exists_getElem, Prod.mk.injEq, exists_and_right, not_exists, not_and,
    forall_exists_index, Literal.negate, Bool.not_eq_not] at h1 h2 h3
  rcases h1 with ⟨i, ⟨hi, heq1⟩, heq2⟩
  specialize h2 i hi
  specialize h3 i hi
  simp_all

@[inline]
def contains [BEq α] (c : Clause α) (lit : Literal α) : Bool :=
  go 0
where
  go (i : Nat) : Bool :=
    if h : i < c.size then
      have h1 := by simpa [Internal.size_eq_size_atoms] using h
      have h2 := by simpa [Internal.size_eq_size_polarities] using h
      if c.atoms[i]'h1 == lit.1 && (c.polarities[i]'h2 == 1) == lit.2 then
        true
      else
        go (i + 1)
    else
      false

private theorem contains_go_iff [BEq α] [LawfulBEq α] {c : Clause α} {lit : Literal α} {i : Nat} :
    contains.go c lit i = true
      ↔ ∃ (j : Nat) (hj : j < c.atoms.size), i ≤ j ∧ (c.atoms[j], c.polarity j) = lit := by
  fun_induction contains.go c lit i with
  | case1 i h1 h2 h3 h =>
    simp only [exists_and_left, true_iff]
    cases lit
    exists i
    simp_all [Internal.polarity_eq_getElem]
  | case2 i h1 h2 h3 h4 ih  =>
    rw [ih]
    constructor
    · rintro ⟨j, hj1, hj2⟩
      exists j, hj1
      constructor
      · omega
      · simp [hj2.right]
    · rintro ⟨j, hj1, hj2⟩
      exists j, hj1
      constructor
      · have : j < c.polarities.size := by
          simpa [← c.size_polarities] using hj1
        have : i ≠ j := by
          intro h5
          cases lit
          simp_all [Internal.polarity_eq_getElem]
        omega
      · simp [hj2.right]
  | case3 _ hnlt =>
    simp only [Bool.false_eq_true, exists_and_left, false_iff, not_exists, not_and]
    intro j hle hj
    simp only [Internal.size_eq_size_atoms] at hnlt
    omega

theorem contains_iff_mem [BEq α] [LawfulBEq α] {c : Clause α} {lit : Literal α} :
    c.contains lit = true ↔ lit ∈ c := by
  rw [contains, contains_go_iff, Internal.mem_iff_exists_getElem]
  exact ⟨fun ⟨j, hj, _, hlit⟩ => ⟨j, hj, hlit⟩, fun ⟨j, hj, hlit⟩ => ⟨j, hj, by omega, hlit⟩⟩

instance [DecidableEq α] {lit : Literal α} {c : Clause α} : Decidable (lit ∈ c) :=
  decidable_of_iff (c.contains lit = true) contains_iff_mem

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
  go 0 b
where
  go (i : Nat) (b : β) : m β := do
    if h : i < c.atoms.size then
      match ← f (c.atoms[i], c.polarity i) (Internal.getElem_mem h) b with
      | .done b => pure b
      | .yield b => go (i + 1) b
    else
      pure b

instance [Monad m] : ForIn' m (Clause α) (Literal α) inferInstance where
  forIn' := forIn'Impl

@[simp]
theorem not_mem_empty {l : Literal α} : l ∉ (empty : Clause α) := by
  simp [← mem_literals_iff]

@[simp]
theorem mem_add {c : Clause α} {l1 : Literal α} :
    l1 ∈ c.add atom pol ↔ l1 = (atom, pol) ∨ l1 ∈ c := by
  simp [← mem_literals_iff, or_comm]

private theorem forIn'Impl_go_eq_forIn'_drop [Monad m] {c : Clause α}
    {f : (l : Literal α) → l ∈ c → β → m (ForInStep β)} (i : Nat) (b : β) :
    forIn'Impl.go c f i b =
      forIn' (c.literals.drop i) b
        (fun l hl b => f l (mem_literals_iff.mp (List.mem_of_mem_drop hl)) b) := by
  fun_induction forIn'Impl.go c f i b with
  | case1 i b h ih =>
    have hlt : i < c.literals.length := by
      simp only [length_literals, Internal.size_eq_size_atoms]; omega
    simp only [List.drop_eq_getElem_cons hlt, List.forIn'_cons, Internal.getElem_literals hlt]
    apply bind_congr
    intro step
    cases step with
    | done b' => rfl
    | yield b' => exact ih b'
  | case2 i b h =>
    have hd : c.literals.drop i = [] :=
      List.drop_of_length_le (by simp only [length_literals, Internal.size_eq_size_atoms]; omega)
    simp only [hd, List.forIn'_nil]

theorem forIn'_eq_forIn'_literals [Monad m] {c : Clause α} {init : β}
    {f : (l : Literal α) → l ∈ c → β → m (ForInStep β)} :
    forIn' c init f = forIn' c.literals init (fun l h b => f l (mem_literals_iff.mp h) b) := by
  show forIn'Impl c init f = _
  rw [forIn'Impl, forIn'Impl_go_eq_forIn'_drop]
  simp

/--
Erase all occurrences of `lit` from `c`.
-/
@[inline]
def erase [BEq α] (c : Clause α) (lit : Literal α) : Clause α :=
  go 0 empty
where
  go (i : Nat) (acc : Clause α) : Clause α :=
    if h : i < c.size then
      let atom := c.atoms[i]'(by rw [← Internal.size_eq_size_atoms]; exact h)
      let pol := (c.polarities[i]'(by rw [c.size_polarities]; exact h)) == 1
      if atom == lit.fst && pol == lit.snd then
        go (i + 1) acc
      else
        go (i + 1) (acc.add atom pol)
    else
      acc

private theorem literals_erase_go [BEq α] [LawfulBEq α] {c : Clause α} {lit : Literal α} {i : Nat}
    {acc : Clause α} :
    (erase.go c lit i acc).literals
      = acc.literals ++ (c.literals.drop i).filter (fun l => l != lit) := by
  fun_induction erase.go c lit i acc with
  | case1 i acc h atom pol heq ih =>
    have hlt : i < c.literals.length := by rw [length_literals]; exact h
    have hlit : c.literals[i] = lit := by
      rw [Internal.getElem_literals hlt, Internal.polarity_eq_getElem (by rw [c.size_polarities]; exact h)]
      simp only [atom, pol, Bool.and_eq_true, beq_iff_eq] at heq
      simp [heq.1, heq.2]
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hlit]
    simp [ih]
  | case2 i acc h atom pol heq ih =>
    have hlt : i < c.literals.length := by rw [length_literals]; exact h
    have hlit : c.literals[i] = (atom, pol) := by
      rw [Internal.getElem_literals hlt, Internal.polarity_eq_getElem (by rw [c.size_polarities]; exact h)]
    have hne : ((atom, pol) : Literal α) != lit := by
      simp only [atom, pol, Bool.and_eq_true, beq_iff_eq, not_and] at heq
      simp only [bne_iff_ne, ne_eq, Prod.ext_iff, not_and]
      exact heq
    rw [List.drop_eq_getElem_cons hlt, List.filter_cons, hlit, ih, literals_add]
    simp [hne]
  | case3 i acc h =>
    rw [List.drop_of_length_le (by rw [length_literals]; omega)]
    simp

@[simp]
theorem literals_erase [BEq α] [LawfulBEq α] {c : Clause α} {lit : Literal α} :
    (c.erase lit).literals = c.literals.filter (fun l => l != lit) := by
  rw [erase, literals_erase_go]
  simp

@[simp]
theorem mem_erase_iff [BEq α] [LawfulBEq α] {c : Clause α} :
    lit' ∈ c.erase lit ↔ (lit ≠ lit' ∧ lit' ∈ c) := by
  rw [← mem_literals_iff, literals_erase, List.mem_filter, ← mem_literals_iff]
  simp [and_comm, ne_comm]

/--
The disjunction of two clauses, obtained by concatenating their literals.
-/
def append (c1 c2 : Clause α) : Clause α where
  atoms := c1.atoms ++ c2.atoms
  polarities := c1.polarities ++ c2.polarities
  size_polarities := by
    rw [ByteArray.size_append, Array.size_append, c1.size_polarities, c2.size_polarities]
  isBool_polarities := by
    intro i h
    have hs : (c1.polarities ++ c2.polarities).size = c1.polarities.size + c2.polarities.size :=
      ByteArray.size_append
    by_cases h' : i < c1.polarities.size
    · rw [ByteArray.getElem_append_left h']
      exact c1.isBool_polarities i h'
    · rw [ByteArray.getElem_append_right (by omega)]
      exact c2.isBool_polarities _ (by omega)

instance : Append (Clause α) where
  append := append

@[simp]
theorem Internal.atoms_append {c1 c2 : Clause α} : (c1 ++ c2).atoms = c1.atoms ++ c2.atoms := by
  rfl

@[simp]
theorem Internal.polarities_append {c1 c2 : Clause α} :
    (c1 ++ c2).polarities = c1.polarities ++ c2.polarities := by
  rfl

theorem polarity_append {c1 c2 : Clause α} {i : Nat} :
    (c1 ++ c2).polarity i =
      if i < c1.size then c1.polarity i else c2.polarity (i - c1.size) := by
  have h1 : c1.polarities.data.size = c1.size := by
    rw [ByteArray.size_data, ← Internal.size_eq_size_polarities]
  simp only [Internal.polarity_eq_data, Internal.polarities_append, ByteArray.data_append,
    Array.getElem?_append, h1]
  split <;> rfl

@[simp]
theorem size_append {c1 c2 : Clause α} :
    (c1 ++ c2).size = c1.size + c2.size := by
  simp [Internal.size_eq_size_atoms]

@[simp]
theorem literals_append {c1 c2 : Clause α} :
    (c1 ++ c2).literals = c1.literals ++ c2.literals := by
  apply List.ext_getElem
  · simp [length_literals]
  · intro i h1 h2
    rw [Internal.getElem_literals h1, polarity_append]
    simp only [Internal.atoms_append]
    by_cases hi : i < c1.size
    · have hi' : i < c1.atoms.size := by simpa [Internal.size_eq_size_atoms] using hi
      rw [ite_eq_left hi, Array.getElem_append_left hi',
        List.getElem_append_left (by simpa [length_literals] using hi),
        Internal.getElem_literals]
    · have hi' : ¬ i < c1.atoms.size := by simpa [Internal.size_eq_size_atoms] using hi
      rw [ite_eq_right hi, Array.getElem_append_right (by omega),
        List.getElem_append_right (by simp only [length_literals]; omega), Internal.getElem_literals]
      simp [length_literals, Internal.size_eq_size_atoms]

@[simp]
theorem empty_append {c : Clause α} : (empty : Clause α) ++ c = c := Clause.ext (by simp)

@[simp]
theorem append_empty {c : Clause α} : c ++ (empty : Clause α) = c := Clause.ext (by simp)

@[simp]
theorem append_assoc {c1 c2 c3 : Clause α} : (c1 ++ c2) ++ c3 = c1 ++ (c2 ++ c3) :=
  Clause.ext (by simp)

@[simp]
theorem append_add {c1 c2 : Clause α} : c1 ++ c2.add atom pol = (c1 ++ c2).add atom pol :=
  Clause.ext (by simp)

theorem ofLiterals_append {l1 l2 : List (Literal α)} :
    ofLiterals (l1 ++ l2) = ofLiterals l1 ++ ofLiterals l2 := Clause.ext (by simp)

@[simp]
theorem append_eq_empty_iff {c1 c2 : Clause α} : c1 ++ c2 = empty ↔ c1 = empty ∧ c2 = empty := by
  rw [← literals_eq_nil_iff, ← literals_eq_nil_iff, ← literals_eq_nil_iff, literals_append,
    List.append_eq_nil_iff]

@[simp]
theorem mem_append {c1 c2 : Clause α} {l : Literal α} : l ∈ c1 ++ c2 ↔ l ∈ c1 ∨ l ∈ c2 := by
  simp [← mem_literals_iff]

end Clause

@[expose, inline]
def empty : CNF α := { clauses := #[] }

@[expose, inline]
def emptyWithCapacity (n : Nat) : CNF α := { clauses := .emptyWithCapacity n }

@[expose, inline]
def add (f : CNF α) (c : CNF.Clause α) : CNF α := { f with clauses := f.clauses.push c }

@[inline]
def append (f1 f2 : CNF α) : CNF α :=
  { clauses := f1.clauses ++ f2.clauses }

instance : Append (CNF α) where
  append := append

namespace Clause

/--
Variable `v` occurs in `Clause` `c`.
-/
def VarMem (v : α) (c : Clause α) : Prop := v ∈ c.atoms

instance {v : α} {c : Clause α} [DecidableEq α] : Decidable (VarMem v c) :=
  inferInstanceAs <| Decidable (v ∈ c.atoms)

theorem VarMem_iff_exists_mem_literals {v : α} {c : Clause α} :
    VarMem v c ↔ ∃ pol, (v, pol) ∈ c.literals := by
  simp only [VarMem, ← Array.mem_toList_iff, ← Internal.map_fst_literals, List.mem_map]
  constructor
  · rintro ⟨⟨_, pol⟩, hmem, rfl⟩
    exact ⟨pol, hmem⟩
  · rintro ⟨pol, hmem⟩
    exact ⟨(v, pol), hmem, rfl⟩

@[simp] theorem not_VarMem_empty {v : α} : ¬VarMem v .empty := by simp [VarMem, empty]

theorem VarMem_add_self {c : Clause α} : VarMem atom (c.add atom pol) := by
  cases pol <;> simp [VarMem]

theorem VarMem_add_ne_self {c : Clause α} {atom1 atom2 : α} (h : atom1 ≠ atom2) :
    VarMem atom1 (c.add atom2 pol) ↔ VarMem atom1 c := by
  simp [VarMem, h]

@[simp] theorem VarMem_add {v : α} : VarMem v (c.add atom pol) ↔ (v = atom ∨ VarMem v c) := by
  by_cases h : v = atom
  · simp [VarMem_add_self, h]
  · simp [VarMem_add_ne_self, h]

@[simp] theorem VarMem_append {v : α} {c1 c2 : Clause α} :
    VarMem v (c1 ++ c2) ↔ (VarMem v c1 ∨ VarMem v c2) := by
  simp [VarMem]

@[elab_as_elim]
theorem inductionOn {motive : Clause α → Prop} (empty : motive .empty)
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

theorem Internal.clauses_append {f1 f2 : CNF α} : (f1 ++ f2).clauses = f1.clauses ++ f2.clauses := by
  rfl

@[simp]
theorem not_mem_empty {c : Clause α} : c ∉ (empty : CNF α) := by
  simp [Internal.mem_iff, empty]

@[simp]
theorem mem_add {f : CNF α} {c1 c2 : Clause α} : c1 ∈ f.add c2 ↔ c1 = c2 ∨ c1 ∈ f := by
  simp [Internal.mem_iff, add, or_comm]

@[simp]
theorem mem_append {f1 f2 : CNF α} {c : Clause α} : c ∈ (f1 ++ f2) ↔ c ∈ f1 ∨ c ∈ f2 := by
  simp [Internal.mem_iff, Internal.clauses_append]

/--
Variable `v` occurs in `CNF` formula `f`.
-/
@[expose]
def VarMem (v : α) (f : CNF α) : Prop := ∃ c, c ∈ f.clauses ∧ c.VarMem v

instance {v : α} {f : CNF α} [DecidableEq α] : Decidable (VarMem v f) :=
  inferInstanceAs <| Decidable (∃ c, c ∈ f.clauses ∧ c.VarMem v)

theorem Internal.any_not_isEmpty_iff_exists_mem {f : CNF α} :
    (f.clauses.any fun c => !List.isEmpty c.literals) = true ↔ ∃ v, VarMem v f := by
  simp only [Array.any_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, VarMem,
    Clause.VarMem_iff_exists_mem_literals]
  constructor
  · rintro ⟨idx, hidx, ⟨atom, pol⟩, hlit⟩
    exact ⟨atom, f.clauses[idx], Array.getElem_mem hidx, pol, hlit⟩
  · rintro ⟨v, clause, hclause, pol, hlit⟩
    rw [Array.mem_iff_getElem] at hclause
    rcases hclause with ⟨idx, hidx, rfl⟩
    exact ⟨idx, hidx, (v, pol), hlit⟩

theorem Internal.any_atoms_size_ne_zero_iff_exists_mem {f : CNF α} :
    (f.clauses.any fun c => c.atoms.size != 0) = true ↔ ∃ v, VarMem v f := by
  have h : ∀ c : Clause α, (c.atoms.size != 0) = !c.literals.isEmpty := by
    intro c
    rw [← Clause.Internal.size_eq_size_atoms, ← Clause.length_literals]
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

end CNF

end Sat
end Std
