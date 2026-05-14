/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Util
public import Init.Data.Option.Basic

public section

@[expose] section

@[never_extract]
def outOfBounds [Inhabited α] : α :=
  panic! "index out of bounds"

theorem outOfBounds_eq_default [Inhabited α] : (outOfBounds : α) = default := rfl

/--
The classes `GetElem` and `GetElem?` implement lookup notation,
specifically `xs[i]`, `xs[i]?`, `xs[i]!`, and `xs[i]'p`.

Both classes are indexed by types `coll`, `idx`, and `elem` which are
the collection, the index, and the element types.
A single collection may support lookups with multiple index
types. The relation `valid` determines when the index is guaranteed to be
valid; lookups of valid indices are guaranteed not to fail.

For example, an instance for arrays looks like
`GetElem (Array α) Nat α (fun xs i => i < xs.size)`. In other words, given an
array `xs` and a natural number `i`, `xs[i]` will return an `α` when `valid xs i`
holds, which is true when `i` is less than the size of the array. `Array`
additionally supports indexing with `USize` instead of `Nat`.
In either case, because the bounds are checked at compile time,
no runtime check is required.

Given `xs[i]` with `xs : coll` and `i : idx`, Lean looks for an instance of
`GetElem coll idx elem valid` and uses this to infer the type of the return
value `elem` and side condition `valid` required to ensure `xs[i]` yields
a valid value of type `elem`. The tactic `get_elem_tactic` is
invoked to prove validity automatically. The `xs[i]'p` notation uses the
proof `p` to satisfy the validity condition.
If the proof `p` is long, it is often easier to place the
proof in the context using `have`, because `get_elem_tactic` tries
`assumption`.


The proof side-condition `valid xs i` is automatically dispatched by the
`get_elem_tactic` tactic; this tactic can be extended by adding more clauses to
`get_elem_tactic_extensible` using `macro_rules`.

`xs[i]?` and `xs[i]!` do not impose a proof obligation; the former returns
an `Option elem`, with `none` signalling that the value isn't present, and
the latter returns `elem` but panics if the value isn't there, returning
`default : elem` based on the `Inhabited elem` instance.
These are provided by the `GetElem?` class, for which there is a default instance
generated from a `GetElem` class as long as `valid xs i` is always decidable.

Important instances include:
  * `arr[i] : α` where `arr : Array α` and `i : Nat` or `i : USize`: does array
    indexing with no runtime bounds check and a proof side goal `i < arr.size`.
  * `l[i] : α` where `l : List α` and `i : Nat`: index into a list, with proof
    side goal `i < l.length`.

-/
class GetElem (coll : Type u) (idx : Type v) (elem : outParam (Type w))
              (valid : outParam (coll → idx → Prop)) where
  /--
  The syntax `arr[i]` gets the `i`'th element of the collection `arr`. If there
  are proof side conditions to the application, they will be automatically
  inferred by the `get_elem_tactic` tactic.
  -/
  getElem (xs : coll) (i : idx) (h : valid xs i) : elem

export GetElem (getElem)

class GetElemV (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  getElemV [h : Nonempty elem] (xs : coll) (i : idx) : elem

export GetElemV (getElemV)

@[inherit_doc getElem]
syntax:max term noWs "[" withoutPosition(term) "]" : term
macro_rules | `($x[$i]) => `(getElem $x $i (by get_elem_tactic))

@[inherit_doc getElem]
syntax term noWs "[" withoutPosition(term) "]'" term:max : term
macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

@[inherit_doc getElem]
syntax:max term noWs "｢" withoutPosition(term) "｣" : term
macro_rules | `($x｢$i｣) => `(getElemV $x $i (h := by first | assumption | infer_instance | exact ⟨by assumption⟩ | exact ⟨$x[$i]⟩))

/-- Helper function for implementation of `GetElem?.getElem?`. -/
abbrev decidableGetElem? [GetElem coll idx elem valid] (xs : coll) (i : idx) [Decidable (valid xs i)] :
    Option elem :=
  if h : valid xs i then some xs[i] else none

@[inherit_doc GetElem]
class GetElem? (coll : Type u) (idx : Type v) (elem : outParam (Type w))
    (valid : outParam (coll → idx → Prop)) extends GetElem coll idx elem valid where
  /--
  The syntax `arr[i]?` gets the `i`'th element of the collection `arr`,
  if it is present (and wraps it in `some`), and otherwise returns `none`.
  -/
  getElem? : coll → idx → Option elem

  /--
  The syntax `arr[i]!` gets the `i`'th element of the collection `arr`,
  if it is present, and otherwise panics at runtime and returns the `default` term
  from `Inhabited elem`.
  -/
  getElem! [Inhabited elem] (xs : coll) (i : idx) : elem :=
    match getElem? xs i with | some e => e | none => outOfBounds

export GetElem? (getElem? getElem!)

/--
The syntax `arr[i]?` gets the `i`'th element of the collection `arr` or
returns `none` if `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)

/--
The syntax `arr[i]!` gets the `i`'th element of the collection `arr` and
panics if `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)

recommended_spelling "getElem" for "xs[i]" in [GetElem.getElem, «term__[_]»]
recommended_spelling "getElem" for "xs[i]'h" in [GetElem.getElem, «term__[_]'_»]
recommended_spelling "getElem?" for "xs[i]?" in [GetElem?.getElem?, «term__[_]_?»]
recommended_spelling "getElem!" for "xs[i]!" in [GetElem?.getElem!, «term__[_]_!»]
recommended_spelling "getElemV" for "xs｢i｣" in [GetElemV.getElemV, «term__｢_｣»]

instance (priority := low) [GetElem coll idx elem valid] [∀ xs i, Decidable (valid xs i)] :
    GetElem? coll idx elem valid where
  getElem? xs i := decidableGetElem? xs i

theorem getElem_congr [GetElem coll idx elem valid] {c d : coll} (h : c = d)
    {i j : idx} (h' : i = j) (w : valid c i) : c[i] = d[j]'(h' ▸ h ▸ w) := by
  cases h; cases h'; rfl

theorem getElem_congr_coll [GetElem coll idx elem valid] {c d : coll} {i : idx} {w : valid c i}
    (h : c = d) : c[i] = d[i]'(h ▸ w) := by
  cases h; rfl

theorem getElem_congr_idx [GetElem coll idx elem valid] {c : coll} {i j : idx} {w : valid c i}
    (h' : i = j) : c[i] = c[j]'(h' ▸ w) := by
  cases h'; rfl

/--
Lawful `GetElem?` instances (which extend `GetElem`) are those for which the potentially-failing
`GetElem?.getElem?` and `GetElem?.getElem!` operators succeed when the validity predicate is
satisfied, and fail when it is not.
-/
class LawfulGetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w))
   (dom : outParam (cont → idx → Prop)) [ge : GetElem? cont idx elem dom] : Prop where

  /-- `GetElem?.getElem?` succeeds when the validity predicate is satisfied and fails otherwise. -/
  getElem?_def (c : cont) (i : idx) [Decidable (dom c i)] :
      c[i]? = if h : dom c i then some (c[i]'h) else none := by
    intros
    try simp only [getElem?] <;> congr

  /-- `GetElem?.getElem!` succeeds and fails when `GetElem.getElem?` succeeds and fails. -/
  getElem!_def [Inhabited elem] (c : cont) (i : idx) :
      c[i]! = match c[i]? with | some e => e | none => default := by
    intros
    simp only [getElem!, getElem?, outOfBounds_eq_default]

export LawfulGetElem (getElem?_def getElem!_def)

class LawfulGetElemV (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop))
    [GetElem? cont idx elem dom] [GetElemV cont idx elem] : Prop where
  getElemV_def {_ : Nonempty elem} (c : cont) (i : idx) :
    c｢i｣ = match c[i]? with | some e => e | none => Classical.ofNonempty

export LawfulGetElemV (getElemV_def)

instance (priority := low) [GetElem coll idx elem valid] [∀ xs i, Decidable (valid xs i)] :
    LawfulGetElem coll idx elem valid where

theorem getElem?_pos [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) : c[i]? = some (c[i]'h) := by
  have : Decidable (dom c i) := .isTrue h
  rw [getElem?_def]
  exact dif_pos h

@[simp]
theorem getElem_eq_getElemV [GetElem? cont idx elem dom]
    [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) :
    c[i] = c｢i｣ := by
  simp [getElemV_def, getElem?_pos, h]

@[grind =, simp]
theorem getElem?_eq_some_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) :
    c[i]? = some c｢i｣ := by
  have : Decidable (dom c i) := .isTrue h
  simp only [getElem?_def, getElem_eq_getElemV]
  exact dif_pos h

grind_pattern getElem?_eq_some_getElemV => haveI : Nonempty elem := _; c｢i｣ where
  guard dom c i

@[simp, grind =]
theorem getElem?_neg [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : ¬dom c i) : c[i]? = none := by
  have : Decidable (dom c i) := .isFalse h
  rw [getElem?_def]
  exact dif_neg h

theorem getElem!_pos [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : dom c i) :
    c[i]! = c[i]'h := by
  have : Decidable (dom c i) := .isTrue h
  simp [getElem!_def, getElem?_pos, h]

@[simp, grind =]
theorem getElem!_eq_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : dom c i) :
    c[i]! = c｢i｣ := by
  simp [getElem!_pos c i h, getElem_eq_getElemV]

@[simp, grind =]
theorem getElem!_neg [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : ¬dom c i) : c[i]! = default := by
  have : Decidable (dom c i) := .isFalse h
  simp [getElem!_def, getElem?_neg, h]

theorem getElemV_pos [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) :
    c｢i｣ = c[i]'h := by
  rw [getElemV_def, getElem?_pos]

theorem getElemV_neg [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {_ : Nonempty elem}
    (c : cont) (i : idx) (h : ¬dom c i) :
    c｢i｣ = Classical.ofNonempty := by
  rw [getElemV_def, getElem?_neg _ _ h]

-- -- TODO
-- theorem get_getElem? [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
--     (c : cont) (i : idx) [Decidable (dom c i)] (h) :
--     c[i]?.get h = c[i]'(by simp only [getElem?_def] at h; split at h <;> simp_all) := by
--   simp only [getElem?_def] at h ⊢
--   split <;> simp_all

-- -- TODO
-- @[simp, grind =]
-- theorem getV_getElem?_eq_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
--     [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
--     (c : cont) (i : idx) [Decidable (dom c i)] (h : (c[i]?).isSome) :
--     haveI : Nonempty elem := ⟨(c[i]?).get h⟩
--     (c[i]?).getV = c｢i｣ := by
--   simp only [getElem?_def] at h ⊢
--   split <;> simp_all [getElem_eq_getElemV]

@[simp] theorem getElem?_eq_none_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) [Decidable (dom c i)] : c[i]? = none ↔ ¬dom c i := by
  simp only [getElem?_def]
  split <;> simp_all

@[simp] theorem none_eq_getElem?_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) [Decidable (dom c i)] : none = c[i]? ↔ ¬dom c i := by
  simp only [getElem?_def]
  split <;> simp_all

theorem of_getElem?_eq_some [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : c[i]? = some e) : dom c i := by
  simp only [getElem?_def] at h
  split at h <;> rename_i h'
  case isTrue =>
    exact h'
  case isFalse =>
    simp at h

theorem getElem?_eq_some_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] : c[i]? = some e ↔ Exists fun h : dom c i => c[i] = e := by
  simp only [getElem?_def]
  split <;> rename_i h
  case isTrue =>
    constructor
    case mp =>
      intro w
      refine ⟨h, ?_⟩
      simpa using w
    case mpr =>
      intro ⟨h, w⟩
      simpa using w
  case isFalse =>
    simp only [reduceCtorEq, false_iff]
    intro ⟨w, w'⟩
    exact h w

theorem getElem?_eq_some_iff_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] {a : elem} :
    c[i]? = some a ↔ dom c i ∧ c｢i｣ = a := by
  simp only [getElem?_eq_some_iff]
  simpa [getElem_eq_getElemV] using ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem some_eq_getElem?_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] : some e = c[i]? ↔ Exists fun h : dom c i => c[i] = e := by
  rw [eq_comm, getElem?_eq_some_iff]

theorem some_eq_getElem?_iff_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] {a : elem} :
    some a = c[i]? ↔ dom c i ∧ c｢i｣ = a := by
  rw [eq_comm, getElem?_eq_some_iff_getElemV]

theorem getElem_of_getElem? [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : c[i]? = some e) : Exists fun h : dom c i => c[i] = e :=
  getElem?_eq_some_iff.mp h

theorem getElemV_of_getElem? [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] {a : elem}
    (h : c[i]? = some a) :
    haveI : Nonempty elem := ⟨a⟩
    c｢i｣ = a := by
  have hdom := of_getElem?_eq_some h
  rw [← getElem_eq_getElemV _ _ hdom]
  exact (getElem?_eq_some_iff.mp h).2

theorem of_getElem_eq [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] {h} (_ : c[i] = e) : dom c i := h

theorem some_getElem_eq_getElem?_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i):
    (some c[i] = c[i]?) ↔ True := by
  simp [getElem?_pos, h]

@[simp] theorem some_getElemV_eq_getElem?_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i) :
    haveI : Nonempty elem := ⟨c[i]⟩
    (some c｢i｣ = c[i]?) ↔ True := by
  simp [h]

theorem getElem?_eq_some_getElem_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i):
    (c[i]? = some c[i]) ↔ True := by
  simp [getElem?_pos, h]

@[simp] theorem getElem?_eq_some_getElemV_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom]
    {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i) :
    haveI : Nonempty elem := ⟨c[i]⟩
    (c[i]? = some c｢i｣) ↔ True := by
  simp [h]

@[simp, grind =] theorem isSome_getElem? [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) [Decidable (dom c i)] : c[i]?.isSome = dom c i := by
  simp only [getElem?_def]
  split <;> simp_all

namespace Fin

instance instGetElemFinVal [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
  getElem xs i h := getElem xs i.1 h

instance instGetElem?FinVal [GetElem? cont Nat elem dom] : GetElem? cont (Fin n) elem fun xs i => dom xs i where
  getElem? xs i := getElem? xs i.val
  getElem! xs i := getElem! xs i.val

instance [GetElem? cont Nat elem dom] [h : LawfulGetElem cont Nat elem dom] :
      LawfulGetElem cont (Fin n) elem fun xs i => dom xs i where
  getElem?_def _c _i _d := h.getElem?_def ..
  getElem!_def _c _i := h.getElem!_def ..

@[simp, grind =] theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

@[simp, grind =] theorem getElem?_fin [h : GetElem? Cont Nat Elem Dom] (a : Cont) (i : Fin n) : a[i]? = a[i.1]? := rfl

@[simp, grind =] theorem getElem!_fin [GetElem? Cont Nat Elem Dom] (a : Cont) (i : Fin n) [Inhabited Elem] : a[i]! = a[i.1]! := rfl

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| (with_reducible apply Fin.val_lt_of_le); get_elem_tactic_extensible; done)

end Fin

namespace List

instance : GetElem (List α) Nat α fun as i => i < as.length where
  getElem as i h := as.get ⟨i, h⟩

@[simp, grind =]
theorem getElem_cons_zero (a : α) (as : List α) (h : 0 < (a :: as).length) :
    getElem (a :: as) 0 h = a := rfl

@[simp, grind =]
theorem getElem_cons_succ (a : α) (as : List α) (i : Nat) (h : i + 1 < (a :: as).length) : getElem (a :: as) (i+1) h = getElem as i (Nat.lt_of_succ_lt_succ h) :=
    rfl

theorem getElem_mem : ∀ {l : List α} {n} (h : n < l.length), l[n]'h ∈ l
  | _ :: _, 0, _ => .head ..
  | _ :: l, _+1, _ => .tail _ (getElem_mem (l := l) ..)

theorem getElem_cons_drop {as : List α} {i : Nat} (h : i < as.length) :
    as[i] :: as.drop (i+1) = as.drop i :=
  match as, i with
  | _::_, 0   => rfl
  | _::_, i+1 => getElem_cons_drop (i := i) (Nat.add_one_lt_add_one_iff.mp h)

@[deprecated getElem_cons_drop (since := "2025-10-26")]
theorem getElem_cons_drop_succ_eq_drop {as : List α} {i : Nat} (h : i < as.length) :
    as[i] :: as.drop (i+1) = as.drop i := getElem_cons_drop h

/-! ### getElem? -/

/-- Internal implementation of `as[i]?`. Do not use directly. -/
-- We still keep it public for reduction purposes
def get?Internal : (as : List α) → (i : Nat) → Option α
  | a::_,  0   => some a
  | _::as, n+1 => get?Internal as n
  | _,     _   => none

/-- Internal implementation of `as[i]!`. Do not use directly. -/
-- We still keep it public for reduction purposes
def get!Internal [Inhabited α] : (as : List α) → (i : Nat) → α
  | a::_,  0   => a
  | _::as, n+1 => get!Internal as n
  | _,     _   => panic! "invalid index"

/-- This instance overrides the default implementation of `a[i]?` via `decidableGetElem?`,
giving better definitional equalities. -/
instance : GetElem? (List α) Nat α fun as i => i < as.length where
  getElem? as i := as.get?Internal i
  getElem! as i := as.get!Internal i

@[simp] theorem get?Internal_eq_getElem? {l : List α} {i : Nat} :
    l.get?Internal i = l[i]? := rfl

@[simp] theorem get!Internal_eq_getElem! [Inhabited α] {l : List α} {i : Nat} :
    l.get!Internal i = l[i]! := rfl

-- This is only needed locally; after the `LawfulGetElem` instance the general `getElem?_pos` lemma applies.
theorem getElem?_eq_getElem {l : List α} {i} (h : i < l.length) :
    l[i]? = some l[i] := by
  induction l generalizing i with
  | nil => cases h
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih ..

-- This is only needed locally; after the `LawfulGetElem` instance the general `getElem?_eq_none_iff` lemma applies.
@[local simp] theorem getElem?_eq_none_iff : l[i]? = none ↔ length l ≤ i :=
  match l with
  | [] => by simp; rfl
  | _ :: l => by
    cases i with
    | zero => simp [List.getElem?_eq_getElem]
    | succ i =>
      simp only [length_cons, Nat.add_le_add_iff_right]
      exact getElem?_eq_none_iff (l := l) (i := i)

theorem none_eq_getElem?_iff {l : List α} {i : Nat} : none = l[i]? ↔ length l ≤ i := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none (h : length l ≤ i) : l[i]? = none := getElem?_eq_none_iff.mpr h

grind_pattern getElem?_eq_none => l.length, l[i]? where
  guard l.length ≤ i

noncomputable def getElemVInternal [Nonempty α] : (as : List α) → (i : Nat) → α
  | a::_,  0   => a
  | _::as, n+1 => getElemVInternal as n
  | _,     _   => Classical.ofNonempty

noncomputable instance : GetElemV (List α) Nat α where
  getElemV xs i := xs.getElemVInternal i

instance : LawfulGetElem (List α) Nat α fun as i => i < as.length where
  getElem?_def as i h := by
    split <;> simp_all [List.getElem?_eq_getElem, List.getElem?_eq_none]
  getElem!_def as i := by
    induction as generalizing i with
    | nil => rfl
    | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i

instance : LawfulGetElemV (List α) Nat α fun as i => i < as.length where
  getElemV_def as i := by
    simp only [getElemV, getElem?]
    induction as generalizing i with
    | nil => rfl
    | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

@[simp]
theorem getElemV_mem {l : List α} {n} (h : n < l.length) : l｢n｣ ∈ l :=
  match l, n with
  | _ :: _, 0 => .head ..
  | _ :: l, _+1 => .tail _ (getElemV_mem (l := l) (by simpa [Nat.add_one_lt_add_one_iff] using h) ..)

grind_pattern getElemV_mem => l｢n｣ ∈ l

@[simp] theorem getElemV_cons_zero {l : List α} :
    haveI : Nonempty α := ⟨a⟩
    (a::l)｢0｣ = a :=
  rfl

@[simp] theorem getElemV_cons_succ {l : List α} :
    haveI : Nonempty α := ⟨a⟩
    (a::l)｢i+1｣ = l｢i｣ :=
  rfl

@[simp]
theorem getElemV_cons_drop {as : List α} {i : Nat} {_ : Nonempty α} (h : i < as.length) :
    as｢i｣ :: as.drop (i+1) = as.drop i := by
  simp [getElemV_pos as i h, getElem_cons_drop, - getElem_eq_getElemV]

@[local simp] theorem getElem?_eq_getElemV {l : List α} {i} (h : i < l.length) :
    haveI : Nonempty α := ⟨l[i]⟩
    l[i]? = some l｢i｣ := by
  induction l generalizing i with
  | nil => cases h
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.getElem?_eq_getElem h]

end List

namespace Array

instance : GetElem (Array α) Nat α fun xs i => i < xs.size where
  getElem xs i h := xs.getInternal i h

-- We provide a `GetElem?` instance, rather than using the low priority instance,
-- so that we use the `@[extern]` definition of `get!Internal`.
instance : GetElem? (Array α) Nat α fun xs i => i < xs.size where
  getElem? xs i := decidableGetElem? xs i
  getElem! xs i := xs.get!Internal i

noncomputable instance : GetElemV (Array α) Nat α where
  getElemV xs i := xs.getD i Classical.ofNonempty

instance : LawfulGetElem (Array α) Nat α fun xs i => i < xs.size where
  getElem?_def xs i h := by
    simp only [getElem?, decidableGetElem?]
    split <;> rfl
  getElem!_def xs i := by
    simp only [getElem!, getElem?, decidableGetElem?, get!Internal, getD, getElem]
    split <;> rfl

instance : LawfulGetElemV (Array α) Nat α fun xs i => i < xs.size where
  getElemV_def xs i := by
    simp only [getElemV, getElem?, decidableGetElem?, getD, getElem]
    split <;> rfl

theorem getInternal_eq_getElem (a : Array α) (i : Nat) (h) :
    a.getInternal i h = a[i] := rfl

@[simp] theorem getInternal_eq_getElemV (a : Array α) (i : Nat) (h) :
    haveI : Nonempty α := ⟨a.getInternal i h⟩
    a.getInternal i h = a｢i｣ := by
  simp [getElemV_pos a i h, getInternal_eq_getElem, - getElem_eq_getElemV]

@[simp] theorem get!Internal_eq_getElem! [Inhabited α] (a : Array α) (i : Nat) :
    a.get!Internal i = a[i]! := by
  simp only [get!Internal, getD, getInternal_eq_getElem, getElem!_def]
  split <;> simp_all [getElem?_neg]

end Array

namespace Lean.Syntax

instance : GetElem Syntax Nat Syntax fun _ _ => True where
  getElem stx i _ := stx.getArg i

end Lean.Syntax
