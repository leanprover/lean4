/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Util

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
`get_elem_tactic_trivial` using `macro_rules`.

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

@[inherit_doc getElem]
syntax:max term noWs "[" withoutPosition(term) "]" : term
macro_rules | `($x[$i]) => `(getElem $x $i (by get_elem_tactic))

@[inherit_doc getElem]
syntax term noWs "[" withoutPosition(term) "]'" term:max : term
macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

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
panics `i` is out of bounds.
-/
macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)

recommended_spelling "getElem" for "xs[i]" in [GetElem.getElem, «term__[_]»]
recommended_spelling "getElem" for "xs[i]'h" in [GetElem.getElem, «term__[_]'_»]
recommended_spelling "getElem?" for "xs[i]?" in [GetElem?.getElem?, «term__[_]_?»]
recommended_spelling "getElem!" for "xs[i]!" in [GetElem?.getElem!, «term__[_]_!»]

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

instance (priority := low) [GetElem coll idx elem valid] [∀ xs i, Decidable (valid xs i)] :
    LawfulGetElem coll idx elem valid where

theorem getElem?_pos [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) : c[i]? = some (c[i]'h) := by
  have : Decidable (dom c i) := .isTrue h
  rw [getElem?_def]
  exact dif_pos h

theorem getElem?_neg [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : ¬dom c i) : c[i]? = none := by
  have : Decidable (dom c i) := .isFalse h
  rw [getElem?_def]
  exact dif_neg h

theorem getElem!_pos [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : dom c i) :
    c[i]! = c[i]'h := by
  have : Decidable (dom c i) := .isTrue h
  simp [getElem!_def, getElem?_def, h]

theorem getElem!_neg [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : ¬dom c i) : c[i]! = default := by
  have : Decidable (dom c i) := .isFalse h
  simp [getElem!_def, getElem?_def, h]

@[simp] theorem get_getElem? [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) [Decidable (dom c i)] (h) :
    c[i]?.get h = c[i]'(by simp only [getElem?_def] at h; split at h <;> simp_all) := by
  simp only [getElem?_def] at h ⊢
  split <;> simp_all

@[simp] theorem getElem?_eq_none_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) [Decidable (dom c i)] : c[i]? = none ↔ ¬dom c i := by
  simp only [getElem?_def]
  split <;> simp_all

@[deprecated getElem?_eq_none_iff (since := "2025-02-17")]
abbrev getElem?_eq_none := @getElem?_eq_none_iff

@[deprecated getElem?_eq_none (since := "2024-12-11")]
abbrev isNone_getElem? := @getElem?_eq_none_iff

@[simp] theorem isSome_getElem? [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
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

@[simp] theorem getElem_fin [GetElem? Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

@[simp] theorem getElem?_fin [h : GetElem? Cont Nat Elem Dom] (a : Cont) (i : Fin n) : a[i]? = a[i.1]? := by rfl

@[simp] theorem getElem!_fin [GetElem? Cont Nat Elem Dom] (a : Cont) (i : Fin n) [Inhabited Elem] : a[i]! = a[i.1]! := rfl

macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| (with_reducible apply Fin.val_lt_of_le); get_elem_tactic_trivial; done)

end Fin

namespace List

instance : GetElem (List α) Nat α fun as i => i < as.length where
  getElem as i h := as.get ⟨i, h⟩

@[simp, grind]
theorem getElem_cons_zero (a : α) (as : List α) (h : 0 < (a :: as).length) : getElem (a :: as) 0 h = a := by
  rfl

@[simp, grind]
theorem getElem_cons_succ (a : α) (as : List α) (i : Nat) (h : i + 1 < (a :: as).length) : getElem (a :: as) (i+1) h = getElem as i (Nat.lt_of_succ_lt_succ h) := by
  rfl

@[simp] theorem getElem_mem : ∀ {l : List α} {n} (h : n < l.length), l[n]'h ∈ l
  | _ :: _, 0, _ => .head ..
  | _ :: l, _+1, _ => .tail _ (getElem_mem (l := l) ..)

theorem getElem_cons_drop_succ_eq_drop {as : List α} {i : Nat} (h : i < as.length) :
    as[i] :: as.drop (i+1) = as.drop i :=
  match as, i with
  | _::_, 0   => rfl
  | _::_, i+1 => getElem_cons_drop_succ_eq_drop (i := i) (Nat.add_one_lt_add_one_iff.mp h)

@[deprecated getElem_cons_drop_succ_eq_drop (since := "2024-11-05")]
abbrev get_drop_eq_drop := @getElem_cons_drop_succ_eq_drop

/-! ### getElem? -/

/-- Internal implementation of `as[i]?`. Do not use directly. -/
private def get?Internal : (as : List α) → (i : Nat) → Option α
  | a::_,  0   => some a
  | _::as, n+1 => get?Internal as n
  | _,     _   => none

/-- Internal implementation of `as[i]!`. Do not use directly. -/
private def get!Internal [Inhabited α] : (as : List α) → (i : Nat) → α
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

@[simp] theorem getElem?_eq_getElem {l : List α} {i} (h : i < l.length) :
    l[i]? = some l[i] := by
  induction l generalizing i with
  | nil => cases h
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih ..

@[simp] theorem getElem?_eq_none_iff : l[i]? = none ↔ length l ≤ i :=
  match l with
  | [] => by simp; rfl
  | _ :: l => by
    cases i with
    | zero => simp
    | succ i =>
      simp only [length_cons, Nat.add_le_add_iff_right]
      exact getElem?_eq_none_iff (l := l) (i := i)

@[simp] theorem none_eq_getElem?_iff {l : List α} {i : Nat} : none = l[i]? ↔ length l ≤ i := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none (h : length l ≤ i) : l[i]? = none := getElem?_eq_none_iff.mpr h

instance : LawfulGetElem (List α) Nat α fun as i => i < as.length where
  getElem?_def as i h := by
    split <;> simp_all
  getElem!_def as i := by
    induction as generalizing i with
    | nil => rfl
    | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i

end List

namespace Array

instance : GetElem (Array α) Nat α fun xs i => i < xs.size where
  getElem xs i h := xs.getInternal i h

-- We provide a `GetElem?` instance, rather than using the low priority instance,
-- so that we use the `@[extern]` definition of `get!Internal`.
instance : GetElem? (Array α) Nat α fun xs i => i < xs.size where
  getElem? xs i := decidableGetElem? xs i
  getElem! xs i := xs.get!Internal i

instance : LawfulGetElem (Array α) Nat α fun xs i => i < xs.size where
  getElem?_def xs i h := by
    simp only [getElem?, decidableGetElem?]
    split <;> rfl
  getElem!_def xs i := by
    simp only [getElem!, getElem?, decidableGetElem?, get!Internal, getD, getElem]
    split <;> rfl

@[simp] theorem getInternal_eq_getElem (a : Array α) (i : Nat) (h) :
    a.getInternal i h = a[i] := rfl

@[simp] theorem get!Internal_eq_getElem! [Inhabited α] (a : Array α) (i : Nat) :
    a.get!Internal i = a[i]! := by
  simp only [get!Internal, getD, getInternal_eq_getElem, getElem!_def]
  split <;> simp_all [getElem?_pos, getElem?_neg]

end Array

namespace Lean.Syntax

instance : GetElem Syntax Nat Syntax fun _ _ => True where
  getElem stx i _ := stx.getArg i

end Lean.Syntax
