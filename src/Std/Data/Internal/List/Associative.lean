/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.BEq
import Init.Data.Nat.Simproc
import Init.Data.List.Perm
import Init.Data.List.Find
import Std.Classes.Ord
import Std.Data.Internal.List.Defs

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: Verification of associative lists
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w}

open List (Perm Sublist pairwise_cons erase_sublist filter_sublist)

namespace Std.Internal.List

attribute [-simp] List.isEmpty_eq_false_iff

@[elab_as_elim]
theorem assoc_induction {motive : List ((a : α) × β a) → Prop} (nil : motive [])
    (cons : (k : α) → (v : β k) → (tail : List ((a : α) × β a)) →
        motive tail → motive (⟨k, v⟩ :: tail)) :
    (t : List ((a : α) × β a)) → motive t
  | [] => nil
  | ⟨_, _⟩ :: _ => cons _ _ _ (assoc_induction nil cons _)

/-- Internal implementation detail of the hash map -/
def getEntry? [BEq α] (a : α) : List ((a : α) × β a) → Option ((a : α) × β a)
  | [] => none
  | ⟨k, v⟩ :: l => bif k == a then some ⟨k, v⟩ else getEntry? a l

@[simp] theorem getEntry?_nil [BEq α] {a : α} :
    getEntry? a ([] : List ((a : α) × β a)) = none := rfl
theorem getEntry?_cons [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} :
    getEntry? a (⟨k, v⟩ :: l) = bif k == a then some ⟨k, v⟩ else getEntry? a l := rfl

theorem getEntry?_cons_of_true [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} (h : k == a) :
    getEntry? a (⟨k, v⟩ :: l) = some ⟨k, v⟩ := by
  simp [getEntry?, h]

theorem getEntry?_cons_of_false [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    (h : (k == a) = false) : getEntry? a (⟨k, v⟩ :: l) = getEntry? a l := by
  simp [getEntry?, h]

@[simp]
theorem getEntry?_cons_self [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    getEntry? k (⟨k, v⟩ :: l) = some ⟨k, v⟩ :=
  getEntry?_cons_of_true BEq.refl

theorem getEntry?_eq_some [BEq α] {l : List ((a : α) × β a)} {a : α} {p : (a : α) × β a}
    (h : getEntry? a l = some p) : p.1 == a := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    cases h' : k' == a
    · rw [getEntry?_cons_of_false h'] at h
      exact ih h
    · rw [getEntry?_cons_of_true h', Option.some.injEq] at h
      obtain rfl := congrArg Sigma.fst h
      exact h'

theorem getEntry?_congr [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a b : α}
    (h : a == b) : getEntry? a l = getEntry? b l := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h' : k == a
    · have h₂ : (k == b) = false := BEq.neq_of_neq_of_beq h' h
      rw [getEntry?_cons_of_false h', getEntry?_cons_of_false h₂, ih]
    · rw [getEntry?_cons_of_true h', getEntry?_cons_of_true (BEq.trans h' h)]

theorem isEmpty_eq_false_iff_exists_isSome_getEntry? [BEq α] [ReflBEq α] :
    {l : List ((a : α) × β a)} → l.isEmpty = false ↔ ∃ a, (getEntry? a l).isSome
  | [] => by simp
  | (⟨k, v⟩::l) => by simpa using ⟨k, by simp⟩

theorem isEmpty_iff_forall_isSome_getEntry? [BEq α] [ReflBEq α] :
    {l : List ((a : α) × β a)} → l.isEmpty ↔ ∀ a, (getEntry? a l).isSome = false
  | [] => by simp
  | (⟨k, v⟩::l) => ⟨by simp, fun h => have := h k; by simp at this⟩

section

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def getValue? [BEq α] (a : α) : List ((_ : α) × β) → Option β
  | [] => none
  | ⟨k, v⟩ :: l => bif k == a then some v else getValue? a l

@[simp] theorem getValue?_nil [BEq α] {a : α} : getValue? a ([] : List ((_ : α) × β)) = none := rfl
theorem getValue?_cons [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} :
    getValue? a (⟨k, v⟩ :: l) = bif k == a then some v else getValue? a l := rfl

theorem getValue?_cons_of_true [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    getValue? a (⟨k, v⟩ :: l) = some v := by
  simp [getValue?, h]

theorem getValue?_cons_of_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β}
    (h : (k == a) = false) : getValue? a (⟨k, v⟩ :: l) = getValue? a l := by
  simp [getValue?, h]

@[simp]
theorem getValue?_cons_self [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    getValue? k (⟨k, v⟩ :: l) = some v :=
  getValue?_cons_of_true BEq.refl

theorem getValue?_eq_getEntry? [BEq α] {l : List ((_ : α) × β)} {a : α} :
    getValue? a l = (getEntry? a l).map (·.2) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [getEntry?_cons_of_false h, getValue?_cons_of_false h, ih]
    · rw [getEntry?_cons_of_true h, getValue?_cons_of_true h, Option.map_some']

theorem getValue?_congr [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {a b : α}
    (h : a == b) : getValue? a l = getValue? b l := by
  simp [getValue?_eq_getEntry?, getEntry?_congr h]

theorem isEmpty_eq_false_iff_exists_isSome_getValue? [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} :
    l.isEmpty = false ↔ ∃ a, (getValue? a l).isSome := by
  simp [isEmpty_eq_false_iff_exists_isSome_getEntry?, getValue?_eq_getEntry?]

end

/-- Internal implementation detail of the hash map -/
def getValueCast? [BEq α] [LawfulBEq α] (a : α) : List ((a : α) × β a) → Option (β a)
  | [] => none
  | ⟨k, v⟩ :: l => if h : k == a then some (cast (congrArg β (eq_of_beq h)) v)
      else getValueCast? a l

@[simp] theorem getValueCast?_nil [BEq α] [LawfulBEq α] {a : α} :
    getValueCast? a ([] : List ((a : α) × β a)) = none := rfl
theorem getValueCast?_cons [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} :
    getValueCast? a (⟨k, v⟩ :: l) = if h : k == a then some (cast (congrArg β (eq_of_beq h)) v)
      else getValueCast? a l := rfl

theorem getValueCast?_cons_of_true [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} (h : k == a) :
    getValueCast? a (⟨k, v⟩ :: l) = some (cast (congrArg β (eq_of_beq h)) v) := by
  simp [getValueCast?, h]

theorem getValueCast?_cons_of_false [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} (h : (k == a) = false) : getValueCast? a (⟨k, v⟩ :: l) = getValueCast? a l := by
  simp [getValueCast?, h]

@[simp]
theorem getValueCast?_cons_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    getValueCast? k (⟨k, v⟩ :: l) = some v := by
  rw [getValueCast?_cons_of_true BEq.refl, cast_eq]

theorem getValue?_eq_getValueCast? [BEq α] [LawfulBEq α] {β : Type v} {l : List ((_ : α) × β)}
    {a : α} : getValue? a l = getValueCast? a l := by
  induction l using assoc_induction <;> simp_all [getValueCast?_cons, getValue?_cons]

section

variable {β : Type v}

/-- This is a strange dependent version of `Option.map` in which the mapping function is allowed to
"know" about the option that is being mapped. This happens to be useful in this file (see
`getValueCast_eq_getEntry?`), but we do not want it to leak out of the file. -/
private def Option.dmap : (o : Option α) → (f : (a : α) → (o = some a) → β) → Option β
  | none, _ => none
  | some a, f => some (f a rfl)

@[simp] private theorem Option.dmap_none (f : (a : α) → (none = some a) → β) :
    Option.dmap none f = none := rfl

@[simp] private theorem Option.dmap_some (a : α) (f : (a' : α) → (some a = some a') → β) :
    Option.dmap (some a) f = some (f a rfl) := rfl

private theorem Option.dmap_congr {o o' : Option α} {f : (a : α) → (o = some a) → β} (h : o = o') :
    Option.dmap o f = Option.dmap o' (fun a h' => f a (h ▸ h')) := by
  cases h; rfl

@[simp]
private theorem Option.isSome_dmap {o : Option α} {f : (a : α) → (o = some a) → β} :
    (Option.dmap o f).isSome = o.isSome := by
  cases o <;> rfl

end

theorem getValueCast?_eq_getEntry? [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α} :
    getValueCast? a l = Option.dmap (getEntry? a l)
      (fun p h => cast (congrArg β (eq_of_beq (getEntry?_eq_some h))) p.2) := by
  induction l using assoc_induction
  · simp
  · next k v t ih =>
    cases h : k == a
    · rw [getValueCast?_cons_of_false h, ih, Option.dmap_congr (getEntry?_cons_of_false h)]
    · rw [getValueCast?_cons_of_true h, Option.dmap_congr (getEntry?_cons_of_true h),
        Option.dmap_some]

theorem isSome_getValueCast?_eq_isSome_getEntry? [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)}
    {a : α} : (getValueCast? a l).isSome = (getEntry? a l).isSome := by
  rw [getValueCast?_eq_getEntry?, Option.isSome_dmap]

theorem isEmpty_eq_false_iff_exists_isSome_getValueCast? [BEq α] [LawfulBEq α]
    {l : List ((a : α) × β a)} : l.isEmpty = false ↔ ∃ a, (getValueCast? a l).isSome := by
  simp [isEmpty_eq_false_iff_exists_isSome_getEntry?, isSome_getValueCast?_eq_isSome_getEntry?]

/-- Internal implementation detail of the hash map -/
def containsKey [BEq α] (a : α) : List ((a : α) × β a) → Bool
  | [] => false
  | ⟨k, _⟩ :: l => k == a || containsKey a l

@[simp] theorem containsKey_nil [BEq α] {a : α} :
    containsKey a ([] : List ((a : α) × β a)) = false := rfl
@[simp] theorem containsKey_cons [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} :
    containsKey a (⟨k, v⟩ :: l) = (k == a || containsKey a l) := rfl

theorem containsKey_cons_eq_false [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} :
    (containsKey a (⟨k, v⟩ :: l) = false) ↔ ((k == a) = false) ∧ (containsKey a l = false) := by
  simp [containsKey_cons, not_or]

theorem containsKey_cons_eq_true [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} :
    (containsKey a (⟨k, v⟩ :: l)) ↔ (k == a) ∨ (containsKey a l) := by
  simp [containsKey_cons]

theorem containsKey_cons_of_beq [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    (h : k == a) : containsKey a (⟨k, v⟩ :: l) := containsKey_cons_eq_true.2 <| Or.inl h

@[simp]
theorem containsKey_cons_self [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    containsKey k (⟨k, v⟩ :: l) := containsKey_cons_of_beq BEq.refl

theorem containsKey_cons_of_containsKey [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    (h : containsKey a l) : containsKey a (⟨k, v⟩ :: l) := containsKey_cons_eq_true.2 <| Or.inr h

theorem containsKey_of_containsKey_cons [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    (h₁ : containsKey a (⟨k, v⟩ :: l)) (h₂ : (k == a) = false) : containsKey a l := by
  rcases (containsKey_cons_eq_true.1 h₁) with (h|h)
  · exact False.elim (Bool.eq_false_iff.1 h₂ h)
  · exact h

theorem containsKey_eq_isSome_getEntry? [BEq α] {l : List ((a : α) × β a)} {a : α} :
    containsKey a l = (getEntry? a l).isSome := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · simp [getEntry?_cons_of_false h, h, ih]
    · simp [getEntry?_cons_of_true h, h]

theorem containsKey_eq_contains_map_fst [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k : α} : containsKey k l = (l.map Sigma.fst).contains k := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [containsKey_cons, ih]
    simp only [List.map_cons, List.contains_cons]
    rw [BEq.comm]

theorem isEmpty_eq_false_of_containsKey [BEq α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l = true) : l.isEmpty = false := by
  cases l <;> simp_all

theorem isEmpty_eq_false_iff_exists_containsKey [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} :
    l.isEmpty = false ↔ ∃ a, containsKey a l := by
  simp [isEmpty_eq_false_iff_exists_isSome_getEntry?, containsKey_eq_isSome_getEntry?]

theorem isEmpty_iff_forall_containsKey [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} :
    l.isEmpty ↔ ∀ a, containsKey a l = false := by
  simp only [isEmpty_iff_forall_isSome_getEntry?, containsKey_eq_isSome_getEntry?]

@[simp]
theorem getEntry?_eq_none [BEq α] {l : List ((a : α) × β a)} {a : α} :
    getEntry? a l = none ↔ containsKey a l = false := by
  rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, ← containsKey_eq_isSome_getEntry?]

@[simp]
theorem getValue?_eq_none {β : Type v} [BEq α] {l : List ((_ : α) × β)} {a : α} :
    getValue? a l = none ↔ containsKey a l = false := by
  rw [getValue?_eq_getEntry?, Option.map_eq_none', getEntry?_eq_none]

theorem containsKey_eq_isSome_getValue? {β : Type v} [BEq α] {l : List ((_ : α) × β)} {a : α} :
    containsKey a l = (getValue? a l).isSome := by
  simp [containsKey_eq_isSome_getEntry?, getValue?_eq_getEntry?]

theorem containsKey_eq_isSome_getValueCast? [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)}
    {a : α} : containsKey a l = (getValueCast? a l).isSome := by
  simp [containsKey_eq_isSome_getEntry?, getValueCast?_eq_getEntry?]

theorem getValueCast?_eq_none [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l = false) : getValueCast? a l = none := by
  rwa [← Option.not_isSome_iff_eq_none, ← containsKey_eq_isSome_getValueCast?, Bool.not_eq_true]

theorem containsKey_congr [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a b : α}
    (h : a == b) : containsKey a l = containsKey b l := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_congr h]

theorem containsKey_of_beq [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a b : α}
    (hla : containsKey a l) (hab : a == b) : containsKey b l := by
  rwa [← containsKey_congr hab]

/-- Internal implementation detail of the hash map -/
def getEntry [BEq α] (a : α) (l : List ((a : α) × β a)) (h : containsKey a l) : (a : α) × β a :=
  (getEntry? a l).get <| containsKey_eq_isSome_getEntry?.symm.trans h

theorem getEntry?_eq_some_getEntry [BEq α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l) : getEntry? a l = some (getEntry a l h) := by
  simp [getEntry]

theorem getEntry_eq_of_getEntry?_eq_some [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    (h : getEntry? a l = some ⟨k, v⟩) {h'} : getEntry a l h' = ⟨k, v⟩ := by
  simp [getEntry, h]

theorem getEntry_cons_of_beq [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} (h : k == a) :
    getEntry a (⟨k, v⟩ :: l) (containsKey_cons_of_beq (v := v) h) = ⟨k, v⟩ := by
  simp [getEntry, getEntry?_cons_of_true h]

@[simp]
theorem getEntry_cons_self [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    getEntry k (⟨k, v⟩ :: l) containsKey_cons_self = ⟨k, v⟩ :=
  getEntry_cons_of_beq BEq.refl

theorem getEntry_cons_of_false [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    {h₁ : containsKey a (⟨k, v⟩ :: l)} (h₂ : (k == a) = false) : getEntry a (⟨k, v⟩ :: l) h₁ =
      getEntry a l (containsKey_of_containsKey_cons (v := v) h₁ h₂) := by
  simp [getEntry, getEntry?_cons_of_false h₂]

section

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def getValue [BEq α] (a : α) (l : List ((_ : α) × β)) (h : containsKey a l) : β :=
  (getValue? a l).get <| containsKey_eq_isSome_getValue?.symm.trans h

theorem getValue?_eq_some_getValue [BEq α] {l : List ((_ : α) × β)} {a : α} (h : containsKey a l) :
    getValue? a l = some (getValue a l h) := by
  simp [getValue]

theorem getValue_cons_of_beq [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} (h : k == a) :
    getValue a (⟨k, v⟩ :: l) (containsKey_cons_of_beq (k := k) (v := v) h) = v := by
  simp [getValue, getValue?_cons_of_true h]

@[simp]
theorem getValue_cons_self [BEq α] [ReflBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    getValue k (⟨k, v⟩ :: l) containsKey_cons_self = v :=
  getValue_cons_of_beq BEq.refl

theorem getValue_cons_of_false [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β}
    {h₁ : containsKey a (⟨k, v⟩ :: l)} (h₂ : (k == a) = false) : getValue a (⟨k, v⟩ :: l) h₁ =
      getValue a l (containsKey_of_containsKey_cons (k := k) (v := v) h₁ h₂) := by
  simp [getValue, getValue?_cons_of_false h₂]

theorem getValue_cons [BEq α] {l : List ((_ : α) × β)} {k a : α} {v : β} {h} :
    getValue a (⟨k, v⟩ :: l) h = if h' : k == a then v
      else getValue a l (containsKey_of_containsKey_cons (k := k) h (Bool.eq_false_iff.2 h')) := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, getValue?_cons, apply_dite Option.some,
    cond_eq_if]
  split
  · rfl
  · exact getValue?_eq_some_getValue _

theorem getValue_congr [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {a b : α} (hab : a == b)
    {h} : getValue a l h = getValue b l ((containsKey_congr hab).symm.trans h) := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, ← getValue?_eq_some_getValue,
    getValue?_congr hab]

end

/-- Internal implementation detail of the hash map -/
def getValueCast [BEq α] [LawfulBEq α] (a : α) (l : List ((a : α) × β a)) (h : containsKey a l) :
    β a :=
  (getValueCast? a l).get <| containsKey_eq_isSome_getValueCast?.symm.trans h

theorem getValueCast?_eq_some_getValueCast [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l) : getValueCast? a l = some (getValueCast a l h) := by
  simp [getValueCast]

theorem Option.get_congr {o o' : Option α} {ho : o.isSome} (h : o = o') :
    o.get ho = o'.get (h ▸ ho) := by
  cases h; rfl

theorem getValueCast_cons [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    (h : containsKey a (⟨k, v⟩ :: l)) :
    getValueCast a (⟨k, v⟩ :: l) h =
      if h' : k == a then
        cast (congrArg β (eq_of_beq h')) v
      else
        getValueCast a l (containsKey_of_containsKey_cons (k := k) h (Bool.eq_false_iff.2 h')) := by
  rw [getValueCast, Option.get_congr getValueCast?_cons]
  split <;> simp [getValueCast]

theorem getValue_eq_getValueCast {β : Type v} [BEq α] [LawfulBEq α] {l : List ((_ : α) × β)} {a : α}
    {h} : getValue a l h = getValueCast a l h := by
  induction l using assoc_induction
  · simp at h
  · simp_all [getValue_cons, getValueCast_cons]

/-- Internal implementation detail of the hash map -/
def getValueCastD [BEq α] [LawfulBEq α] (a : α) (l : List ((a : α) × β a)) (fallback : β a) : β a :=
  (getValueCast? a l).getD fallback

@[simp]
theorem getValueCastD_nil [BEq α] [LawfulBEq α] {a : α} {fallback : β a} :
  getValueCastD a ([] : List ((a : α) × β a)) fallback = fallback := rfl

theorem getValueCastD_eq_getValueCast? [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    {fallback : β a} : getValueCastD a l fallback = (getValueCast? a l).getD fallback := rfl

theorem getValueCastD_eq_fallback [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    {fallback : β a} (h : containsKey a l = false) : getValueCastD a l fallback = fallback := by
  rw [containsKey_eq_isSome_getValueCast?, Bool.eq_false_iff, ne_eq,
    Option.not_isSome_iff_eq_none] at h
  rw [getValueCastD_eq_getValueCast?, h, Option.getD_none]

theorem getValueCast_eq_getValueCastD [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    {fallback : β a} (h : containsKey a l = true) :
    getValueCast a l h = getValueCastD a l fallback := by
  rw [getValueCastD_eq_getValueCast?, getValueCast, Option.get_eq_getD]

theorem getValueCast?_eq_some_getValueCastD [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    {fallback : β a} (h : containsKey a l = true) :
    getValueCast? a l = some (getValueCastD a l fallback) := by
  rw [getValueCast?_eq_some_getValueCast h, getValueCast_eq_getValueCastD]

/-- Internal implementation detail of the hash map -/
def getValueCast! [BEq α] [LawfulBEq α] (a : α) [Inhabited (β a)] (l : List ((a : α) × β a)) :
    β a :=
  (getValueCast? a l).get!

@[simp]
theorem getValueCast!_nil [BEq α] [LawfulBEq α] {a : α} [Inhabited (β a)] :
    getValueCast! a ([] : List ((a : α) × β a)) = default := rfl

theorem getValueCast!_eq_getValueCast? [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    [Inhabited (β a)] : getValueCast! a l = (getValueCast? a l).get! := rfl

theorem getValueCast!_eq_default [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    [Inhabited (β a)] (h : containsKey a l = false) : getValueCast! a l = default := by
  rw [containsKey_eq_isSome_getValueCast?, Bool.eq_false_iff, ne_eq,
    Option.not_isSome_iff_eq_none] at h
  rw [getValueCast!_eq_getValueCast?, h, Option.get!_none]

theorem getValueCast_eq_getValueCast! [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    [Inhabited (β a)] (h : containsKey a l = true) : getValueCast a l h = getValueCast! a l := by
  rw [getValueCast!_eq_getValueCast?, getValueCast, Option.get_eq_get!]

theorem getValueCast?_eq_some_getValueCast! [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    [Inhabited (β a)] (h : containsKey a l = true) :
    getValueCast? a l = some (getValueCast! a l) := by
  rw [getValueCast?_eq_some_getValueCast h, getValueCast_eq_getValueCast!]

theorem getValueCast!_eq_getValueCastD_default [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)}
    {a : α} [Inhabited (β a)] : getValueCast! a l = getValueCastD a l default := rfl

section

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def getValueD [BEq α] (a : α) (l : List ((_ : α) × β)) (fallback : β) : β :=
  (getValue? a l).getD fallback

@[simp]
theorem getValueD_nil [BEq α] {a : α} {fallback : β} :
    getValueD a ([] : List ((_ : α) × β)) fallback = fallback := rfl

theorem getValueD_eq_getValue? [BEq α] {l : List ((_ : α) × β)} {a : α} {fallback : β} :
    getValueD a l fallback = (getValue? a l).getD fallback := rfl

theorem getValueD_eq_fallback [BEq α] {l : List ((_ : α) × β)} {a : α} {fallback : β}
    (h : containsKey a l = false) : getValueD a l fallback = fallback := by
  rw [containsKey_eq_isSome_getValue?, Bool.eq_false_iff, ne_eq, Option.not_isSome_iff_eq_none] at h
  rw [getValueD_eq_getValue?, h, Option.getD_none]

theorem getValue_eq_getValueD [BEq α] {l : List ((_ : α) × β)} {a : α} {fallback : β}
    (h : containsKey a l = true) : getValue a l h = getValueD a l fallback := by
  rw [getValueD_eq_getValue?, getValue, Option.get_eq_getD]

theorem getValue?_eq_some_getValueD [BEq α] {l : List ((_ : α) × β)} {a : α} {fallback : β}
    (h : containsKey a l = true) : getValue? a l = some (getValueD a l fallback) := by
  rw [getValue?_eq_some_getValue h, getValue_eq_getValueD]

theorem getValueD_eq_getValueCastD [BEq α] [LawfulBEq α] {l : List ((_ : α) × β)} {a : α}
    {fallback : β} : getValueD a l fallback = getValueCastD a l fallback := by
  simp only [getValueD_eq_getValue?, getValueCastD_eq_getValueCast?, getValue?_eq_getValueCast?]

theorem getValueD_congr [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {a b : α}
    {fallback : β} (hab : a == b) : getValueD a l fallback = getValueD b l fallback := by
  simp only [getValueD_eq_getValue?, getValue?_congr hab]

/-- Internal implementation detail of the hash map -/
def getValue! [BEq α] [Inhabited β] (a : α) (l : List ((_ : α) × β)) : β :=
  (getValue? a l).get!

@[simp]
theorem getValue!_nil [BEq α] [Inhabited β] {a : α} :
    getValue! a ([] : List ((_ : α) × β)) = default := rfl

theorem getValue!_eq_getValue? [BEq α] [Inhabited β] {l : List ((_ : α) × β)} {a : α} :
    getValue! a l = (getValue? a l).get! := rfl

theorem getValue!_eq_default [BEq α] [Inhabited β] {l : List ((_ : α) × β)} {a : α}
    (h : containsKey a l = false) : getValue! a l = default := by
  rw [containsKey_eq_isSome_getValue?, Bool.eq_false_iff, ne_eq, Option.not_isSome_iff_eq_none] at h
  rw [getValue!_eq_getValue?, h, Option.get!_none]

theorem getValue_eq_getValue! [BEq α] [Inhabited β] {l : List ((_ : α) × β)} {a : α}
    (h : containsKey a l = true) : getValue a l h = getValue! a l := by
  rw [getValue!_eq_getValue?, getValue, Option.get_eq_get!]

theorem getValue?_eq_some_getValue! [BEq α] [Inhabited β] {l : List ((_ : α) × β)} {a : α}
    (h : containsKey a l = true) : getValue? a l = some (getValue! a l) := by
  rw [getValue?_eq_some_getValue h, getValue_eq_getValue!]

theorem getValue!_eq_getValueCast! [BEq α] [LawfulBEq α] [Inhabited β] {l : List ((_ : α) × β)}
    {a : α} : getValue! a l = getValueCast! a l := by
  simp only [getValue!_eq_getValue?, getValueCast!_eq_getValueCast?, getValue?_eq_getValueCast?]

theorem getValue!_congr [BEq α] [PartialEquivBEq α] [Inhabited β] {l : List ((_ : α) × β)} {a b : α}
    (hab : a == b) : getValue! a l = getValue! b l := by
  simp only [getValue!_eq_getValue?, getValue?_congr hab]

theorem getValue!_eq_getValueD_default [BEq α] [Inhabited β] {l : List ((_ : α) × β)} {a : α} :
    getValue! a l = getValueD a l default := rfl

end

/-- Internal implementation detail of the hash map -/
def getKey? [BEq α] (a : α) : List ((a : α) × β a) → Option α
  | [] => none
  | ⟨k, _⟩ :: l => bif k == a then some k else getKey? a l

@[simp] theorem getKey?_nil [BEq α] {a : α} :
    getKey? a ([] : List ((a : α) × β a)) = none := rfl

@[simp] theorem getKey?_cons [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} :
    getKey? a (⟨k, v⟩ :: l) = bif k == a then some k else getKey? a l := rfl

theorem getKey?_cons_of_true [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} (h : k == a) :
    getKey? a (⟨k, v⟩ :: l) = some k := by
  simp [h]

theorem getKey?_cons_of_false [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k}
    (h : (k == a) = false) : getKey? a (⟨k, v⟩ :: l) = getKey? a l := by
  simp [h]

theorem getKey?_eq_getEntry? [BEq α] {l : List ((a : α) × β a)} {a : α} :
    getKey? a l = (getEntry? a l).map (·.1) := by
  induction l using assoc_induction
  · simp
  · next k v l ih =>
    cases h : k == a
    · rw [getEntry?_cons_of_false h, getKey?_cons_of_false h, ih]
    · rw [getEntry?_cons_of_true h, getKey?_cons_of_true h, Option.map_some']

theorem containsKey_eq_isSome_getKey? [BEq α] {l : List ((a : α) × β a)} {a : α} :
    containsKey a l = (getKey? a l).isSome := by
  simp [containsKey_eq_isSome_getEntry?, getKey?_eq_getEntry?]

/-- Internal implementation detail of the hash map -/
def getKey [BEq α] (a : α) (l : List ((a : α) × β a)) (h : containsKey a l) : α :=
  (getKey? a l).get <| containsKey_eq_isSome_getKey?.symm.trans h

theorem getKey?_eq_some_getKey [BEq α] {l : List ((a : α) × β a)} {a : α} (h : containsKey a l) :
    getKey? a l = some (getKey a l h) := by
  simp [getKey]

theorem getKey_cons [BEq α] {l : List ((a : α) × β a)} {k a : α} {v : β k} {h} :
    getKey a (⟨k, v⟩ :: l) h = if h' : k == a then k
      else getKey a l (containsKey_of_containsKey_cons (k := k) h (Bool.eq_false_iff.2 h')) := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey, getKey?_cons, apply_dite Option.some,
    cond_eq_if]
  split
  · rfl
  · exact getKey?_eq_some_getKey _

/-- Internal implementation detail of the hash map -/
def getKeyD [BEq α] (a : α) (l : List ((a : α) × β a)) (fallback : α) : α :=
  (getKey? a l).getD fallback

@[simp]
theorem getKeyD_nil [BEq α] {a fallback : α} :
  getKeyD a ([] : List ((a : α) × β a)) fallback = fallback := rfl

theorem getKeyD_eq_getKey? [BEq α] {l : List ((a : α) × β a)} {a fallback : α} :
  getKeyD a l fallback = (getKey? a l).getD fallback := rfl

theorem getKeyD_eq_fallback [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {a fallback : α}
    (h : containsKey a l = false) : getKeyD a l fallback = fallback := by
  rw [containsKey_eq_isSome_getKey?, Bool.eq_false_iff, ne_eq,
    Option.not_isSome_iff_eq_none] at h
  rw [getKeyD_eq_getKey?, h, Option.getD_none]

theorem getKey_eq_getKeyD [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {a fallback : α}
    (h : containsKey a l = true) :
    getKey a l h = getKeyD a l fallback := by
  rw [getKeyD_eq_getKey?, getKey, Option.get_eq_getD]

theorem getKey?_eq_some_getKeyD [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {a fallback : α}
    (h : containsKey a l = true) :
    getKey? a l = some (getKeyD a l fallback) := by
  rw [getKey?_eq_some_getKey h, getKey_eq_getKeyD]

/-- Internal implementation detail of the hash map -/
def getKey! [BEq α] [Inhabited α] (a : α) (l : List ((a : α) × β a)) : α :=
  (getKey? a l).get!

@[simp]
theorem getKey!_nil [BEq α] [Inhabited α] {a : α} :
    getKey! a ([] : List ((a : α) × β a)) = default := rfl

theorem getKey!_eq_getKey? [BEq α] [Inhabited α] {l : List ((a : α) × β a)} {a : α} :
    getKey! a l = (getKey? a l).get! := rfl

theorem getKey!_eq_default [BEq α] [Inhabited α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l = false) : getKey! a l = default := by
  rw [containsKey_eq_isSome_getKey?, Bool.eq_false_iff, ne_eq,
    Option.not_isSome_iff_eq_none] at h
  rw [getKey!_eq_getKey?, h, Option.get!_none]

theorem getKey_eq_getKey! [BEq α] [Inhabited α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l = true) : getKey a l h = getKey! a l := by
  rw [getKey!_eq_getKey?, getKey, Option.get_eq_get!]

theorem getKey?_eq_some_getKey! [BEq α] [Inhabited α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l = true) :
    getKey? a l = some (getKey! a l) := by
  rw [getKey?_eq_some_getKey h, getKey_eq_getKey!]

theorem getKey!_eq_getKeyD_default [BEq α] [EquivBEq α] [Inhabited α] {l : List ((a : α) × β a)}
    {a : α} : getKey! a l = getKeyD a l default := rfl

/-- Internal implementation detail of the hash map -/
def replaceEntry [BEq α] (k : α) (v : β k) : List ((a : α) × β a) → List ((a : α) × β a)
  | [] => []
  | ⟨k', v'⟩ :: l => bif k' == k then ⟨k, v⟩ :: l else ⟨k', v'⟩ :: replaceEntry k v l

@[simp] theorem replaceEntry_nil [BEq α] {k : α} {v : β k} : replaceEntry k v [] = [] := rfl
theorem replaceEntry_cons [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v : β k} {v' : β k'} :
    replaceEntry k v (⟨k', v'⟩ :: l) =
      bif k' == k then ⟨k, v⟩ :: l else ⟨k', v'⟩ :: replaceEntry k v l := rfl

theorem replaceEntry_cons_of_true [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v : β k}
    {v' : β k'} (h : k' == k) : replaceEntry k v (⟨k', v'⟩ :: l) = ⟨k, v⟩ :: l := by
  simp [replaceEntry, h]

theorem replaceEntry_cons_of_false [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v : β k}
    {v' : β k'} (h : (k' == k) = false) :
    replaceEntry k v (⟨k', v'⟩ :: l) = ⟨k', v'⟩ :: replaceEntry k v l := by
  simp [replaceEntry, h]

theorem replaceEntry_of_containsKey_eq_false [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l = false) : replaceEntry k v l = l := by
  induction l
  · simp
  · next k v l ih =>
    rw [containsKey_cons_eq_false] at h
    rw [replaceEntry_cons_of_false h.1, ih h.2]

@[simp]
theorem isEmpty_replaceEntry [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (replaceEntry k v l).isEmpty = l.isEmpty := by
  induction l using assoc_induction
  · simp
  · simp only [replaceEntry_cons, cond_eq_if, List.isEmpty_cons]
    split <;> simp

theorem mem_replaceEntry_of_beq_eq_false [BEq α] [EquivBEq α] {a : α} {b : β a}
    {l : List ((a : α) × β a)} (p : (a : α) × β a) (hne : (p.1 == a) = false) :
    p ∈ replaceEntry a b l ↔ p ∈ l := by
  induction l
  · simp only [replaceEntry_nil]
  · next ih =>
    simp only [replaceEntry, cond_eq_if]
    split
    · next h =>
      simp only [List.mem_cons, Sigma.ext_iff]
      apply Iff.intro <;> exact fun
      | Or.inr y => Or.inr y
      | Or.inl y => by simp_all only [BEq.refl, Bool.true_eq_false]
    · simp only [List.mem_cons, ih]

theorem mem_replaceEntry_of_key_ne [BEq α] [LawfulBEq α] {a : α} {b : β a}
    {l : List ((a : α) × β a)} (p : (a : α) × β a) (hne : p.1 ≠ a) :
    p ∈ replaceEntry a b l ↔ p ∈ l :=
  mem_replaceEntry_of_beq_eq_false p <| beq_false_of_ne hne

theorem getEntry?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List ((a : α) × β a)} {a k : α}
    {v : β k} (hl : containsKey k l = false) :
    getEntry? a (replaceEntry k v l) = getEntry? a l := by
  rw [replaceEntry_of_containsKey_eq_false hl]

theorem getEntry?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {a k : α} {v : β k} (h : (k == a) = false) :
    getEntry? a (replaceEntry k v l) = getEntry? a l := by
  induction l using assoc_induction
  · simp
  · next k' v' l ih =>
    cases h' : k' == k
    · rw [replaceEntry_cons_of_false h', getEntry?_cons, getEntry?_cons, ih]
    · rw [replaceEntry_cons_of_true h']
      have hk : (k' == a) = false := BEq.neq_of_beq_of_neq h' h
      simp only [getEntry?_cons_of_false h, getEntry?_cons_of_false hk]

theorem getEntry?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {a k : α} {v : β k} (hl : containsKey k l = true) (h : k == a) :
    getEntry? a (replaceEntry k v l) = some ⟨k, v⟩ := by
  induction l using assoc_induction
  · simp at hl
  · next k' v' l ih =>
    cases hk'a : k' == k
    · rw [replaceEntry_cons_of_false hk'a]
      have hk'k : (k' == a) = false := BEq.neq_of_neq_of_beq hk'a h
      rw [getEntry?_cons_of_false hk'k]
      exact ih (containsKey_of_containsKey_cons hl hk'a)
    · rw [replaceEntry_cons_of_true hk'a, getEntry?_cons_of_true h]

theorem getEntry?_replaceEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a k : α}
    {v : β k} :
    getEntry? a (replaceEntry k v l) = if containsKey k l ∧ k == a then some ⟨k, v⟩ else
      getEntry? a l := by
  cases hl : containsKey k l
  · simp [getEntry?_replaceEntry_of_containsKey_eq_false hl]
  · cases h : k == a
    · simp [getEntry?_replaceEntry_of_false h]
    · simp [getEntry?_replaceEntry_of_true hl h]

@[simp]
theorem length_replaceEntry [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (replaceEntry k v l).length = l.length := by
  induction l using assoc_induction <;> simp_all [replaceEntry_cons, Bool.apply_cond List.length]

section

variable {β : Type v}

theorem getValue?_replaceEntry_of_containsKey_eq_false [BEq α] {l : List ((_ : α) × β)} {k a : α}
    {v : β} (hl : containsKey k l = false) : getValue? a (replaceEntry k v l) = getValue? a l := by
  simp [getValue?_eq_getEntry?, getEntry?_replaceEntry_of_containsKey_eq_false hl]

theorem getValue?_replaceEntry_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {v : β} (h : (k == a) = false) :
    getValue? a (replaceEntry k v l) = getValue? a l := by
  simp [getValue?_eq_getEntry?, getEntry?_replaceEntry_of_false h]

theorem getValue?_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {v : β} (hl : containsKey k l = true) (h : k == a) :
    getValue? a (replaceEntry k v l) = some v := by
  simp [getValue?_eq_getEntry?, getEntry?_replaceEntry_of_true hl h]

end

theorem getValueCast?_replaceEntry [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a k : α}
    {v : β k} : getValueCast? a (replaceEntry k v l) =
      if h : containsKey k l ∧ k == a then some (cast (congrArg β (eq_of_beq h.2)) v)
        else getValueCast? a l := by
  rw [getValueCast?_eq_getEntry?]
  split
  · next h =>
    rw [Option.dmap_congr (getEntry?_replaceEntry_of_true h.1 h.2), Option.dmap_some]
  · next h =>
    simp only [Decidable.not_and_iff_or_not_not] at h
    rcases h with h|h
    · rw [Option.dmap_congr
          (getEntry?_replaceEntry_of_containsKey_eq_false (Bool.eq_false_iff.2 h)),
        getValueCast?_eq_getEntry?]
    · rw [Option.dmap_congr (getEntry?_replaceEntry_of_false (Bool.eq_false_iff.2 h)),
        getValueCast?_eq_getEntry?]

theorem getKey?_replaceEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a k : α}
    {v : β k} : getKey? a (replaceEntry k v l) =
      if containsKey k l ∧ k == a then some k else getKey? a l := by
  rw [getKey?_eq_getEntry?]
  split
  · next h => simp [getEntry?_replaceEntry_of_true h.1 h.2]
  · next h =>
    simp only [Decidable.not_and_iff_or_not_not] at h
    rcases h with h|h
    · rw [getEntry?_replaceEntry_of_containsKey_eq_false (Bool.eq_false_iff.2 h), getKey?_eq_getEntry?]
    · rw [getEntry?_replaceEntry_of_false (Bool.eq_false_iff.2 h), getKey?_eq_getEntry?]

@[simp]
theorem containsKey_replaceEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a k : α}
    {v : β k} : containsKey a (replaceEntry k v l) = containsKey a l := by
  by_cases h : (getEntry? k l).isSome ∧ k == a
  · simp only [containsKey_eq_isSome_getEntry?, getEntry?_replaceEntry, h, and_self, ↓reduceIte,
      Option.isSome_some, Bool.true_eq]
    rw [← getEntry?_congr h.2, h.1]
  · simp [containsKey_eq_isSome_getEntry?, getEntry?_replaceEntry, h]

/-- Internal implementation detail of the hash map -/
def eraseKey [BEq α] (k : α) : List ((a : α) × β a) → List ((a : α) × β a)
  | [] => []
  | ⟨k', v'⟩ :: l => bif k' == k then l else ⟨k', v'⟩ :: eraseKey k l

@[simp] theorem eraseKey_nil [BEq α] {k : α} : eraseKey k ([] : List ((a : α) × β a)) = [] := rfl

theorem eraseKey_cons [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v' : β k'} :
    eraseKey k (⟨k', v'⟩ :: l) = bif k' == k then l else ⟨k', v'⟩ :: eraseKey k l := rfl

theorem eraseKey_cons_of_beq [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v' : β k'}
    (h : k' == k) : eraseKey k (⟨k', v'⟩ :: l) = l :=
  by simp [eraseKey_cons, h]

@[simp]
theorem eraseKey_cons_self [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    eraseKey k (⟨k, v⟩ :: l) = l :=
  eraseKey_cons_of_beq BEq.refl

theorem eraseKey_cons_of_false [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v' : β k'}
    (h : (k' == k) = false) : eraseKey k (⟨k', v'⟩ :: l) = ⟨k', v'⟩ :: eraseKey k l := by
  simp [eraseKey_cons, h]

theorem eraseKey_of_containsKey_eq_false [BEq α] {l : List ((a : α) × β a)} {k : α}
    (h : containsKey k l = false) : eraseKey k l = l := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_false_iff] at h
    rw [eraseKey_cons_of_false h.1, ih h.2]

theorem mem_eraseKey_of_key_beq_eq_false [BEq α] {a : α}
    {l : List ((a : α) × β a)} (p : (a : α) × β a) (hne : (p.1 == a) = false) :
    p ∈ eraseKey a l ↔ p ∈ l := by
  induction l
  · simp only [eraseKey_nil]
  · next ih =>
    simp only [eraseKey, List.mem_cons]
    rw [cond_eq_if]
    split
    · next h =>
      rw [iff_or_self, Sigma.ext_iff]
      intro ⟨h₁, h₂⟩
      rw [h₁, h] at hne
      contradiction
    · next h =>
      simp only [List.mem_cons, ih]

theorem mem_eraseKey_of_key_ne [BEq α] [LawfulBEq α] {a : α}
    {l : List ((a : α) × β a)} (p : (a : α) × β a) (hne : p.1 ≠ a) : p ∈ eraseKey a l ↔ p ∈ l :=
  mem_eraseKey_of_key_beq_eq_false p <| beq_false_of_ne hne

theorem sublist_eraseKey [BEq α] {l : List ((a : α) × β a)} {k : α} :
    Sublist (eraseKey k l) l := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    rw [eraseKey_cons]
    cases k' == k
    · simpa
    · simp

theorem length_eraseKey [BEq α] {l : List ((a : α) × β a)} {k : α} :
    (eraseKey k l).length = if containsKey k l then l.length - 1 else l.length := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    rw [eraseKey_cons, containsKey_cons]
    cases k' == k
    · rw [cond_false, Bool.false_or, List.length_cons, ih]
      cases h : containsKey k t
      · simp
      · simp only [Nat.succ_eq_add_one, List.length_cons, Nat.add_sub_cancel, if_true]
        rw [Nat.sub_add_cancel]
        cases t
        · simp at h
        · simp
    · simp

theorem length_eraseKey_le [BEq α] {l : List ((a : α) × β a)} {k : α} :
    (eraseKey k l).length ≤ l.length :=
  sublist_eraseKey.length_le

theorem length_le_length_eraseKey [BEq α] {l : List ((a : α) × β a)} {k : α} :
    l.length ≤ (eraseKey k l).length + 1 := by
  rw [length_eraseKey]
  split <;> omega

theorem isEmpty_eraseKey [BEq α] {l : List ((a : α) × β a)} {k : α} :
    (eraseKey k l).isEmpty = (l.isEmpty || (l.length == 1 && containsKey k l)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rw [List.isEmpty_iff_length_eq_zero, length_eraseKey, List.isEmpty_iff_length_eq_zero]
  cases containsKey k l <;> cases l <;> simp

@[simp] theorem keys_nil : keys ([] : List ((a : α) × β a)) = [] := rfl
@[simp] theorem keys_cons {l : List ((a : α) × β a)} {k : α} {v : β k} :
    keys (⟨k, v⟩ :: l) = k :: keys l := rfl

theorem keys_eq_map (l : List ((a : α) × β a)) : keys l = l.map (·.1) := by
  induction l using assoc_induction <;> simp_all

theorem length_keys_eq_length (l : List ((a : α) × β a)) : (keys l).length = l.length := by
  induction l using assoc_induction <;> simp_all

theorem isEmpty_keys_eq_isEmpty (l : List ((a : α) × β a)) : (keys l).isEmpty = l.isEmpty := by
  induction l using assoc_induction <;> simp_all

theorem containsKey_eq_keys_contains [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {a : α} : containsKey a l = (keys l).contains a := by
  induction l using assoc_induction
  · rfl
  · next k _ l ih => simp [ih, BEq.comm]

theorem containsKey_eq_true_iff_exists_mem [BEq α] {l : List ((a : α) × β a)} {a : α} :
    containsKey a l = true ↔ ∃ p ∈ l, p.1 == a := by
  induction l using assoc_induction <;> simp_all

theorem containsKey_of_mem [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} {p : (a : α) × β a}
    (hp : p ∈ l) : containsKey p.1 l :=
  containsKey_eq_true_iff_exists_mem.2 ⟨p, ⟨hp, BEq.refl⟩⟩

@[simp]
theorem DistinctKeys.nil [BEq α] : DistinctKeys ([] : List ((a : α) × β a)) :=
  ⟨by simp⟩

theorem DistinctKeys.def [BEq α] {l : List ((a : α) × β a)} :
    DistinctKeys l ↔ l.Pairwise (fun a b => (a.1 == b.1) = false) :=
  ⟨fun h => by simpa [keys_eq_map, List.pairwise_map] using h.distinct,
   fun h => ⟨by simpa [keys_eq_map, List.pairwise_map] using h⟩⟩

open List

theorem DistinctKeys.perm_keys [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)}
    (h : Perm (keys l') (keys l)) : DistinctKeys l → DistinctKeys l'
  | ⟨h'⟩ => ⟨h'.perm h.symm BEq.symm_false⟩

theorem DistinctKeys.perm [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)}
    (h : Perm l' l) : DistinctKeys l → DistinctKeys l' :=
  DistinctKeys.perm_keys (by simpa only [keys_eq_map] using h.map _)

theorem DistinctKeys.congr [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)}
    (h : Perm l l') : DistinctKeys l ↔ DistinctKeys l' :=
  ⟨fun h' => h'.perm h.symm, fun h' => h'.perm h⟩

theorem distinctKeys_of_sublist_keys [BEq α] {l : List ((a : α) × β a)} {l' : List ((a : α) × γ a)}
    (h : Sublist (keys l') (keys l)) : DistinctKeys l → DistinctKeys l' :=
  fun ⟨h'⟩ => ⟨h'.sublist h⟩

theorem distinctKeys_of_sublist [BEq α] {l l' : List ((a : α) × β a)} (h : Sublist l' l) :
    DistinctKeys l → DistinctKeys l' :=
  distinctKeys_of_sublist_keys (by simpa only [keys_eq_map] using h.map _)

theorem DistinctKeys.of_keys_eq [BEq α] {l : List ((a : α) × β a)} {l' : List ((a : α) × γ a)}
    (h : keys l = keys l') : DistinctKeys l → DistinctKeys l' :=
  distinctKeys_of_sublist_keys (h ▸ Sublist.refl _)

theorem containsKey_iff_exists [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a : α} :
    containsKey a l ↔ ∃ a' ∈ keys l, a == a' := by
  rw [containsKey_eq_keys_contains, List.contains_iff_exists_mem_beq]

theorem containsKey_eq_false_iff_forall_mem_keys [BEq α] [PartialEquivBEq α]
    {l : List ((a : α) × β a)} {a : α} :
    (containsKey a l) = false ↔ ∀ a' ∈ keys l, (a == a') = false := by
  simp only [Bool.eq_false_iff, ne_eq, containsKey_iff_exists, not_exists, not_and]

theorem containsKey_eq_false_iff [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a : α} :
    containsKey a l = false ↔ ∀ (b : ((a : α) × β a)), b ∈ l → (a == b.fst) = false := by
  simp [containsKey_eq_false_iff_forall_mem_keys, keys_eq_map]

@[simp]
theorem distinctKeys_cons_iff [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} : DistinctKeys (⟨k, v⟩ :: l) ↔ DistinctKeys l ∧ (containsKey k l) = false := by
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨⟨h₁⟩, h₂⟩ => ⟨?_⟩⟩
  · rw [keys_cons, pairwise_cons] at h
    exact ⟨⟨h.2⟩, containsKey_eq_false_iff_forall_mem_keys.2 h.1⟩
  · rw [keys_cons, pairwise_cons, ← containsKey_eq_false_iff_forall_mem_keys]
    exact ⟨h₂, h₁⟩

theorem DistinctKeys.tail [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    DistinctKeys (⟨k, v⟩ :: l) → DistinctKeys l :=
  fun h => (distinctKeys_cons_iff.mp h).1

theorem DistinctKeys.containsKey_eq_false [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k : α} {v : β k} : DistinctKeys (⟨k, v⟩ :: l) → containsKey k l = false :=
  fun h => (distinctKeys_cons_iff.mp h).2

theorem DistinctKeys.cons [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l = false) : DistinctKeys l → DistinctKeys (⟨k, v⟩ :: l) :=
  fun h' => distinctKeys_cons_iff.mpr ⟨h', h⟩

theorem mem_iff_getEntry?_eq_some [BEq α] [EquivBEq α] {l : List ((a : α) × β a)}
    {p : (a : α) × β a} (h : DistinctKeys l) : p ∈ l ↔ getEntry? p.1 l = some p := by
  induction l using assoc_induction
  · simp_all
  · next k v t ih =>
    simp only [List.mem_cons, getEntry?_cons, ih h.tail]
    refine ⟨?_, ?_⟩
    · rintro (rfl|hk)
      · simp
      · suffices (k == p.fst) = false by simp_all
        refine Bool.eq_false_iff.2 fun hcon => Bool.false_ne_true ?_
        rw [← h.containsKey_eq_false, containsKey_congr hcon,
          containsKey_eq_isSome_getEntry?, hk, Option.isSome_some]
    · cases k == p.fst
      · rw [cond_false]
        exact Or.inr
      · rw [cond_true, Option.some.injEq]
        exact Or.inl ∘ Eq.symm

theorem DistinctKeys.replaceEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} (h : DistinctKeys l) : DistinctKeys (replaceEntry k v l) := by
  induction l using assoc_induction
  · simp
  · next k' v' l ih =>
    rw [distinctKeys_cons_iff] at h
    cases hk'k : k' == k
    · rw [replaceEntry_cons_of_false hk'k, distinctKeys_cons_iff]
      refine ⟨ih h.1, ?_⟩
      simpa using h.2
    · rw [replaceEntry_cons_of_true hk'k, distinctKeys_cons_iff]
      refine ⟨h.1, ?_⟩
      simpa [containsKey_congr (BEq.symm hk'k)] using h.2

theorem getEntry?_of_mem [BEq α] [PartialEquivBEq α]
    {l : List ((a : α) × β a)} (hl : DistinctKeys l)
    {k k' : α} (hk : k == k') {v : β k} (hkv : ⟨k, v⟩ ∈ l) :
    getEntry? k' l = some ⟨k, v⟩ := by
  induction l using assoc_induction with
  | nil => simp at hkv
  | cons k₁ v₁ t ih =>
    obtain ⟨⟨⟩⟩|hkv := List.mem_cons.1 hkv
    · rw [getEntry?_cons_of_true hk]
    · rw [getEntry?_cons_of_false, ih hl.tail hkv]
      exact BEq.neq_of_neq_of_beq (containsKey_eq_false_iff.1 hl.containsKey_eq_false _ hkv) hk

/-- Internal implementation detail of the hash map -/
def insertEntry [BEq α]  (k : α) (v : β k) (l : List ((a : α) × β a)) : List ((a : α) × β a) :=
  bif containsKey k l then replaceEntry k v l else ⟨k, v⟩ :: l

@[simp]
theorem insertEntry_nil [BEq α] {k : α} {v : β k} :
    insertEntry k v ([] : List ((a : α) × β a)) = [⟨k, v⟩] :=
  by simp [insertEntry]

theorem insertEntry_cons_of_false [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v : β k}
    {v' : β k'} (h : (k' == k) = false) :
    Perm (insertEntry k v (⟨k', v'⟩ :: l)) (⟨k', v'⟩ :: insertEntry k v l) := by
  simp only [insertEntry, containsKey_cons, h, Bool.false_or, cond_eq_if]
  split
  · rw [replaceEntry_cons_of_false h]
  · apply Perm.swap

theorem insertEntry_cons_of_beq [BEq α] {l : List ((a : α) × β a)} {k k' : α} {v : β k} {v' : β k'}
    (h : k' == k) : insertEntry k v (⟨k', v'⟩ :: l) = ⟨k, v⟩ :: l := by
  simp_all only [insertEntry, containsKey_cons, Bool.true_or, cond_true, replaceEntry_cons_of_true]

@[simp]
theorem insertEntry_cons_self [BEq α] [ReflBEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    insertEntry k v (⟨k, v⟩ :: l) = ⟨k, v⟩ :: l :=
  insertEntry_cons_of_beq BEq.refl

theorem insertEntry_of_containsKey [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l) : insertEntry k v l = replaceEntry k v l := by
  simp [insertEntry, h]

theorem insertEntry_of_containsKey_eq_false [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l = false) : insertEntry k v l = ⟨k, v⟩ :: l := by
  simp [insertEntry, h]

theorem mem_insertEntry_of_key_beq_eq_false [BEq α] [EquivBEq α] {a : α} {b : β a}
    {l : List ((a : α) × β a)} (p : (a : α) × β a)
    (hne : (p.1 == a) = false) : p ∈ insertEntry a b l ↔ p ∈ l := by
  simp only [insertEntry, cond_eq_if]
  split
  · exact mem_replaceEntry_of_beq_eq_false p hne
  · simp only [List.mem_cons, or_iff_right_iff_imp, Sigma.ext_iff]
    rw [← Bool.not_eq_true] at hne
    exact fun x => hne (beq_of_eq x.1) |> False.elim

theorem mem_insertEntry_of_key_ne [BEq α] [LawfulBEq α] {a : α} {b : β a}
    {l : List ((a : α) × β a)} (p : (a : α) × β a)
    (hne : p.1 ≠ a) : p ∈ insertEntry a b l ↔ p ∈ l :=
  mem_insertEntry_of_key_beq_eq_false p <| beq_false_of_ne hne

theorem DistinctKeys.insertEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} (h : DistinctKeys l) : DistinctKeys (insertEntry k v l) := by
  cases h' : containsKey k l
  · rw [insertEntry_of_containsKey_eq_false h', distinctKeys_cons_iff]
    exact ⟨h, h'⟩
  · rw [insertEntry_of_containsKey h']
    exact h.replaceEntry

@[simp]
theorem isEmpty_insertEntry [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (insertEntry k v l).isEmpty = false := by
  cases h : containsKey k l
  · simp [insertEntry_of_containsKey_eq_false h]
  · rw [insertEntry_of_containsKey h, isEmpty_replaceEntry, isEmpty_eq_false_of_containsKey h]

theorem length_insertEntry [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (insertEntry k v l).length = if containsKey k l then l.length else l.length + 1 := by
  simp [insertEntry, Bool.apply_cond List.length]

theorem length_le_length_insertEntry [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    l.length ≤ (insertEntry k v l).length := by
  rw [length_insertEntry]
  split <;> omega

theorem length_insertEntry_le [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (insertEntry k v l).length ≤ l.length + 1 := by
  rw [length_insertEntry]
  split <;> omega

section

variable {β : Type v}

theorem getValue?_insertEntry_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    {v : β} (h : k == a) : getValue? a (insertEntry k v l) = some v := by
  cases h' : containsKey k l
  · rw [insertEntry_of_containsKey_eq_false h', getValue?_cons_of_true h]
  · rw [insertEntry_of_containsKey h', getValue?_replaceEntry_of_true h' h]

theorem getValue?_insertEntry_of_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α}
    {v : β} : getValue? k (insertEntry k v l) = some v :=
  getValue?_insertEntry_of_beq BEq.refl

theorem getValue?_insertEntry_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {v : β} (h : (k == a) = false) : getValue? a (insertEntry k v l) = getValue? a l := by
  cases h' : containsKey k l
  · rw [insertEntry_of_containsKey_eq_false h', getValue?_cons_of_false h]
  · rw [insertEntry_of_containsKey h', getValue?_replaceEntry_of_false h]

theorem getValue?_insertEntry [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    {v : β} : getValue? a (insertEntry k v l) = if k == a then some v else getValue? a l := by
  cases h : k == a
  · simp [getValue?_insertEntry_of_false h, h]
  · simp [getValue?_insertEntry_of_beq h, h]

theorem getValue?_insertEntry_self [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α} {v : β} :
    getValue? k (insertEntry k v l) = some v := by
  simp [getValue?_insertEntry]

end

theorem getEntry?_insertEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} :
    getEntry? a (insertEntry k v l) = if k == a then some ⟨k, v⟩ else getEntry? a l := by
  cases hl : containsKey k l
  · rw [insertEntry_of_containsKey_eq_false hl, getEntry?_cons, cond_eq_if]
  · simp [insertEntry_of_containsKey hl, getEntry?_replaceEntry, hl]

theorem getValueCast?_insertEntry [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} : getValueCast? a (insertEntry k v l) =
      if h : k == a then some (cast (congrArg β (eq_of_beq h)) v) else getValueCast? a l := by
  cases hl : containsKey k l
  · rw [insertEntry_of_containsKey_eq_false hl, getValueCast?_cons]
  · rw [insertEntry_of_containsKey hl, getValueCast?_replaceEntry, hl]
    split <;> simp_all

theorem getValueCast?_insertEntry_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} : getValueCast? k (insertEntry k v l) = some v := by
  rw [getValueCast?_insertEntry, dif_pos BEq.refl, cast_eq]

theorem getValueCast!_insertEntry [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    [Inhabited (β a)] {v : β k} : getValueCast! a (insertEntry k v l) =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v else getValueCast! a l := by
  simp [getValueCast!_eq_getValueCast?, getValueCast?_insertEntry, apply_dite Option.get!]

theorem getValueCast!_insertEntry_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α}
    [Inhabited (β k)] {v : β k} : getValueCast! k (insertEntry k v l) = v := by
  rw [getValueCast!_insertEntry, dif_pos BEq.refl, cast_eq]

theorem getValueCastD_insertEntry [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {fallback : β a} {v : β k} : getValueCastD a (insertEntry k v l) fallback =
      if h : k == a then cast (congrArg β (eq_of_beq h)) v
      else getValueCastD a l fallback := by
  simp [getValueCastD_eq_getValueCast?, getValueCast?_insertEntry,
    apply_dite (fun x => Option.getD x fallback)]

theorem getValueCastD_insertEntry_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α}
    {fallback : β k} {v : β k} : getValueCastD k (insertEntry k v l) fallback = v := by
  rw [getValueCastD_insertEntry, dif_pos BEq.refl, cast_eq]

theorem getValue!_insertEntry {β : Type v} [BEq α] [PartialEquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {k a : α} {v : β} :
    getValue! a (insertEntry k v l) = if k == a then v else getValue! a l := by
  simp [getValue!_eq_getValue?, getValue?_insertEntry, apply_ite Option.get!]

theorem getValue!_insertEntry_self {β : Type v} [BEq α] [EquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {k : α} {v : β} : getValue! k (insertEntry k v l) = v := by
  simp [getValue!_insertEntry, BEq.refl]

theorem getValueD_insertEntry {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {fallback v : β} : getValueD a (insertEntry k v l) fallback =
      if k == a then v else getValueD a l fallback := by
  simp [getValueD_eq_getValue?, getValue?_insertEntry, apply_ite (fun x => Option.getD x fallback)]

theorem getValueD_insertEntry_self {β : Type v} [BEq α] [EquivBEq α] {l : List ((_ : α) × β)}
    {k : α} {fallback v : β} : getValueD k (insertEntry k v l) fallback = v := by
  simp [getValueD_insertEntry, BEq.refl]

theorem getKey?_insertEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} : getKey? a (insertEntry k v l) = if k == a then some k else getKey? a l := by
  cases hl : containsKey k l
  · simp [insertEntry_of_containsKey_eq_false hl]
  · rw [insertEntry_of_containsKey hl, getKey?_replaceEntry, hl]
    split <;> simp_all

theorem getKey?_insertEntry_self [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} : getKey? k (insertEntry k v l) = some k := by
  simp [getKey?_insertEntry]

theorem getKey?_eq_none [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l = false) : getKey? a l = none := by
  rwa [← Option.not_isSome_iff_eq_none, ← containsKey_eq_isSome_getKey?, Bool.not_eq_true]

theorem getKey!_insertEntry [BEq α] [EquivBEq α] [Inhabited α]  {l : List ((a : α) × β a)}
    {k a : α} {v : β k} : getKey! a (insertEntry k v l) =
      if k == a then k else getKey! a l := by
  simp [getKey!_eq_getKey?, getKey?_insertEntry, apply_ite Option.get!]

theorem getKey!_insertEntry_self [BEq α] [EquivBEq α] [Inhabited α] {l : List ((a : α) × β a)}
    {k : α} {v : β k} : getKey! k (insertEntry k v l) = k := by
  rw [getKey!_insertEntry, if_pos BEq.refl]

theorem getKeyD_insertEntry [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k a fallback : α}
    {v : β k} : getKeyD a (insertEntry k v l) fallback =
      if k == a then k else getKeyD a l fallback := by
  simp [getKeyD_eq_getKey?, getKey?_insertEntry, apply_ite (fun x => Option.getD x fallback)]

theorem getKeyD_insertEntry_self [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k fallback : α}
    {v : β k} : getKeyD k (insertEntry k v l) fallback = k := by
  rw [getKeyD_insertEntry, if_pos BEq.refl]

@[local simp]
theorem containsKey_insertEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} : containsKey a (insertEntry k v l) = ((k == a) || containsKey a l) := by
  rw [containsKey_eq_isSome_getEntry?, containsKey_eq_isSome_getEntry?, getEntry?_insertEntry]
  cases k == a <;> simp

theorem containsKey_insertEntry_of_beq [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a : α} {v : β k} (h : k == a) : containsKey a (insertEntry k v l) := by
  simp [h]

theorem containsKey_insertEntry_self [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} : containsKey k (insertEntry k v l) :=
  containsKey_insertEntry_of_beq BEq.refl

theorem containsKey_of_containsKey_insertEntry [BEq α] [PartialEquivBEq α]
    {l : List ((a : α) × β a)} {k a : α} {v : β k} (h₁ : containsKey a (insertEntry k v l))
    (h₂ : (k == a) = false) : containsKey a l := by
  rwa [containsKey_insertEntry, h₂, Bool.false_or] at h₁

theorem getValueCast_insertEntry [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} {h} : getValueCast a (insertEntry k v l) h =
    if h' : k == a then cast (congrArg β (eq_of_beq h')) v
    else getValueCast a l (containsKey_of_containsKey_insertEntry h (Bool.eq_false_iff.2 h')) := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, apply_dite Option.some,
    getValueCast?_insertEntry]
  simp only [← getValueCast?_eq_some_getValueCast]

theorem getValueCast_insertEntry_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} : getValueCast k (insertEntry k v l) containsKey_insertEntry_self = v := by
  simp [getValueCast_insertEntry]

theorem getValue_insertEntry {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {v : β} {h} : getValue a (insertEntry k v l) h =
      if h' : k == a then v
      else getValue a l (containsKey_of_containsKey_insertEntry h (Bool.eq_false_iff.2 h')) := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, apply_dite Option.some,
    getValue?_insertEntry, ← dite_eq_ite]
  simp only [← getValue?_eq_some_getValue]

theorem getValue_insertEntry_self {β : Type v} [BEq α] [EquivBEq α] {l : List ((_ : α) × β)} {k : α}
    {v : β} : getValue k (insertEntry k v l) containsKey_insertEntry_self = v := by
  simp [getValue_insertEntry]

theorem getKey_insertEntry [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} {h} : getKey a (insertEntry k v l) h =
    if h' : k == a then k
    else getKey a l (containsKey_of_containsKey_insertEntry h (Bool.eq_false_iff.2 h')) := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey, apply_dite Option.some, getKey?_insertEntry]
  simp only [← getKey?_eq_some_getKey, dite_eq_ite]

theorem getKey_insertEntry_self [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} : getKey k (insertEntry k v l) containsKey_insertEntry_self = k := by
  simp [getKey_insertEntry]

/-- Internal implementation detail of the hash map -/
def insertEntryIfNew [BEq α] (k : α) (v : β k) (l : List ((a : α) × β a)) : List ((a : α) × β a) :=
  bif containsKey k l then l else ⟨k, v⟩ :: l

theorem insertEntryIfNew_of_containsKey [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l) : insertEntryIfNew k v l = l := by
  simp_all [insertEntryIfNew]

theorem insertEntryIfNew_of_containsKey_eq_false [BEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} (h : containsKey k l = false) : insertEntryIfNew k v l = ⟨k, v⟩ :: l := by
  simp_all [insertEntryIfNew]

theorem DistinctKeys.insertEntryIfNew [BEq α] [PartialEquivBEq α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (h: DistinctKeys l):
    DistinctKeys (insertEntryIfNew k v l) := by
  simp only [Std.Internal.List.insertEntryIfNew, cond_eq_if]
  split
  · exact h
  · rw [distinctKeys_cons_iff]
    rename_i h'
    simp [h, h']

@[simp]
theorem isEmpty_insertEntryIfNew [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (insertEntryIfNew k v l).isEmpty = false := by
  cases h : containsKey k l
  · simp [insertEntryIfNew_of_containsKey_eq_false h]
  · rw [insertEntryIfNew_of_containsKey h]
    exact isEmpty_eq_false_of_containsKey h

theorem getEntry?_insertEntryIfNew [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} : getEntry? a (insertEntryIfNew k v l) =
      if k == a && !containsKey k l then some ⟨k, v⟩ else getEntry? a l := by
  cases h : containsKey k l
  · simp [insertEntryIfNew_of_containsKey_eq_false h, getEntry?_cons]
  · simp [insertEntryIfNew_of_containsKey h]

theorem getValueCast?_insertEntryIfNew [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} : getValueCast? a (insertEntryIfNew k v l) =
      if h : k == a ∧ containsKey k l = false then some (cast (congrArg β (eq_of_beq h.1)) v)
      else getValueCast? a l := by
  cases h : containsKey k l
  · rw [insertEntryIfNew_of_containsKey_eq_false h, getValueCast?_cons]
    split <;> simp_all
  · simp [insertEntryIfNew_of_containsKey h]

theorem getValue?_insertEntryIfNew {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {v : β} : getValue? a (insertEntryIfNew k v l) =
      if k == a ∧ containsKey k l = false then some v else getValue? a l := by
  simp [getValue?_eq_getEntry?, getEntry?_insertEntryIfNew,
      apply_ite (Option.map (fun (y : ((_ : α) × β)) => y.2))]

theorem containsKey_insertEntryIfNew [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a : α} {v : β k} :
    containsKey a (insertEntryIfNew k v l) = ((k == a) || containsKey a l) := by
  simp only [containsKey_eq_isSome_getEntry?, getEntry?_insertEntryIfNew, apply_ite Option.isSome,
    Option.isSome_some, if_true_left]
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.not_isSome, Option.isNone_iff_eq_none,
    getEntry?_eq_none, Bool.if_true_left, Bool.decide_and, Bool.decide_eq_true,
    Bool.decide_eq_false]
  cases h : k == a
  · simp
  · rw [containsKey_eq_isSome_getEntry?, getEntry?_congr h]
    simp

theorem containsKey_insertEntryIfNew_self [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k : α}
    {v : β k} : containsKey k (insertEntryIfNew k v l) := by
  rw [containsKey_insertEntryIfNew, BEq.refl, Bool.true_or]

theorem containsKey_of_containsKey_insertEntryIfNew [BEq α] [PartialEquivBEq α]
    {l : List ((a : α) × β a)} {k a : α} {v : β k} (h₁ : containsKey a (insertEntryIfNew k v l))
    (h₂ : (k == a) = false) : containsKey a l := by
  rwa [containsKey_insertEntryIfNew, h₂, Bool.false_or] at h₁

/--
This is a restatement of `containsKey_insertEntryIfNew` that is written to exactly match the proof
obligation in the statement of `getValueCast_insertEntryIfNew`.
-/
theorem containsKey_of_containsKey_insertEntryIfNew' [BEq α] [PartialEquivBEq α]
    {l : List ((a : α) × β a)} {k a : α} {v : β k} (h₁ : containsKey a (insertEntryIfNew k v l))
    (h₂ : ¬((k == a) ∧ containsKey k l = false)) : containsKey a l := by
  rw [Decidable.not_and_iff_or_not, Bool.not_eq_true, Bool.not_eq_false] at h₂
  rcases h₂ with h₂|h₂
  · rwa [containsKey_insertEntryIfNew, h₂, Bool.false_or] at h₁
  · rwa [insertEntryIfNew_of_containsKey h₂] at h₁

theorem getValueCast_insertEntryIfNew [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} {h} : getValueCast a (insertEntryIfNew k v l) h =
    if h' : k == a ∧ containsKey k l = false then
      cast (congrArg β (eq_of_beq h'.1)) v
    else
      getValueCast a l (containsKey_of_containsKey_insertEntryIfNew' h h') := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, apply_dite Option.some,
    getValueCast?_insertEntryIfNew]
  simp only [← getValueCast?_eq_some_getValueCast]

theorem getValue_insertEntryIfNew {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {v : β} {h} : getValue a (insertEntryIfNew k v l) h =
    if h' : k == a ∧ containsKey k l = false then v
    else getValue a l (containsKey_of_containsKey_insertEntryIfNew' h h') := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, apply_dite Option.some,
    getValue?_insertEntryIfNew, ← dite_eq_ite]
  simp [← getValue?_eq_some_getValue]

theorem getValueCast!_insertEntryIfNew [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} [Inhabited (β a)] : getValueCast! a (insertEntryIfNew k v l) =
      if h : k == a ∧ containsKey k l = false then cast (congrArg β (eq_of_beq h.1)) v
      else getValueCast! a l := by
  simp [getValueCast!_eq_getValueCast?, getValueCast?_insertEntryIfNew, apply_dite Option.get!]

theorem getValue!_insertEntryIfNew {β : Type v} [BEq α] [PartialEquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {k a : α} {v : β} : getValue! a (insertEntryIfNew k v l) =
      if k == a ∧ containsKey k l = false then v else getValue! a l := by
  simp [getValue!_eq_getValue?, getValue?_insertEntryIfNew, apply_ite Option.get!]

theorem getValueCastD_insertEntryIfNew [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} {fallback : β a} : getValueCastD a (insertEntryIfNew k v l) fallback =
      if h : k == a ∧ containsKey k l = false then cast (congrArg β (eq_of_beq h.1)) v
      else getValueCastD a l fallback := by
  simp [getValueCastD_eq_getValueCast?, getValueCast?_insertEntryIfNew,
    apply_dite (fun x => Option.getD x fallback)]

theorem getValueD_insertEntryIfNew {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {fallback v : β} : getValueD a (insertEntryIfNew k v l) fallback =
      if k == a ∧ containsKey k l = false then v else getValueD a l fallback := by
  simp [getValueD_eq_getValue?, getValue?_insertEntryIfNew,
    apply_ite (fun x => Option.getD x fallback)]

theorem getKey?_insertEntryIfNew [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    {v : β k} : getKey? a (insertEntryIfNew k v l) =
      if k == a ∧ containsKey k l = false then some k else getKey? a l := by
  cases h : containsKey k l
  · rw [insertEntryIfNew_of_containsKey_eq_false h]
    split <;> simp_all
  · simp [insertEntryIfNew_of_containsKey h]

theorem getKey_insertEntryIfNew [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a : α} {v : β k} {h} : getKey a (insertEntryIfNew k v l) h =
    if h' : k == a ∧ containsKey k l = false then k
    else getKey a l (containsKey_of_containsKey_insertEntryIfNew' h h') := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey, apply_dite Option.some,
    getKey?_insertEntryIfNew, ← dite_eq_ite]
  simp [← getKey?_eq_some_getKey]

theorem getKey!_insertEntryIfNew [BEq α] [PartialEquivBEq α] [Inhabited α]
    {l : List ((a : α) × β a)} {k a : α} {v : β k} : getKey! a (insertEntryIfNew k v l) =
      if k == a ∧ containsKey k l = false then k else getKey! a l := by
  simp [getKey!_eq_getKey?, getKey?_insertEntryIfNew, apply_ite Option.get!]

theorem getKeyD_insertEntryIfNew [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a fallback : α} {v : β k} : getKeyD a (insertEntryIfNew k v l) fallback =
      if k == a ∧ containsKey k l = false then k else getKeyD a l fallback := by
  simp [getKeyD_eq_getKey?, getKey?_insertEntryIfNew, apply_ite (fun x => Option.getD x fallback)]

theorem length_insertEntryIfNew [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (insertEntryIfNew k v l).length = if containsKey k l then l.length else l.length + 1 := by
  simp [insertEntryIfNew, Bool.apply_cond List.length]

theorem length_le_length_insertEntryIfNew [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    l.length ≤ (insertEntryIfNew k v l).length := by
  rw [length_insertEntryIfNew]
  split <;> omega

theorem length_insertEntryIfNew_le [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k} :
    (insertEntryIfNew k v l).length ≤ l.length + 1 := by
  rw [length_insertEntryIfNew]
  split <;> omega

@[simp]
theorem keys_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α} :
    keys (eraseKey k l) = (keys l).erase k := by
  induction l using assoc_induction
  · rfl
  · next k' v' l ih =>
    simp only [eraseKey_cons, keys_cons, List.erase_cons]
    rw [BEq.comm]
    cases k == k' <;> simp [ih]

theorem DistinctKeys.eraseKey [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α} :
    DistinctKeys l → DistinctKeys (eraseKey k l) := by
  apply distinctKeys_of_sublist_keys (by simpa using erase_sublist _ _)

theorem getEntry?_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α}
    (h : DistinctKeys l) : getEntry? k (eraseKey k l) = none := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [eraseKey_cons_of_false h', getEntry?_cons_of_false h']
      exact ih h.tail
    · rw [eraseKey_cons_of_beq h', ← Option.not_isSome_iff_eq_none, Bool.not_eq_true,
        ← containsKey_eq_isSome_getEntry?, ← containsKey_congr h']
      exact h.containsKey_eq_false

theorem getEntry?_eraseKey_of_beq [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    (hl : DistinctKeys l) (hka : k == a) : getEntry? a (eraseKey k l) = none := by
  rw [← getEntry?_congr hka, getEntry?_eraseKey_self hl]

theorem getEntry?_eraseKey_of_false [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a : α} (hka : (k == a) = false) : getEntry? a (eraseKey k l) = getEntry? a l := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    cases h' : k' == k
    · rw [eraseKey_cons_of_false h']
      cases h'' : k' == a
      · rw [getEntry?_cons_of_false h'', ih, getEntry?_cons_of_false h'']
      · rw [getEntry?_cons_of_true h'', getEntry?_cons_of_true h'']
    · rw [eraseKey_cons_of_beq h']
      have hx : (k' == a) = false := BEq.neq_of_beq_of_neq h' hka
      rw [getEntry?_cons_of_false hx]

theorem getEntry?_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    (hl : DistinctKeys l) :
    getEntry? a (eraseKey k l) = if k == a then none else getEntry? a l := by
  cases h : k == a
  · simp [getEntry?_eraseKey_of_false h, h]
  · simp [getEntry?_eraseKey_of_beq hl h, h]

theorem keys_filterMap [BEq α] {l : List ((a : α) × β a)} {f : (a : α) → β a → Option (γ a)} :
    keys (l.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) =
      keys (l.filter fun p => (f p.1 p.2).isSome) := by
  induction l using assoc_induction
  · simp
  · next k v t ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    cases f k v <;> simp [ih]

@[simp]
theorem keys_map [BEq α] {l : List ((a : α) × β a)} {f : (a : α) → β a → γ a} :
    keys (l.map fun p => ⟨p.1, f p.1 p.2⟩) = keys l := by
  induction l using assoc_induction <;> simp_all

theorem DistinctKeys.filterMap [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {f : (a : α) → β a → Option (γ a)} :
    DistinctKeys l → DistinctKeys (l.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  apply distinctKeys_of_sublist_keys
  rw [keys_filterMap, keys_eq_map, keys_eq_map]
  apply Sublist.map
  exact filter_sublist l

theorem DistinctKeys.map [BEq α] {l : List ((a : α) × β a)} {f : (a : α) → β a → γ a}
    (h : DistinctKeys l) : DistinctKeys (l.map fun p => ⟨p.1, f p.1 p.2⟩) :=
  h.of_keys_eq keys_map.symm

theorem DistinctKeys.filter [BEq α] {l : List ((a : α) × β a)} {f : (a : α) → β a → Bool}
    (h : DistinctKeys l) : DistinctKeys (l.filter fun p => f p.1 p.2) :=
  distinctKeys_of_sublist (filter_sublist _) h

section

variable {β : Type v}

theorem getValue?_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k : α}
    (h : DistinctKeys l) : getValue? k (eraseKey k l) = none := by
  simp [getValue?_eq_getEntry?, getEntry?_eraseKey_self h]

theorem getValue?_eraseKey_of_beq [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    (hl : DistinctKeys l) (hka : k == a) : getValue? a (eraseKey k l) = none := by
  simp [getValue?_eq_getEntry?, getEntry?_eraseKey_of_beq hl hka]

theorem getValue?_eraseKey_of_false [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    (hka : (k == a) = false) : getValue? a (eraseKey k l) = getValue? a l := by
  simp [getValue?_eq_getEntry?, getEntry?_eraseKey_of_false hka]

theorem getValue?_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)} {k a : α}
    (hl : DistinctKeys l) :
    getValue? a (eraseKey k l) = if k == a then none else getValue? a l := by
  simp [getValue?_eq_getEntry?, getEntry?_eraseKey hl, apply_ite (Option.map _)]

end

theorem getKey?_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    (hl : DistinctKeys l) :
    getKey? a (eraseKey k l) = if k == a then none else getKey? a l := by
  rw [getKey?_eq_getEntry?, getEntry?_eraseKey hl]
  by_cases h : k == a
  . simp [h]
  . simp [h, getKey?_eq_getEntry?]

theorem getKey?_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α}
    (hl : DistinctKeys l) : getKey? k (eraseKey k l) = none := by
  simp [getKey?_eq_getEntry?, getEntry?_eraseKey_self hl]

theorem getKey!_eraseKey [BEq α] [PartialEquivBEq α] [Inhabited α] {l : List ((a : α) × β a)}
    {k a : α} (hl : DistinctKeys l) :
    getKey! a (eraseKey k l) = if k == a then default else getKey! a l := by
  simp [getKey!_eq_getKey?, getKey?_eraseKey hl, apply_ite Option.get!]

theorem getKey!_eraseKey_self [BEq α] [PartialEquivBEq α] [Inhabited α]  {l : List ((a : α) × β a)}
    {k : α} (hl : DistinctKeys l) : getKey! k (eraseKey k l) = default := by
  simp [getKey!_eq_getKey?, getKey?_eraseKey_self hl]

theorem getKeyD_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a fallback : α}
    (hl : DistinctKeys l) :
    getKeyD a (eraseKey k l) fallback = if k == a then fallback else getKeyD a l fallback := by
  simp [getKeyD_eq_getKey?, getKey?_eraseKey hl, apply_ite (fun x => Option.getD x fallback)]

theorem getKeyD_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k fallback : α} (hl : DistinctKeys l) : getKeyD k (eraseKey k l) fallback = fallback := by
  simp [getKeyD_eq_getKey?, getKey?_eraseKey_self hl]

theorem containsKey_eraseKey_self [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k : α}
    (h : DistinctKeys l) : containsKey k (eraseKey k l) = false := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_eraseKey_self h]

theorem containsKey_eraseKey_of_beq [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a : α} (hl : DistinctKeys l) (hka : a == k) : containsKey a (eraseKey k l) = false := by
  rw [containsKey_congr hka, containsKey_eraseKey_self hl]

theorem containsKey_eraseKey_of_false [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a : α} (hka : (k == a) = false) : containsKey a (eraseKey k l) = containsKey a l := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_eraseKey_of_false hka]

theorem containsKey_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {k a : α}
    (hl : DistinctKeys l) : containsKey a (eraseKey k l) = (!(k == a) && containsKey a l) := by
  simp [containsKey_eq_isSome_getEntry?, getEntry?_eraseKey hl, apply_ite]

theorem getValueCast?_eraseKey [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    (hl : DistinctKeys l) :
    getValueCast? a (eraseKey k l) = if k == a then none else getValueCast? a l := by
  rw [getValueCast?_eq_getEntry?, Option.dmap_congr (getEntry?_eraseKey hl)]
  by_cases h : k == a
  · rw [Option.dmap_congr (if_pos h), Option.dmap_none, if_pos h]
  · rw [Option.dmap_congr (if_neg h), getValueCast?_eq_getEntry?]
    exact (if_neg h).symm

theorem getValueCast?_eraseKey_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α}
    (hl : DistinctKeys l) : getValueCast? k (eraseKey k l) = none := by
  rw [getValueCast?_eraseKey hl, if_pos BEq.refl]

theorem getValueCast!_eraseKey [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    [Inhabited (β a)] (hl : DistinctKeys l) :
    getValueCast! a (eraseKey k l) = if k == a then default else getValueCast! a l := by
  simp [getValueCast!_eq_getValueCast?, getValueCast?_eraseKey hl, apply_ite Option.get!]

theorem getValueCast!_eraseKey_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α}
    [Inhabited (β k)] (hl : DistinctKeys l) : getValueCast! k (eraseKey k l) = default := by
  simp [getValueCast!_eq_getValueCast?, getValueCast?_eraseKey_self hl]

theorem getValueCastD_eraseKey [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α}
    {fallback : β a} (hl : DistinctKeys l) : getValueCastD a (eraseKey k l) fallback =
      if k == a then fallback else getValueCastD a l fallback := by
  simp [getValueCastD_eq_getValueCast?, getValueCast?_eraseKey hl,
    apply_ite (fun x => Option.getD x fallback)]

theorem getValueCastD_eraseKey_self [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k : α}
    {fallback : β k} (hl : DistinctKeys l) :
    getValueCastD k (eraseKey k l) fallback = fallback := by
  simp [getValueCastD_eq_getValueCast?, getValueCast?_eraseKey_self hl]

theorem getValue!_eraseKey {β : Type v} [BEq α] [PartialEquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {k a : α} (hl : DistinctKeys l) :
    getValue! a (eraseKey k l) = if k == a then default else getValue! a l := by
  simp [getValue!_eq_getValue?, getValue?_eraseKey hl, apply_ite Option.get!]

theorem getValue!_eraseKey_self {β : Type v} [BEq α] [PartialEquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {k : α} (hl : DistinctKeys l) :
    getValue! k (eraseKey k l) = default := by
  simp [getValue!_eq_getValue?, getValue?_eraseKey_self hl]

theorem getValueD_eraseKey {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {fallback : β} (hl : DistinctKeys l) : getValueD a (eraseKey k l) fallback =
      if k == a then fallback else getValueD a l fallback := by
  simp [getValueD_eq_getValue?, getValue?_eraseKey hl, apply_ite (fun x => Option.getD x fallback)]

theorem getValueD_eraseKey_self {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k : α} {fallback : β} (hl : DistinctKeys l) :
    getValueD k (eraseKey k l) fallback = fallback := by
  simp [getValueD_eq_getValue?, getValue?_eraseKey_self hl]

theorem containsKey_of_containsKey_eraseKey [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k a : α} (hl : DistinctKeys l) : containsKey a (eraseKey k l) → containsKey a l := by
  simp [containsKey_eraseKey hl]

theorem getValueCast_eraseKey [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {k a : α} {h}
    (hl : DistinctKeys l) : getValueCast a (eraseKey k l) h =
      getValueCast a l (containsKey_of_containsKey_eraseKey hl h) := by
  rw [containsKey_eraseKey hl, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, getValueCast?_eraseKey hl, h.1]
  simp [← getValueCast?_eq_some_getValueCast]

theorem getValue_eraseKey {β : Type v} [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × β)}
    {k a : α} {h} (hl : DistinctKeys l) :
    getValue a (eraseKey k l) h = getValue a l (containsKey_of_containsKey_eraseKey hl h) := by
  rw [containsKey_eraseKey hl, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, getValue?_eraseKey hl, h.1]
  simp [← getValue?_eq_some_getValue]

theorem getKey_eraseKey [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k a : α} {h}
    (hl : DistinctKeys l) : getKey a (eraseKey k l) h =
      getKey a l (containsKey_of_containsKey_eraseKey hl h) := by
  rw [containsKey_eraseKey hl, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [← Option.some_inj, ← getKey?_eq_some_getKey, getKey?_eraseKey hl, h.1]
  simp [← getKey?_eq_some_getKey]

theorem getEntry?_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)} {a : α}
    (hl : DistinctKeys l) (h : Perm l l') : getEntry? a l = getEntry? a l' := by
  induction h
  · simp
  · next p t₁ t₂ _ ih₂ =>
    rcases p with ⟨k', v'⟩
    simp only [getEntry?_cons, ih₂ hl.tail]
  · next p p' _ =>
    rcases p with ⟨k₁, v₁⟩
    rcases p' with ⟨k₂, v₂⟩
    simp only [getEntry?_cons]
    cases h₂ : k₂ == a <;> cases h₁ : k₁ == a <;> try simp; done
    simp only [distinctKeys_cons_iff, containsKey_cons, Bool.or_eq_false_iff] at hl
    exact ((Bool.eq_false_iff.1 hl.2.1).elim (BEq.trans h₁ (BEq.symm h₂))).elim
  · next l₁ l₂ l₃ hl₁₂ _ ih₁ ih₂ => exact (ih₁ hl).trans (ih₂ (hl.perm (hl₁₂.symm)))

theorem containsKey_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)} {k : α}
    (h : Perm l l') : containsKey k l = containsKey k l' := by
  induction h
  · simp
  · next p t₁ t₂ _ ih₂ => rw [containsKey_cons, containsKey_cons, ih₂]
  · next p p' _ =>
    rw [containsKey_cons, containsKey_cons, containsKey_cons, containsKey_cons]
    simp only [← Bool.or_assoc, Bool.or_comm]
  · next _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem getValueCast?_of_perm [BEq α] [LawfulBEq α] {l l' : List ((a : α) × β a)} {a : α}
    (hl : DistinctKeys l) (h : Perm l l') : getValueCast? a l = getValueCast? a l' := by
  rw [getValueCast?_eq_getEntry?, getValueCast?_eq_getEntry?,
    Option.dmap_congr (getEntry?_of_perm hl h)]

theorem getValueCast_of_perm [BEq α] [LawfulBEq α] {l l' : List ((a : α) × β a)} {a : α} {h'}
    (hl : DistinctKeys l) (h : Perm l l') :
    getValueCast a l h' = getValueCast a l' ((containsKey_of_perm h).symm.trans h') := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, ← getValueCast?_eq_some_getValueCast,
    getValueCast?_of_perm hl h]

theorem getValueCast!_of_perm [BEq α] [LawfulBEq α] {l l' : List ((a : α) × β a)} {a : α}
    [Inhabited (β a)] (hl : DistinctKeys l) (h : Perm l l') :
    getValueCast! a l = getValueCast! a l' := by
  simp only [getValueCast!_eq_getValueCast?, getValueCast?_of_perm hl h]

theorem getValueCastD_of_perm [BEq α] [LawfulBEq α] {l l' : List ((a : α) × β a)} {a : α}
    {fallback : β a} (hl : DistinctKeys l) (h : Perm l l') :
    getValueCastD a l fallback = getValueCastD a l' fallback := by
  simp only [getValueCastD_eq_getValueCast?, getValueCast?_of_perm hl h]

section

variable {β : Type v}

theorem getValue?_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((_ : α) × β)} {a : α}
    (hl : DistinctKeys l) (h : Perm l l') : getValue? a l = getValue? a l' := by
  simp only [getValue?_eq_getEntry?, getEntry?_of_perm hl h]

theorem getValue_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((_ : α) × β)} {a : α} {h'}
    (hl : DistinctKeys l) (h : Perm l l') :
    getValue a l h' = getValue a l' ((containsKey_of_perm h).symm.trans h') := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, ← getValue?_eq_some_getValue,
    getValue?_of_perm hl h]

theorem getValue!_of_perm [BEq α] [PartialEquivBEq α] [Inhabited β] {l l' : List ((_ : α) × β)}
    {a : α} (hl : DistinctKeys l) (h : Perm l l') : getValue! a l = getValue! a l' := by
  simp only [getValue!_eq_getValue?, getValue?_of_perm hl h]

theorem getValueD_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((_ : α) × β)} {a : α}
    {fallback : β} (hl : DistinctKeys l) (h : Perm l l') :
    getValueD a l fallback = getValueD a l' fallback := by
  simp only [getValueD_eq_getValue?, getValue?_of_perm hl h]

end

theorem getKey?_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)} {a : α}
    (hl : DistinctKeys l) (h : Perm l l') : getKey? a l = getKey? a l' := by
  rw [getKey?_eq_getEntry?, getKey?_eq_getEntry?, getEntry?_of_perm hl h]

theorem getKey_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)} {a : α} {h'}
    (hl : DistinctKeys l) (h : Perm l l') :
    getKey a l h' = getKey a l' ((containsKey_of_perm h).symm.trans h') := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey, ← getKey?_eq_some_getKey,
    getKey?_of_perm hl h]

theorem getKey!_of_perm [BEq α] [PartialEquivBEq α] [Inhabited α] {l l' : List ((a : α) × β a)}
    {a : α} (hl : DistinctKeys l) (h : Perm l l') :
    getKey! a l = getKey! a l' := by
  simp only [getKey!_eq_getKey?, getKey?_of_perm hl h]

theorem getKeyD_of_perm [BEq α] [PartialEquivBEq α] {l l' : List ((a : α) × β a)} {a fallback : α}
    (hl : DistinctKeys l) (h : Perm l l') :
    getKeyD a l fallback = getKeyD a l' fallback := by
  simp only [getKeyD_eq_getKey?, getKey?_of_perm hl h]

theorem perm_cons_getEntry [BEq α] {l : List ((a : α) × β a)} {a : α} (h : containsKey a l) :
    ∃ l', Perm l (getEntry a l h :: l') := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_true] at h
    cases hk : k' == a
    · obtain ⟨l', hl'⟩ := ih (h.resolve_left (Bool.not_eq_true _ ▸ hk))
      rw [getEntry_cons_of_false hk]
      exact ⟨⟨k', v'⟩ :: l', (hl'.cons _).trans (Perm.swap' _ _ (Perm.refl _))⟩
    · exact ⟨t, by rw [getEntry_cons_of_beq hk]⟩

-- Note: this theorem becomes false if you don't assume that BEq is reflexive on α.
theorem getEntry?_ext [BEq α] [EquivBEq α] {l l' : List ((a : α) × β a)} (hl : DistinctKeys l)
    (hl' : DistinctKeys l') (h : ∀ a, getEntry? a l = getEntry? a l') : Perm l l' := by
  induction l using assoc_induction generalizing l'
  · induction l' using assoc_induction
    · exact Perm.refl _
    · next k _ _ _ => simpa using h k
  · next k v t ih =>
    have hl'k₁ : getEntry? k l' = some ⟨k, v⟩ := by rw [← h, getEntry?_cons_self]
    have hl'k₂ : containsKey k l' := by
      rw [containsKey_eq_isSome_getEntry?, hl'k₁, Option.isSome_some]
    obtain ⟨l'', hl''⟩ := perm_cons_getEntry hl'k₂
    rw [getEntry_eq_of_getEntry?_eq_some hl'k₁] at hl''
    suffices Perm t l'' from (this.cons _).trans hl''.symm
    apply ih hl.tail (hl'.perm hl''.symm).tail
    intro k'
    cases hk' : k == k'
    · simpa only [getEntry?_of_perm hl' hl'', getEntry?_cons_of_false hk'] using h k'
    · rw [← getEntry?_congr hk', ← getEntry?_congr hk', getEntry?_eq_none.2 hl.containsKey_eq_false,
          getEntry?_eq_none.2 (hl'.perm hl''.symm).containsKey_eq_false]

theorem replaceEntry_of_perm [BEq α] [EquivBEq α] {l l' : List ((a : α) × β a)} {k : α} {v : β k}
    (hl : DistinctKeys l) (h : Perm l l') : Perm (replaceEntry k v l) (replaceEntry k v l') := by
  apply getEntry?_ext hl.replaceEntry (hl.perm h.symm).replaceEntry
  simp [getEntry?_replaceEntry, getEntry?_of_perm hl h, containsKey_of_perm h]

theorem insertEntry_of_perm [BEq α] [EquivBEq α] {l l' : List ((a : α) × β a)} {k : α} {v : β k}
    (hl : DistinctKeys l) (h : Perm l l') : Perm (insertEntry k v l) (insertEntry k v l') := by
  apply getEntry?_ext hl.insertEntry (hl.perm h.symm).insertEntry
  simp [getEntry?_insertEntry, getEntry?_of_perm hl h]

theorem eraseKey_of_perm [BEq α] [EquivBEq α] {l l' : List ((a : α) × β a)} {k : α}
    (hl : DistinctKeys l) (h : Perm l l') : Perm (eraseKey k l) (eraseKey k l') := by
  apply getEntry?_ext hl.eraseKey (hl.perm h.symm).eraseKey
  simp [getEntry?_eraseKey hl, getEntry?_eraseKey (hl.perm h.symm), getEntry?_of_perm hl h]

@[simp]
theorem getEntry?_append [BEq α] {l l' : List ((a : α) × β a)} {a : α} :
    getEntry? a (l ++ l') = (getEntry? a l).or (getEntry? a l') := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih => cases h : k' == a <;> simp_all [getEntry?_cons]

theorem getEntry?_append_of_containsKey_eq_false [BEq α] {l l' : List ((a : α) × β a)} {a : α}
    (h : containsKey a l' = false) : getEntry? a (l ++ l') = getEntry? a l := by
  rw [getEntry?_append, getEntry?_eq_none.2 h, Option.or_none]

@[simp]
theorem containsKey_append [BEq α] {l l' : List ((a : α) × β a)} {a : α} :
    containsKey a (l ++ l') = (containsKey a l || containsKey a l') := by
  simp [containsKey_eq_isSome_getEntry?]

theorem containsKey_flatMap_eq_false [BEq α] {γ : Type w} {l : List γ} {f : γ → List ((a : α) × β a)}
    {a : α} (h : ∀ (i : Nat) (h : i < l.length), containsKey a (f l[i]) = false) :
    containsKey a (l.flatMap f) = false := by
  induction l
  · simp
  · next g t ih =>
    simp only [List.flatMap_cons, containsKey_append, Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · simpa using h 0 (by simp)
    · refine ih ?_
      intro i hi
      simpa using h (i + 1) (by simp only [List.length_cons]; omega)

theorem containsKey_append_of_not_contains_right [BEq α] {l l' : List ((a : α) × β a)} {a : α}
    (hl' : containsKey a l' = false) : containsKey a (l ++ l') = containsKey a l := by
  simp [hl']

@[simp]
theorem getValue?_append {β : Type v} [BEq α] {l l' : List ((_ : α) × β)} {a : α} :
    getValue? a (l ++ l') = (getValue? a l).or (getValue? a l') := by
  simp [getValue?_eq_getEntry?, Option.map_or']

theorem getValue?_append_of_containsKey_eq_false {β : Type v} [BEq α] {l l' : List ((_ : α) × β)}
    {a : α} (h : containsKey a l' = false) : getValue? a (l ++ l') = getValue? a l := by
  rw [getValue?_append, getValue?_eq_none.2 h, Option.or_none]

theorem getValue_append_of_containsKey_eq_false {β : Type v} [BEq α] {l l' : List ((_ : α) × β)}
    {a : α} {h'} (h : containsKey a l' = false) : getValue a (l ++ l') h' =
      getValue a l ((containsKey_append_of_not_contains_right h).symm.trans h') := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, ← getValue?_eq_some_getValue,
    getValue?_append_of_containsKey_eq_false h]

theorem getValueCast?_append_of_containsKey_eq_false [BEq α] [LawfulBEq α]
    {l l' : List ((a : α) × β a)} {a : α} (hl' : containsKey a l' = false) :
    getValueCast? a (l ++ l') = getValueCast? a l := by
  rw [getValueCast?_eq_getEntry?, getValueCast?_eq_getEntry?, Option.dmap_congr getEntry?_append,
    Option.dmap_congr (by rw [getEntry?_eq_none.2 hl']), Option.dmap_congr (by rw [Option.or_none])]

theorem getValueCast_append_of_containsKey_eq_false [BEq α] [LawfulBEq α]
    {l l' : List ((a : α) × β a)} {a : α} {h} (hl' : containsKey a l' = false) :
    getValueCast a (l ++ l') h =
      getValueCast a l ((containsKey_append_of_not_contains_right hl').symm.trans h) := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, ← getValueCast?_eq_some_getValueCast,
    getValueCast?_append_of_containsKey_eq_false hl']

theorem getKey?_append_of_containsKey_eq_false [BEq α] [PartialEquivBEq α]
    {l l' : List ((a : α) × β a)} {a : α} (hl' : containsKey a l' = false) :
    getKey? a (l ++ l') = getKey? a l := by
  simp [getKey?_eq_getEntry?, getEntry?_eq_none.2 hl']

theorem getKey_append_of_containsKey_eq_false [BEq α] [PartialEquivBEq α]
    {l l' : List ((a : α) × β a)} {a : α} {h} (hl' : containsKey a l' = false) :
    getKey a (l ++ l') h =
      getKey a l ((containsKey_append_of_not_contains_right hl').symm.trans h) := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey, ← getKey?_eq_some_getKey,
    getKey?_append_of_containsKey_eq_false hl']

theorem replaceEntry_append_of_containsKey_left [BEq α] {l l' : List ((a : α) × β a)} {k : α}
    {v : β k} (h : containsKey k l) : replaceEntry k v (l ++ l') = replaceEntry k v l ++ l' := by
  induction l using assoc_induction
  · simp at h
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_true] at h
    cases h' : k' == k
    · simpa [replaceEntry_cons, h'] using ih (h.resolve_left (Bool.not_eq_true _ ▸ h'))
    · simp [replaceEntry_cons, h']

theorem replaceEntry_append_of_containsKey_left_eq_false [BEq α] {l l' : List ((a : α) × β a)}
    {k : α} {v : β k} (h : containsKey k l = false) :
    replaceEntry k v (l ++ l') = l ++ replaceEntry k v l' := by
  induction l using assoc_induction
  · simp
  · next k' v' t ih =>
    simp only [containsKey_cons, Bool.or_eq_false_iff] at h
    simpa [replaceEntry_cons, h.1] using ih h.2

theorem replaceEntry_append_of_containsKey_right_eq_false [BEq α] {l l' : List ((a : α) × β a)}
    {k : α} {v : β k} (h : containsKey k l' = false) :
    replaceEntry k v (l ++ l') = replaceEntry k v l ++ l' := by
  cases h' : containsKey k l
  · rw [replaceEntry_of_containsKey_eq_false, replaceEntry_of_containsKey_eq_false h']
    simpa using ⟨h', h⟩
  · rw [replaceEntry_append_of_containsKey_left h']

theorem insertEntry_append_of_not_contains_right [BEq α] {l l' : List ((a : α) × β a)}
    {k : α} {v : β k} (h' : containsKey k l' = false) :
    insertEntry k v (l ++ l') = insertEntry k v l ++ l' := by
  cases h : containsKey k l
  · simp [insertEntry, containsKey_append, h, h']
  · simp [insertEntry, containsKey_append, h, h', replaceEntry_append_of_containsKey_left h]

theorem eraseKey_append_of_containsKey_right_eq_false [BEq α] {l l' : List ((a : α) × β a)} {k : α}
    (h : containsKey k l' = false) : eraseKey k (l ++ l') = eraseKey k l ++ l' := by
  induction l using assoc_induction
  · simp [eraseKey_of_containsKey_eq_false h]
  · next k' v' t ih =>
    rw [List.cons_append, eraseKey_cons, eraseKey_cons]
    cases k' == k
    · rw [cond_false, cond_false, ih, List.cons_append]
    · rw [cond_true, cond_true]

/-- Internal implementation detail of the hash map -/
def insertList [BEq α] (l toInsert : List ((a : α) × β a)) : List ((a : α) × β a) :=
  match toInsert with
  | .nil => l
  | .cons ⟨k, v⟩ toInsert => insertList (insertEntry k v l) toInsert

theorem DistinctKeys.insertList [BEq α] [PartialEquivBEq α] {l₁ l₂ : List ((a : α) × β a)}
    (h : DistinctKeys l₁) :
    DistinctKeys (insertList l₁ l₂) := by
  induction l₂ using assoc_induction generalizing l₁
  · simpa [insertList]
  · rename_i k v t ih
    rw [insertList.eq_def]
    exact ih h.insertEntry

theorem insertList_perm_of_perm_first [BEq α] [EquivBEq α] {l1 l2 toInsert : List ((a : α) × β a)}
    (h : Perm l1 l2) (distinct : DistinctKeys l1) :
    Perm (insertList l1 toInsert) (insertList l2 toInsert) := by
  induction toInsert generalizing l1 l2 with
  | nil => simp [insertList, h]
  | cons hd tl ih =>
    simp only [insertList]
    apply ih (insertEntry_of_perm distinct h) (DistinctKeys.insertEntry distinct)

theorem insertList_cons_perm [BEq α] [EquivBEq α] {l₁ l₂ : List ((a : α) × β a)}
    {p : (a : α) × β a} (hl₁ : DistinctKeys l₁) (hl₂ : DistinctKeys (p :: l₂)) :
    (insertList l₁ (p :: l₂)).Perm (insertEntry p.1 p.2 (insertList l₁ l₂)) := by
  induction l₂ generalizing p l₁
  · simp [insertList]
  · rename_i h t ih
    rw [insertList]
    refine (ih hl₁.insertEntry hl₂.tail).trans
      ((insertEntry_of_perm hl₁.insertList
        (ih hl₁ (distinctKeys_of_sublist (by simp) hl₂))).trans
      (List.Perm.trans ?_ (insertEntry_of_perm hl₁.insertList.insertEntry
        (ih hl₁ (distinctKeys_of_sublist (by simp) hl₂)).symm)))
    apply getEntry?_ext hl₁.insertList.insertEntry.insertEntry
      hl₁.insertList.insertEntry.insertEntry (fun k => ?_)
    simp only [getEntry?_insertEntry]
    split <;> rename_i hp <;> split <;> rename_i hh <;> try rfl
    rw [DistinctKeys.def] at hl₂
    have := List.rel_of_pairwise_cons hl₂ (List.mem_cons_self _ _)
    simp [BEq.trans hh (BEq.symm hp)] at this

theorem getEntry?_insertList [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false)) (k : α) :
    getEntry? k (insertList l toInsert) = (getEntry? k toInsert).or (getEntry? k l) := by
  induction toInsert generalizing l with
  | nil => simp [insertList]
  | cons h t ih =>
    rw [getEntry?_of_perm distinct_l.insertList
      (insertList_cons_perm distinct_l (DistinctKeys.def.2 distinct_toInsert)),
      getEntry?_insertEntry]
    cases hk : h.1 == k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih distinct_l distinct_toInsert.tail, getEntry?_cons_of_false hk]
    · simp only [↓reduceIte]
      rw [getEntry?_cons_of_true hk, Option.some_or]

theorem getEntry?_insertList_of_contains_eq_false [BEq α] [PartialEquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (not_contains : containsKey k toInsert = false) :
    getEntry? k (insertList l toInsert) = getEntry? k l := by
  induction toInsert generalizing l with
  | nil => simp [insertList]
  | cons h t ih =>
    unfold insertList
    rw [containsKey_cons_eq_false] at not_contains
    rw [ih not_contains.right, getEntry?_insertEntry]
    simp [not_contains]

theorem getEntry?_insertList_of_contains_eq_true [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (contains : containsKey k toInsert = true) :
    getEntry? k (insertList l toInsert) = getEntry? k toInsert := by
  rw [getEntry?_insertList distinct_l distinct_toInsert]
  rw [containsKey_eq_isSome_getEntry?] at contains
  exact Option.or_of_isSome contains

theorem containsKey_insertList [BEq α] [PartialEquivBEq α] {l toInsert : List ((a : α) × β a)}
    {k : α} : containsKey k (List.insertList l toInsert) =
    (containsKey k l || (toInsert.map Sigma.fst).contains k) := by
  induction toInsert generalizing l with
  | nil =>  simp only [insertList, List.map_nil, List.elem_nil, Bool.or_false]
  | cons hd tl ih =>
    unfold insertList
    rw [ih]
    rw [containsKey_insertEntry]
    simp only [Bool.or_eq_true, List.map_cons, List.contains_cons]
    rw [BEq.comm]
    conv => left; left; rw [Bool.or_comm]
    rw [Bool.or_assoc]

theorem containsKey_of_containsKey_insertList [BEq α] [PartialEquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α} (h₁ : containsKey k (insertList l toInsert))
    (h₂ : (toInsert.map Sigma.fst).contains k = false) : containsKey k l := by
  rw [containsKey_insertList, h₂] at h₁; simp at h₁; exact h₁

theorem getValueCast?_insertList_of_contains_eq_false [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (not_contains : (toInsert.map Sigma.fst).contains k = false) :
    getValueCast? k (insertList l toInsert) = getValueCast? k l := by
  rw [← containsKey_eq_contains_map_fst] at not_contains
  rw [getValueCast?_eq_getEntry?, getValueCast?_eq_getEntry?]
  apply Option.dmap_congr
  rw [getEntry?_insertList_of_contains_eq_false not_contains]

theorem getValueCast?_insertList_of_mem [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k') {v : β k}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValueCast? k' (insertList l toInsert) =
    some (cast (by congr; exact LawfulBEq.eq_of_beq k_beq) v) := by
  rw [getValueCast?_eq_getEntry?]
  have : getEntry? k' (insertList l toInsert) = getEntry? k' toInsert := by
    apply getEntry?_insertList_of_contains_eq_true distinct_l distinct_toInsert
    apply containsKey_of_beq _ k_beq
    exact containsKey_of_mem mem
  rw [← DistinctKeys.def] at distinct_toInsert
  rw [getEntry?_of_mem distinct_toInsert k_beq mem] at this
  rw [Option.dmap_congr this]
  simp

theorem getValueCast_insertList_of_contains_eq_false [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (not_contains : (toInsert.map Sigma.fst).contains k = false)
    {h} :
    getValueCast k (insertList l toInsert) h =
    getValueCast k l (containsKey_of_containsKey_insertList h not_contains) := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast, ← getValueCast?_eq_some_getValueCast,
    getValueCast?_insertList_of_contains_eq_false]
  exact not_contains

theorem getValueCast_insertList_of_mem [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k') (v : β k)
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert)
    {h} :
    getValueCast k' (insertList l toInsert) h =
    cast (by congr; exact LawfulBEq.eq_of_beq k_beq) v := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast,
    getValueCast?_insertList_of_mem k_beq distinct_l distinct_toInsert mem]

theorem getValueCast!_insertList_of_contains_eq_false [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (not_contains : (toInsert.map Sigma.fst).contains k = false) :
    getValueCast! k (insertList l toInsert) = getValueCast! k l := by
  rw [getValueCast!_eq_getValueCast?, getValueCast!_eq_getValueCast?,
    getValueCast?_insertList_of_contains_eq_false not_contains]

theorem getValueCast!_insertList_of_mem [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k') (v : β k) [Inhabited (β k')]
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValueCast! k' (insertList l toInsert) =
    cast (by congr; exact LawfulBEq.eq_of_beq k_beq) v := by
  rw [getValueCast!_eq_getValueCast?,
    getValueCast?_insertList_of_mem k_beq distinct_l distinct_toInsert mem, Option.get!_some]

theorem getValueCastD_insertList_of_contains_eq_false [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α} {fallback : β k}
    (not_mem : (toInsert.map Sigma.fst).contains k = false) :
    getValueCastD k (insertList l toInsert) fallback = getValueCastD k l fallback := by
  rw [getValueCastD_eq_getValueCast?, getValueCastD_eq_getValueCast?,
    getValueCast?_insertList_of_contains_eq_false not_mem]

theorem getValueCastD_insertList_of_mem [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValueCastD k' (insertList l toInsert) fallback =
    cast (by congr; exact LawfulBEq.eq_of_beq k_beq) v := by
  rw [getValueCastD_eq_getValueCast?,
    getValueCast?_insertList_of_mem k_beq distinct_l distinct_toInsert mem, Option.getD_some]

theorem getKey?_insertList_of_contains_eq_false [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (not_contains : (toInsert.map Sigma.fst).contains k = false) :
    getKey? k (insertList l toInsert) = getKey? k l := by
  rw [← containsKey_eq_contains_map_fst] at not_contains
  rw [getKey?_eq_getEntry?, getKey?_eq_getEntry?,
    getEntry?_insertList_of_contains_eq_false not_contains]

theorem getKey?_insertList_of_mem [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Sigma.fst) :
    getKey? k' (insertList l toInsert) = some k := by
  rcases List.mem_map.1 mem with ⟨⟨k, v⟩, pair_mem, rfl⟩
  rw [getKey?_eq_getEntry?, getEntry?_insertList distinct_l distinct_toInsert,
    getEntry?_of_mem (DistinctKeys.def.2 distinct_toInsert) k_beq pair_mem, Option.some_or,
    Option.map_some']

theorem getKey_insertList_of_contains_eq_false [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (not_contains : (toInsert.map Sigma.fst).contains k = false)
    {h} :
    getKey k (insertList l toInsert) h =
      getKey k l (containsKey_of_containsKey_insertList h not_contains) := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey,
    getKey?_insertList_of_contains_eq_false not_contains, getKey?_eq_some_getKey]

theorem getKey_insertList_of_mem [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Sigma.fst)
    {h} :
    getKey k' (insertList l toInsert) h = k := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey,
    getKey?_insertList_of_mem k_beq distinct_l distinct_toInsert mem]

theorem getKey!_insertList_of_contains_eq_false [BEq α] [EquivBEq α] [Inhabited α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (contains_false : (toInsert.map Sigma.fst).contains k = false) :
    getKey! k (insertList l toInsert) = getKey! k l := by
  rw [getKey!_eq_getKey?, getKey?_insertList_of_contains_eq_false contains_false, getKey!_eq_getKey?]

theorem getKey!_insertList_of_mem [BEq α] [EquivBEq α] [Inhabited α]
    {l toInsert : List ((a : α) × β a)}
    {k k' : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Sigma.fst) :
    getKey! k' (insertList l toInsert) = k := by
  rw [getKey!_eq_getKey?, getKey?_insertList_of_mem k_beq distinct_l distinct_toInsert mem,
    Option.get!_some]

theorem getKeyD_insertList_of_contains_eq_false [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k fallback : α}
    (not_contains : (toInsert.map Sigma.fst).contains k = false) :
    getKeyD k (insertList l toInsert) fallback = getKeyD k l fallback := by
  rw [getKeyD_eq_getKey?, getKey?_insertList_of_contains_eq_false not_contains, getKeyD_eq_getKey?]

theorem getKeyD_insertList_of_mem [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Sigma.fst) :
    getKeyD k' (insertList l toInsert) fallback = k := by
  rw [getKeyD_eq_getKey?, getKey?_insertList_of_mem k_beq distinct_l distinct_toInsert mem,
    Option.getD_some]

theorem perm_insertList [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (distinct_both : ∀ (a : α), containsKey a l → (toInsert.map Sigma.fst).contains a = false) :
    Perm (insertList l toInsert) (l ++ toInsert) := by
  rw [← DistinctKeys.def] at distinct_toInsert
  induction toInsert generalizing l with
  | nil => simp only [insertList, List.append_nil, Perm.refl]
  | cons hd tl ih =>
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff] at distinct_both
    refine (insertList_cons_perm distinct_l distinct_toInsert).trans ?_
    rw [insertEntry_of_containsKey_eq_false]
    · refine (Perm.cons _ (ih distinct_l (distinct_toInsert).tail ?_)).trans List.perm_middle.symm
      exact fun a ha => (distinct_both a ha).2
    · simp only [containsKey_insertList, Bool.or_eq_false_iff, ← containsKey_eq_contains_map_fst]
      refine ⟨Bool.not_eq_true _ ▸ fun h => ?_, distinct_toInsert.containsKey_eq_false⟩
      simpa using (distinct_both _ h).1

theorem length_insertList [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (distinct_both : ∀ (a : α), containsKey a l → (toInsert.map Sigma.fst).contains a = false) :
    (insertList l toInsert).length = l.length + toInsert.length := by
  simpa using (perm_insertList distinct_l distinct_toInsert distinct_both).length_eq

theorem length_le_length_insertList [BEq α]
    {l toInsert : List ((a : α) × β a)} :
    l.length ≤ (insertList l toInsert).length := by
  induction toInsert generalizing l with
  | nil => apply Nat.le_refl
  | cons hd tl ih => exact Nat.le_trans length_le_length_insertEntry ih

theorem length_insertList_le [BEq α]
    {l toInsert : List ((a : α) × β a)} :
    (insertList l toInsert).length ≤ l.length + toInsert.length := by
  induction toInsert generalizing l with
  | nil => simp only [insertList, List.length_nil, Nat.add_zero, Nat.le_refl]
  | cons hd tl ih =>
    simp only [insertList, List.length_cons]
    apply Nat.le_trans ih
    rw [Nat.add_comm tl.length 1, ← Nat.add_assoc]
    apply Nat.add_le_add length_insertEntry_le (Nat.le_refl _)

theorem isEmpty_insertList [BEq α]
    {l toInsert : List ((a : α) × β a)} :
    (List.insertList l toInsert).isEmpty = (l.isEmpty && toInsert.isEmpty) := by
  induction toInsert generalizing l with
  | nil => simp [insertList]
  | cons hd tl ih =>
    rw [insertList, List.isEmpty_cons, ih, isEmpty_insertEntry]
    simp

section

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def Prod.toSigma (p : α × β) : ((_ : α) × β) := ⟨p.fst, p.snd⟩

@[simp]
theorem Prod.fst_comp_toSigma :
    Sigma.fst ∘ Prod.toSigma = @Prod.fst α β := by
  apply funext
  simp [Prod.toSigma]

/-- Internal implementation detail of the hash map -/
def insertListConst [BEq α] (l : List ((_ : α) × β)) (toInsert : List (α × β)) : List ((_ : α) × β) :=
  insertList l (toInsert.map Prod.toSigma)

theorem containsKey_insertListConst [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α} :
    containsKey k (insertListConst l toInsert) =
    (containsKey k l || (toInsert.map Prod.fst).contains k) := by
  unfold insertListConst
  rw [containsKey_insertList]
  simp

theorem containsKey_of_containsKey_insertListConst [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (h₁ : containsKey k (insertListConst l toInsert))
    (h₂ : (toInsert.map Prod.fst).contains k = false) : containsKey k l := by
  unfold insertListConst at h₁
  apply containsKey_of_containsKey_insertList h₁
  simpa

theorem getKey?_insertListConst_of_contains_eq_false [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getKey? k (insertListConst l toInsert) = getKey? k l := by
  unfold insertListConst
  apply getKey?_insertList_of_contains_eq_false
  simpa

theorem getKey?_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst) :
    getKey? k' (insertListConst l toInsert) = some k := by
  unfold insertListConst
  apply getKey?_insertList_of_mem k_beq distinct_l
  · simpa [List.pairwise_map]
  · simp only [List.map_map, Prod.fst_comp_toSigma]
    exact mem

theorem getKey_insertListConst_of_contains_eq_false [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false)
    {h} :
    getKey k (insertListConst l toInsert) h =
      getKey k l (containsKey_of_containsKey_insertListConst h not_contains) := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey,
    getKey?_insertListConst_of_contains_eq_false not_contains, getKey?_eq_some_getKey]

theorem getKey_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst)
    {h} :
    getKey k' (insertListConst l toInsert) h = k := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey,
    getKey?_insertListConst_of_mem k_beq distinct_l distinct_toInsert mem]

theorem getKey!_insertListConst_of_contains_eq_false [BEq α] [EquivBEq α] [Inhabited α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getKey! k (insertListConst l toInsert) = getKey! k l := by
  rw [getKey!_eq_getKey?, getKey?_insertListConst_of_contains_eq_false not_contains,
    getKey!_eq_getKey?]

theorem getKey!_insertListConst_of_mem [BEq α] [EquivBEq α] [Inhabited α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    {k k' : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst) :
    getKey! k' (insertListConst l toInsert) = k := by
  rw [getKey!_eq_getKey?, getKey?_insertListConst_of_mem k_beq distinct_l distinct_toInsert mem,
    Option.get!_some]

theorem getKeyD_insertListConst_of_contains_eq_false [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k fallback : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getKeyD k (insertListConst l toInsert) fallback = getKeyD k l fallback := by
  rw [getKeyD_eq_getKey?, getKey?_insertListConst_of_contains_eq_false not_contains,
    getKeyD_eq_getKey?]

theorem getKeyD_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    {k k' fallback : α} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst) :
    getKeyD k' (insertListConst l toInsert) fallback = k := by
  rw [getKeyD_eq_getKey?, getKey?_insertListConst_of_mem k_beq distinct_l distinct_toInsert mem,
    Option.getD_some]

theorem length_insertListConst [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (distinct_both : ∀ (a : α), containsKey a l → (toInsert.map Prod.fst).contains a = false) :
    (insertListConst l toInsert).length = l.length + toInsert.length := by
  unfold insertListConst
  rw [length_insertList distinct_l]
  · simp
  · simpa [List.pairwise_map]
  · simpa using distinct_both

theorem length_le_length_insertListConst [BEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} :
    l.length ≤ (insertListConst l toInsert).length := by
  induction toInsert generalizing l with
  | nil => apply Nat.le_refl
  | cons hd tl ih => exact Nat.le_trans length_le_length_insertEntry ih

theorem length_insertListConst_le [BEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} :
    (insertListConst l toInsert).length ≤ l.length + toInsert.length := by
  unfold insertListConst
  rw [← List.length_map toInsert Prod.toSigma]
  apply length_insertList_le

theorem isEmpty_insertListConst [BEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} :
    (List.insertListConst l toInsert).isEmpty = (l.isEmpty && toInsert.isEmpty) := by
  unfold insertListConst
  rw [isEmpty_insertList, Bool.eq_iff_iff]
  simp

theorem getValue?_insertListConst_of_contains_eq_false [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getValue? k (insertListConst l toInsert) = getValue? k l := by
  unfold insertListConst
  rw [getValue?_eq_getEntry?, getValue?_eq_getEntry?, getEntry?_insertList_of_contains_eq_false]
  rw [containsKey_eq_contains_map_fst]
  simpa

theorem getValue?_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    {k k' : α} (k_beq : k == k') {v : β}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValue? k' (insertListConst l toInsert) = v := by
  unfold insertListConst
  rw [getValue?_eq_getEntry?]
  have : getEntry? k' (insertList l (toInsert.map Prod.toSigma)) =
      getEntry? k' (toInsert.map Prod.toSigma) := by
    apply getEntry?_insertList_of_contains_eq_true distinct_l (by simpa [List.pairwise_map])
    apply containsKey_of_beq _ k_beq
    rw [containsKey_eq_contains_map_fst, List.map_map, Prod.fst_comp_toSigma,
      List.contains_iff_exists_mem_beq]
    exists k
    rw [List.mem_map]
    constructor
    . exists ⟨k, v⟩
    . simp
  rw [this]
  rw [getEntry?_of_mem _ k_beq _]
  . rfl
  · simpa [DistinctKeys.def, List.pairwise_map]
  . simp only [List.mem_map]
    exists (k, v)

theorem getValue_insertListConst_of_contains_eq_false [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    {not_contains : (toInsert.map Prod.fst).contains k = false}
    {h} :
    getValue k (insertListConst l toInsert) h =
    getValue k l (containsKey_of_containsKey_insertListConst h not_contains) := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue, ← getValue?_eq_some_getValue,
    getValue?_insertListConst_of_contains_eq_false not_contains]

theorem getValue_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    {k k' : α} (k_beq : k == k') {v : β}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert)
    {h} :
    getValue k' (insertListConst l toInsert) h = v := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue,
    getValue?_insertListConst_of_mem k_beq distinct_l distinct_toInsert mem]

theorem getValue!_insertListConst_of_contains_eq_false [BEq α] [PartialEquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getValue! k (insertListConst l toInsert) = getValue! k l := by
  simp only [getValue!_eq_getValue?]
  rw [getValue?_insertListConst_of_contains_eq_false not_contains]

theorem getValue!_insertListConst_of_mem [BEq α] [EquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k k' : α} {v: β} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert):
    getValue! k' (insertListConst l toInsert) = v := by
  rw [getValue!_eq_getValue?,
    getValue?_insertListConst_of_mem k_beq distinct_l distinct_toInsert mem, Option.get!_some]

theorem getValueD_insertListConst_of_contains_eq_false [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α} {fallback : β}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getValueD k (insertListConst l toInsert) fallback = getValueD k l fallback := by
  simp only [getValueD_eq_getValue?]
  rw [getValue?_insertListConst_of_contains_eq_false not_contains]

theorem getValueD_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k k' : α} {v fallback: β} (k_beq : k == k')
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert):
    getValueD k' (insertListConst l toInsert) fallback= v := by
  simp only [getValueD_eq_getValue?]
  rw [getValue?_insertListConst_of_mem k_beq distinct_l distinct_toInsert mem, Option.getD_some]

/-- Internal implementation detail of the hash map -/
def insertListIfNewUnit [BEq α] (l: List ((_ : α) × Unit)) (toInsert: List α) :
    List ((_ : α) × Unit) :=
  match toInsert with
  | .nil => l
  | .cons hd tl => insertListIfNewUnit (insertEntryIfNew hd () l) tl

theorem insertListIfNewUnit_perm_of_perm_first [BEq α] [EquivBEq α] {l1 l2 : List ((_ : α) × Unit)}
    {toInsert : List α } (h : Perm l1 l2) (distinct : DistinctKeys l1) :
    Perm (insertListIfNewUnit l1 toInsert) (insertListIfNewUnit l2 toInsert) := by
  induction toInsert generalizing l1 l2 with
  | nil => simp [insertListIfNewUnit, h]
  | cons hd tl ih =>
    simp only [insertListIfNewUnit]
    apply ih
    · simp only [insertEntryIfNew, cond_eq_if]
      have contains_eq : containsKey hd l1 = containsKey hd l2 := containsKey_of_perm h
      rw [contains_eq]
      by_cases contains_hd: containsKey hd l2 = true
      · simp only [contains_hd, ↓reduceIte]
        exact h
      · simp only [contains_hd, Bool.false_eq_true, ↓reduceIte, List.perm_cons]
        exact h
    · apply DistinctKeys.insertEntryIfNew distinct

theorem DistinctKeys.insertListIfNewUnit [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × Unit)}
    {toInsert : List α} (distinct: DistinctKeys l):
    DistinctKeys (insertListIfNewUnit l toInsert) := by
  induction toInsert generalizing l with
  | nil => simp [List.insertListIfNewUnit, distinct]
  | cons hd tl ih =>
    simp only [List.insertListIfNewUnit]
    apply ih (insertEntryIfNew distinct)

theorem getEntry?_insertListIfNewUnit [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × Unit)}
    {toInsert : List α} {k : α} :
    getEntry? k (insertListIfNewUnit l toInsert) =
      (getEntry? k l).or (getEntry? k (toInsert.map (⟨·, ()⟩))) := by
  induction toInsert generalizing l with
  | nil => simp [insertListIfNewUnit]
  | cons hd tl ih =>
    simp only [insertListIfNewUnit, ih, getEntry?_insertEntryIfNew, List.map_cons,
      getEntry?_cons]
    cases hhd : hd == k
    · simp
    · cases hc : containsKey hd l
      · simp only [Bool.not_false, Bool.and_self, ↓reduceIte, Option.some_or, cond_true,
          Option.or_some', Option.some.injEq]
        rw [getEntry?_eq_none.2, Option.getD_none]
        rwa [← containsKey_congr hhd]
      · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, cond_true,
          Option.or_some', getEntry?_eq_none]
        rw [containsKey_congr hhd, containsKey_eq_isSome_getEntry?] at hc
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hc
        simp [hv]

theorem DistinctKeys.mapUnit [BEq α]
    {l : List α} (distinct: l.Pairwise (fun a b => (a == b) = false)) :
    DistinctKeys (l.map (⟨·, ()⟩)) := by
  rw [DistinctKeys.def]
  refine List.Pairwise.map ?_ ?_ distinct
  simp

theorem getEntry?_insertListIfNewUnit_of_contains_eq_false [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α } {k : α}
    (not_contains : toInsert.contains k = false) :
    getEntry? k (insertListIfNewUnit l toInsert) = getEntry? k l := by
  induction toInsert generalizing l with
  | nil => simp [insertListIfNewUnit]
  | cons h t ih =>
    unfold insertListIfNewUnit
    simp only [List.contains_cons, Bool.or_eq_false_iff] at not_contains
    rw [ih not_contains.right, getEntry?_insertEntryIfNew]
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, ite_eq_right_iff, and_imp]
    intro h'
    rw [BEq.comm, And.left not_contains] at h'
    simp at h'

theorem containsKey_insertListIfNewUnit [BEq α] [PartialEquivBEq α] {l : List ((_ : α) × Unit)}
    {toInsert : List α} {k : α} :
    containsKey k (insertListIfNewUnit l toInsert) = (containsKey k l || toInsert.contains k) := by
  induction toInsert generalizing l with
  | nil => simp [insertListIfNewUnit]
  | cons hd tl ih =>
    simp only [insertListIfNewUnit, List.contains_cons]
    rw [ih, containsKey_insertEntryIfNew]
    rw [Bool.or_comm (hd == k), Bool.or_assoc, BEq.comm (a:=hd)]

theorem containsKey_of_containsKey_insertListIfNewUnit [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α} {k : α}
    (h₂ : toInsert.contains k = false) : containsKey k (insertListIfNewUnit l toInsert) →
    containsKey k l := by
  intro h₁
  rw [containsKey_insertListIfNewUnit, h₂] at h₁; simp at h₁; exact h₁

theorem getKey?_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α} {k : α}
    (h': containsKey k l = false) (h : toInsert.contains k = false) :
    getKey? k (insertListIfNewUnit l toInsert) = none := by
  rw [getKey?_eq_getEntry?,
    getEntry?_insertListIfNewUnit_of_contains_eq_false h, Option.map_eq_none', getEntry?_eq_none]
  exact h'

theorem getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k k' : α} (k_beq : k == k')
    (mem' : containsKey k l = false)
    (distinct : toInsert.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ toInsert):
    getKey? k' (insertListIfNewUnit l toInsert) = some k := by
  simp only [getKey?_eq_getEntry?, getEntry?_insertListIfNewUnit, Option.map_eq_some',
    Option.or_eq_some, getEntry?_eq_none]
  exists ⟨k, ()⟩
  simp only [and_true]
  right
  constructor
  · rw [containsKey_congr k_beq] at mem'
    exact mem'
  · apply getEntry?_of_mem (DistinctKeys.mapUnit distinct) k_beq
    simp only [List.mem_map]
    exists k

theorem getKey?_insertListIfNewUnit_of_contains [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k : α}
    (h : containsKey k l = true):
    getKey? k (insertListIfNewUnit l toInsert) = getKey? k l := by
  rw [containsKey_eq_isSome_getEntry?] at h
  simp [getKey?_eq_getEntry?, getEntry?_insertListIfNewUnit, Option.or_of_isSome h]

theorem getKey_insertListIfNewUnit_of_contains_eq_false_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k k' : α} (k_beq : k == k')
    {h} (contains_eq_false : containsKey k l = false)
    (distinct : toInsert.Pairwise (fun a b => (a == b) = false))
    (mem : k ∈ toInsert) :
    getKey k' (insertListIfNewUnit l toInsert) h = k := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey,
    getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem k_beq contains_eq_false distinct mem]

theorem getKey_insertListIfNewUnit_of_contains [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k : α}
    (contains : containsKey k l = true) {h}:
    getKey k (insertListIfNewUnit l toInsert) h = getKey k l contains := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey, ← getKey?_eq_some_getKey,
    getKey?_insertListIfNewUnit_of_contains contains]

theorem getKey!_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false [BEq α] [EquivBEq α]
    [Inhabited α] {l : List ((_ : α) × Unit)} {toInsert : List α} {k : α}
    (contains_eq_false : containsKey k l = false)
    (contains_eq_false' : toInsert.contains k = false) :
    getKey! k (insertListIfNewUnit l toInsert) = default := by
  rw [getKey!_eq_getKey?, getKey?_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false
    contains_eq_false contains_eq_false']
  simp

theorem getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem [BEq α] [EquivBEq α] [Inhabited α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k k' : α} (k_beq : k == k')
    (h : containsKey k l = false)
    (distinct : toInsert.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ toInsert) :
    getKey! k' (insertListIfNewUnit l toInsert) = k := by
  rw [getKey!_eq_getKey?,
    getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem k_beq h distinct mem, Option.get!_some]

theorem getKey!_insertListIfNewUnit_of_contains [BEq α] [EquivBEq α] [Inhabited α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k : α}
    (h : containsKey k l = true) :
    getKey! k (insertListIfNewUnit l toInsert) = getKey! k l  := by
  rw [getKey!_eq_getKey?, getKey?_insertListIfNewUnit_of_contains h, getKey!_eq_getKey?]

theorem getKeyD_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α} {k fallback : α}
    (contains_eq_false : containsKey k l = false) (contains_eq_false' : toInsert.contains k = false) :
    getKeyD k (insertListIfNewUnit l toInsert) fallback = fallback := by
  rw [getKeyD_eq_getKey?, getKey?_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false
    contains_eq_false contains_eq_false']
  simp

theorem getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k k' fallback : α} (k_beq : k == k')
    (h : containsKey k l = false)
    (distinct : toInsert.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ toInsert) :
    getKeyD k' (insertListIfNewUnit l toInsert) fallback = k := by
  rw [getKeyD_eq_getKey?, getKey?_insertListIfNewUnit_of_contains_eq_false_of_mem k_beq h
    distinct mem, Option.getD_some]

theorem getKeyD_insertListIfNewUnit_of_contains [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    {k fallback : α}
    (contains : containsKey k l = true) :
    getKeyD k (insertListIfNewUnit l toInsert) fallback = getKeyD k l fallback := by
  rw [getKeyD_eq_getKey?,
    getKey?_insertListIfNewUnit_of_contains contains, getKeyD_eq_getKey?]

theorem length_insertListIfNewUnit [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}
    (distinct_l : DistinctKeys l)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a == b) = false))
    (distinct_both : ∀ (a : α), containsKey a l → toInsert.contains a = false) :
    (insertListIfNewUnit l toInsert).length = l.length + toInsert.length := by
  induction toInsert generalizing l with
  | nil => simp [insertListIfNewUnit]
  | cons hd tl ih =>
    simp only [insertListIfNewUnit, List.length_cons]
    rw [ih]
    · rw [length_insertEntryIfNew]
      specialize distinct_both hd
      simp only [List.contains_cons, BEq.refl, Bool.true_or, and_true,
        Bool.not_eq_true] at distinct_both
      cases eq : containsKey hd l with
      | true => simp [eq] at distinct_both
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_assoc, Nat.add_comm 1 _]
    · apply DistinctKeys.insertEntryIfNew distinct_l
    · simp only [pairwise_cons] at distinct_toInsert
      apply And.right distinct_toInsert
    · intro a
      simp only [List.contains_cons, Bool.or_eq_true, not_and, not_or,
        Bool.not_eq_true] at distinct_both
      rw [containsKey_insertEntryIfNew]
      simp only [Bool.or_eq_true]
      intro h
      cases h with
      | inl h =>
        simp only [pairwise_cons] at distinct_toInsert
        rw [List.contains_eq_any_beq]
        simp only [List.any_eq_false, Bool.not_eq_true]
        intro x x_mem
        rcases distinct_toInsert with ⟨left,_⟩
        specialize left x x_mem
        apply BEq.neq_of_beq_of_neq
        apply BEq.symm h
        exact left
      | inr h =>
        specialize distinct_both a h
        rw [Bool.or_eq_false_iff] at distinct_both
        apply And.right distinct_both

theorem length_le_length_insertListIfNewUnit [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}:
    l.length ≤ (insertListIfNewUnit l toInsert).length := by
  induction toInsert generalizing l with
  | nil => apply Nat.le_refl
  | cons hd tl ih => exact Nat.le_trans length_le_length_insertEntryIfNew ih

theorem length_insertListIfNewUnit_le [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α}:
    (insertListIfNewUnit l toInsert).length ≤ l.length + toInsert.length := by
  induction toInsert generalizing l with
  | nil => simp only [insertListIfNewUnit, List.length_nil, Nat.add_zero, Nat.le_refl]
  | cons hd tl ih =>
    simp only [insertListIfNewUnit, List.length_cons]
    apply Nat.le_trans ih
    rw [Nat.add_comm tl.length 1, ← Nat.add_assoc]
    apply Nat.add_le_add _ (Nat.le_refl _)
    apply length_insertEntryIfNew_le

theorem isEmpty_insertListIfNewUnit [BEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α} :
    (List.insertListIfNewUnit l toInsert).isEmpty = (l.isEmpty && toInsert.isEmpty) := by
  induction toInsert generalizing l with
  | nil => simp [insertListIfNewUnit]
  | cons hd tl ih =>
    rw [insertListIfNewUnit, List.isEmpty_cons, ih, isEmpty_insertEntryIfNew]
    simp

theorem getValue?_list_unit [BEq α] {l : List ((_ : α) × Unit)} {k : α}:
    getValue? k l = if containsKey k l = true then some () else none := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [getValue?, containsKey, Bool.or_eq_true, Bool.cond_eq_ite_iff]
    by_cases hd_k: (hd.fst == k) = true
    · simp [hd_k]
    · simp [hd_k, ih]

theorem getValue?_insertListIfNewUnit [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α} {k : α}:
    getValue? k (insertListIfNewUnit l toInsert) =
    if containsKey k l ∨ toInsert.contains k then some () else none := by
  simp [containsKey_insertListIfNewUnit, getValue?_list_unit]

end

private theorem Option.map_cast_apply {γ γ' : Type u} (h : γ = γ') (x : Option γ) :
    Option.map (cast h) x = cast (congrArg Option h) x := by
  cases h; cases x <;> simp

private theorem cast_eq_id {α : Type u} : cast (rfl : α = α) = id := by rfl

private theorem function_id_comp {α : Type u} {β : Type v} {f : α → β} :
  id ∘ f = f := rfl

section Alter

section Dependent

variable [BEq α] [LawfulBEq α]

/-- Internal implementation detail of the hash map -/
def alterKey (k : α) (f : Option (β k) → Option (β k))
    (l : List ((a : α) × β a)) : List ((a : α) × β a) :=
  match f (getValueCast? k l) with
  | none => eraseKey k l
  | some v => insertEntry k v l

theorem length_alterKey {k : α} {f : Option (β k) → Option (β k)} {l : List ((a : α) × β a)} :
    (alterKey k f l).length =
      if h : containsKey k l then
        if f (getValueCast k l h) |>.isSome then l.length else l.length - 1
      else
        if f none |>.isSome then l.length + 1 else l.length := by
  rw [alterKey]
  cases h : getValueCast? k l <;> split <;> simp_all [length_eraseKey, length_insertEntry,
    containsKey_eq_isSome_getValueCast?, ← getValueCast?_eq_some_getValueCast]

theorem length_alterKey' {k : α} {f : Option (β k) → Option (β k)} {l : List ((a : α) × β a)} :
    (alterKey k f l).length =
      if containsKey k l && (f (getValueCast? k l)).isNone then
        l.length - 1
      else if !containsKey k l && (f (getValueCast? k l)).isSome then
        l.length + 1
      else
        l.length := by
  rw [alterKey]
  cases h : containsKey k l <;> split <;> split <;> simp_all [length_eraseKey, length_insertEntry]

theorem alterKey_cons_perm {k : α} {f : Option (β k) → Option (β k)} {k' : α} {v' : β k'}
    {l : List ((a : α) × β a)} : Perm (alterKey k f (⟨k', v'⟩ :: l))
      (if hk : k' == k then
        match f (some (cast (congrArg β (eq_of_beq hk)) v')) with
          | none => l
          | some v => ⟨k, v⟩ :: l
        else
          ⟨k', v'⟩ :: alterKey k f l) := by
  rw [alterKey]
  by_cases hk' : k' == k
  · simp only [hk', ↓reduceDIte]
    rw [getValueCast?_cons_of_true hk', eraseKey_cons_of_beq hk']
    simp [insertEntry_cons_of_beq hk']
  · simp only [hk', Bool.false_eq_true, ↓reduceDIte]
    rw [Bool.not_eq_true] at hk'
    rw [getValueCast?_cons_of_false hk', eraseKey_cons_of_false hk', alterKey]
    split
    · rfl
    · exact insertEntry_cons_of_false hk'

theorem isEmpty_alterKey_eq_isEmpty_eraseKey {k : α} {f : Option (β k) → Option (β k)}
    {l : List ((a : α) × β a)} :
    (alterKey k f l).isEmpty = ((eraseKey k l).isEmpty && (f (getValueCast? k l)).isNone) := by
  rw [alterKey, Bool.eq_iff_iff, Bool.and_eq_true_iff]
  cases f (getValueCast? k l)
  repeat simp [isEmpty_insertEntry]

theorem isEmpty_alterKey {k : α} {f : Option (β k) → Option (β k)} {l : List ((a : α) × β a)} :
    (alterKey k f l).isEmpty = ((l.isEmpty || (l.length == 1 && containsKey k l)) &&
      (f (getValueCast? k l)).isNone) := by
  rw [isEmpty_alterKey_eq_isEmpty_eraseKey, isEmpty_eraseKey]

theorem alterKey_of_perm {a : α} {f : Option (β a) → Option (β a)} {l l' : List ((a : α) × β a)}
    (hl : DistinctKeys l) (hp : Perm l l') : Perm (alterKey a f l) (alterKey a f l') := by
  simp only [alterKey, getValueCast?_of_perm hl hp]
  split
  · exact eraseKey_of_perm hl hp
  · exact insertEntry_of_perm hl hp

theorem alterKey_append_of_containsKey_right_eq_false {a : α} {f : Option (β a) → Option (β a)}
    {l l' : List ((a : α) × β a)} (hc : containsKey a l' = false) :
    alterKey a f (l ++ l') = alterKey a f l ++ l' := by
  simp only [alterKey, getValueCast?_append_of_containsKey_eq_false hc,
    eraseKey_append_of_containsKey_right_eq_false hc, insertEntry_append_of_not_contains_right hc]
  split <;> rfl

@[simp]
theorem alterKey_nil {a : α} {f : Option (β a) → Option (β a)} :
    alterKey a f [] = match f none with
| none => []
| some b => [⟨a, b⟩] := rfl

theorem containsKey_alterKey_self {a : α} {f : Option (β a) → Option (β a)}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    containsKey a (alterKey a f l) = (f (getValueCast? a l)).isSome := by
  match l with
  | [] =>
    simp only [getValueCast?_nil, Bool.coe_iff_coe, alterKey_nil]
    cases f none <;> simp
  | x :: xs =>
    simp only [alterKey, Bool.coe_iff_coe]
    cases f (getValueCast? a (x :: xs))
    · simp only [hl, Option.isSome_none, containsKey_eraseKey_self]
    · simp only [containsKey_insertEntry, BEq.refl, Bool.true_or, Option.isSome_some]

theorem containsKey_alterKey {k k' : α} {f : Option (β k) → Option (β k)}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    containsKey k' (alterKey k f l) =
      if k == k' then
        f (getValueCast? k l) |>.isSome
      else
        containsKey k' l := by
  split
  · next h =>
    rw [← containsKey_congr h, containsKey_alterKey_self hl]
  · next h =>
    rw [alterKey]
    cases f (getValueCast? k l)
    · simp [containsKey_eraseKey_of_false (Bool.not_eq_true _ ▸ h)]
    · simp_all

theorem DistinctKeys.alterKey {a : α} {f : Option (β a) → Option (β a)}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) : DistinctKeys (alterKey a f l) := by
  dsimp only [List.alterKey]
  split
  · exact DistinctKeys.eraseKey hl
  · exact DistinctKeys.insertEntry hl

theorem mem_alterKey_of_key_ne {a : α} {f : Option (β a) → Option (β a)}
    {l : List ((a : α) × β a)} (p : (a : α) × β a) (hne : p.1 ≠ a) :
    p ∈ alterKey a f l ↔ p ∈ l := by
  rw [alterKey]
  split <;> simp only [mem_eraseKey_of_key_ne p hne, mem_insertEntry_of_key_ne p hne]

theorem getValueCast?_alterKey (k k' : α) (f : Option (β k) → Option (β k))
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) : getValueCast? k' (alterKey k f l) =
      if h : k == k' then
        cast (congrArg (Option ∘ β) (eq_of_beq h)) (f (getValueCast? k l))
      else
        getValueCast? k' l := by
  split
  · next heq =>
    cases eq_of_beq heq
    simp only [Function.comp_apply, cast_eq]
    rw [alterKey]
    split
    · next hnone =>
      simp only [getValueCast?_eraseKey_self hl, hnone]
    · next hsome =>
      rw [hsome, getValueCast?_insertEntry_self]
  · next heq =>
    rw [alterKey]
    split
    · next hnone =>
      simp only [heq, hnone, hl, beq_iff_eq, getValueCast?_eraseKey, ite_false, Bool.false_eq_true,
        reduceIte]
    · next hsome =>
      simp only [beq_iff_eq, getValueCast?_insertEntry, dite_false, heq, Bool.false_eq_true]

theorem getValueCast_alterKey (k k' : α) (f : Option (β k) → Option (β k))
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) (hc : containsKey k' (alterKey k f l)) :
    getValueCast k' (alterKey k f l) hc =
      if h : k == k' then
        haveI hc' : (f (getValueCast? k l)).isSome := by
          rwa [containsKey_alterKey hl, if_pos h] at hc
        cast (congrArg β (eq_of_beq h)) <| (f (getValueCast? k l)).get hc'
      else
        haveI hc' : containsKey k' l := by rwa [containsKey_alterKey hl, if_neg h] at hc
        getValueCast k' l hc' := by
  have := getValueCast?_alterKey  k k' f l hl
  rw [getValueCast?_eq_some_getValueCast hc] at this
  split
  · next heq =>
    cases eq_of_beq heq
    apply Option.some_inj.mp
    simp_all
  · next heq =>
    apply Option.some_inj.mp
    simp_all only [Bool.false_eq_true, Function.comp_apply, dite_false]
    rw [getValueCast?_eq_some_getValueCast]

theorem getValueCast_alterKey_self (k : α) (f : Option (β k) → Option (β k))
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) (hc : containsKey k (alterKey k f l)) :
    haveI hc' : (f (getValueCast? k l)).isSome := by
      rwa [containsKey_alterKey hl, beq_self_eq_true] at hc
    getValueCast k (alterKey k f l) hc = (f (getValueCast? k l)).get hc' := by
  rw [getValueCast_alterKey _ _ _ _ hl]
  simp

theorem getValueCast!_alterKey {k k' : α} [Inhabited (β k')] {f : Option (β k) → Option (β k)}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) : getValueCast! k' (alterKey k f l) =
      if heq : k == k' then
        (f (getValueCast? k l)).map (cast (congrArg β <| eq_of_beq heq)) |>.get!
      else
        getValueCast! k' l := by
  simp only [hl, getValueCast!_eq_getValueCast?, getValueCast?_alterKey, beq_iff_eq,
    Function.comp_apply]
  split
  · next heq =>
    cases eq_of_beq heq
    simp only [cast_eq, Option.map_cast_apply]
  · rfl

theorem getValueCastD_alterKey {k k' : α} {fallback : β k'} {f : Option (β k) → Option (β k)}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) : getValueCastD k' (alterKey k f l) fallback =
      if heq : k == k' then
        f (getValueCast? k l) |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        getValueCastD k' l fallback := by
  simp only [getValueCastD_eq_getValueCast?, hl, getValueCast?_alterKey, beq_iff_eq,
    Function.comp_apply, apply_dite (Option.getD · fallback), Option.map_cast_apply]

theorem getKey?_alterKey {k k' : α} {f : Option (β k) → Option (β k)} (l : List ((a : α) × β a))
    (hl : DistinctKeys l) :
    getKey? k' (alterKey k f l) =
      if k == k' then
        if (f (getValueCast? k l)).isSome then some k else none
      else
        getKey? k' l := by
  rw [alterKey]
  split <;> next heq => simp [hl, heq, getKey?_eraseKey, getKey?_insertEntry]

theorem getKey!_alterKey [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKey! k' (alterKey k f l) =
      if k == k' then
        if (f (getValueCast? k l)).isSome then k else default
      else
        getKey! k' l := by
  simp only [getKey!_eq_getKey?, hl, getKey?_alterKey, beq_iff_eq]
  split
  · next heq =>
    cases eq_of_beq heq
    split <;> rfl
  · next heq =>
    rfl

theorem getKey_alterKey [Inhabited α] {k k' : α} {f : Option (β k) → Option (β k)}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) (hc : containsKey k' (alterKey k f l)) :
    getKey k' (alterKey k f l) hc =
      if heq : k == k' then
        k
      else
        haveI h' : containsKey k' l := by rwa [containsKey_alterKey hl, if_neg heq] at hc
        getKey k' l h' := by
  have := getKey?_alterKey (f := f) (k' := k') _ hl
  rw [getKey?_eq_some_getKey hc] at this
  split
  · next heq =>
    cases eq_of_beq heq
    apply Option.some_inj.mp
    simp_all
  · next heq =>
    apply Option.some_inj.mp
    simp_all only [Bool.false_eq_true, ite_false]
    rw [getKey?_eq_some_getKey]

theorem getKeyD_alterKey {k k' fallback : α} {f : Option (β k) → Option (β k)}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKeyD k' (alterKey k f l) fallback =
      if k == k' then
        if (f (getValueCast? k l)).isSome then k else fallback
      else
        getKeyD k' l fallback := by
  simp only [hl, getKeyD_eq_getKey?, getKey?_alterKey, beq_iff_eq, Function.comp_apply]
  split
  · next heq =>
    cases eq_of_beq heq
    split <;> rfl
  · rfl

end Dependent

namespace Const

variable [BEq α]

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def alterKey [BEq α] (k : α) (f : Option β → Option β)
    (l : List ((_ : α) × β)) : List ((_ : α) × β) :=
  match f (getValue? k l) with
  | none => eraseKey k l
  | some v => insertEntry k v l

theorem length_alterKey {k : α} {f : Option β → Option β} {l : List ((_ : α) × β)} :
    (alterKey k f l).length =
      if h : containsKey k l then
        if f (some (getValue k l h)) |>.isSome then l.length else l.length - 1
      else
        if f none |>.isSome then l.length + 1 else l.length := by
  rw [alterKey]
  cases h : getValue? k l <;> split <;> simp_all [length_eraseKey, length_insertEntry,
    containsKey_eq_isSome_getValue?, ← getValue?_eq_some_getValue, -getValue?_eq_none]

theorem length_alterKey' {k : α} {f : Option β → Option β} {l : List ((_ : α) × β)} :
    (alterKey k f l).length =
      if containsKey k l && (f (getValue? k l)).isNone then
        l.length - 1
      else if !containsKey k l && (f (getValue? k l)).isSome then
        l.length + 1
      else
        l.length := by
  rw [alterKey]
  cases h : containsKey k l <;> split <;> split <;> simp_all [length_eraseKey, length_insertEntry]

theorem length_alterKey_eq_add_one {k : α} {f : Option β → Option β} {l : List ((_ : α) × β)}
    (h : containsKey k l = false) (h' : (f (getValue? k l)).isSome) :
    (alterKey k f l).length = l.length + 1 := by
  simp [length_alterKey', h, h']

theorem length_alterKey_eq_sub_one {k : α} {f : Option β → Option β} {l : List ((_ : α) × β)}
    (h : containsKey k l) (h' : (f (getValue? k l)).isNone) :
    (alterKey k f l).length = l.length - 1 := by
  simp [length_alterKey', h, h']

theorem length_alterKey_eq_self {k : α} {f : Option β → Option β} {l : List ((_ : α) × β)}
    (h : containsKey k l) (h' : (f (getValue? k l)).isSome) :
    (alterKey k f l).length = l.length := by
  simp [length_alterKey', h, Option.isSome_iff_ne_none.mp h']

theorem length_alterKey_eq_self' {k : α} {f : Option β → Option β} {l : List ((_ : α) × β)}
    (h : containsKey k l = false) (h' : (f (getValue? k l)).isNone) :
    (alterKey k f l).length = l.length := by
  simp [length_alterKey', h, h']

theorem alterKey_cons_perm {k : α} {f : Option β → Option β} {k' : α} {v' : β}
    {l : List ((_ : α) × β)} :
    Perm (alterKey k f (⟨k', v'⟩ :: l))
      (if k' == k then
        match f (some v') with
          | none => l
          | some v => ⟨k, v⟩ :: l
        else
          ⟨k', v'⟩ :: alterKey k f l) := by
  rw [alterKey]
  by_cases hk' : k' == k
  · simp only [hk', ↓reduceDIte]
    rw [getValue?_cons_of_true hk', eraseKey_cons_of_beq hk']
    simp [insertEntry_cons_of_beq hk']
  · simp only [hk', Bool.false_eq_true, ↓reduceDIte]
    rw [Bool.not_eq_true] at hk'
    rw [getValue?_cons_of_false hk', eraseKey_cons_of_false hk', alterKey]
    split
    · rfl
    · simp [insertEntry_cons_of_false hk']

theorem isEmpty_alterKey_eq_isEmpty_eraseKey {k : α} {f : Option β → Option β}
    {l : List ((_ : α) × β)} :
    (alterKey k f l).isEmpty = ((eraseKey k l).isEmpty && (f (getValue? k l)).isNone) := by
  simp only [alterKey, List.isEmpty_iff]
  split <;> { next heq => simp [heq] }

theorem isEmpty_alterKey {k : α} {f : Option β → Option β} {l : List ((_ : α) × β)} :
    (alterKey k f l).isEmpty = ((l.isEmpty || (l.length == 1 && containsKey k l)) &&
      (f (getValue? k l)).isNone) := by
  rw [isEmpty_alterKey_eq_isEmpty_eraseKey, isEmpty_eraseKey]

theorem alterKey_of_perm [EquivBEq α] {a : α} {f : Option β → Option β} {l l' : List ((_ : α) × β)}
    (hl : DistinctKeys l) (hp : Perm l l') :
    Perm (alterKey a f l) (alterKey a f l') := by
  simp only [alterKey, getValue?_of_perm hl hp]
  split
  · exact eraseKey_of_perm hl hp
  · exact insertEntry_of_perm hl hp

theorem alterKey_append_of_containsKey_right_eq_false {a : α} {f : Option β → Option β}
    {l l' : List ((_ : α) × β)} (hc : containsKey a l' = false) :
    alterKey a f (l ++ l') = alterKey a f l ++ l' := by
  simp only [alterKey, getValue?_append_of_containsKey_eq_false hc,
    eraseKey_append_of_containsKey_right_eq_false hc, insertEntry_append_of_not_contains_right hc]
  split <;> rfl

@[simp]
theorem alterKey_nil {a : α} {f : Option β → Option β} :
    alterKey a f [] = match f none with
| none => []
| some b => [⟨a, b⟩] := rfl

theorem containsKey_alterKey_self [EquivBEq α] {a : α} {f : Option β → Option β}
    {l : List ((_ : α) × β)} (hl : DistinctKeys l) :
    containsKey a (alterKey a f l) = (f (getValue? a l)).isSome := by
  match l with
  | [] =>
    simp only [getValue?_nil, Bool.coe_iff_coe, alterKey_nil]
    split <;> { rename_i heq; simp [heq] }
  | x :: xs =>
    simp only [alterKey, Bool.coe_iff_coe]
    split
    · next heq =>
      simp only [hl, heq, Option.isSome_none, containsKey_eraseKey_self]
    · next heq =>
      simp only [containsKey_insertEntry, BEq.refl, Bool.true_or, heq, Option.isSome_some]

theorem mem_alterKey_of_key_not_beq [EquivBEq α] {β : Type v} {a : α} {f : Option β → Option β}
    {l : List ((_ : α) × β)} (p : (_ : α) × β) (hne : (p.1 == a) = false) :
    p ∈ alterKey a f l ↔ p ∈ l := by
  rw [alterKey]
  split <;> simp only
    [mem_eraseKey_of_key_beq_eq_false p hne, mem_insertEntry_of_key_beq_eq_false p hne]

theorem containsKey_alterKey [EquivBEq α] {k k' : α} {f : Option β → Option β}
    {l : List ((_ : α) × β)} (hl : DistinctKeys l) :
    containsKey k' (alterKey k f l) =
      if k == k' then
        f (getValue? k l) |>.isSome
      else
        containsKey k' l := by
  split
  · next h =>
    rw [← containsKey_congr h]
    exact containsKey_alterKey_self hl
  · next h =>
    rw [alterKey]
    split
    · next heq =>
      simp only [containsKey_eraseKey_of_false (Bool.not_eq_true _ ▸ h)]
    · next heq =>
      simp_all only [Bool.not_eq_true, containsKey_insertEntry, Bool.false_or]

theorem getValue?_alterKey [EquivBEq α] (k k' : α) (f : Option β → Option β)
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) : getValue? k' (alterKey k f l) =
      if k == k' then
        f (getValue? k l)
      else
        getValue? k' l := by
  split
  · next heq =>
    rw [alterKey]
    split
    · next hnone =>
      simp only [getValue?_eraseKey_of_beq hl heq, hnone]
    · next hsome =>
      rw [hsome, getValue?_insertEntry_of_beq heq]
  · next heq =>
    rw [alterKey]
    split
    · next hnone =>
      simp only [heq, hnone, hl, beq_iff_eq, getValue?_eraseKey, ite_false, Bool.false_eq_true,
        reduceIte]
    · next hsome =>
      simp only [getValue?_insertEntry, heq, Bool.false_eq_true, reduceIte]

theorem getValue_alterKey [EquivBEq α] (k k' : α) (f : Option β → Option β) (l : List ((_ : α) × β))
    (hl : DistinctKeys l) (hc : containsKey k' (alterKey k f l)) :
    getValue k' (alterKey k f l) hc =
      if h : k == k' then
        haveI hc' : (f (getValue? k l)).isSome := by rwa [containsKey_alterKey hl, if_pos h] at hc
        (f (getValue? k l)).get hc'
      else
        haveI hc' : containsKey k' l := by rwa [containsKey_alterKey hl, if_neg h] at hc
        getValue k' l hc' := by
  have := getValue?_alterKey  k k' f l hl
  rw [getValue?_eq_some_getValue hc] at this
  split
  · next heq =>
    apply Option.some_inj.mp
    simp_all
  · next heq =>
    apply Option.some_inj.mp
    simp_all only [Bool.false_eq_true, ite_false]
    rw [getValue?_eq_some_getValue]

theorem getValue_alterKey_self [EquivBEq α] (k : α) (f : Option β → Option β)
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) (hc : containsKey k (alterKey k f l)) :
    haveI hc' : (f (getValue? k l)).isSome := by rwa [containsKey_alterKey hl, BEq.refl] at hc
    getValue k (alterKey k f l) hc = (f (getValue? k l)).get hc' := by
  rw [getValue_alterKey _ _ _ _ hl]
  simp

theorem getValue!_alterKey [EquivBEq α] {k k' : α} [Inhabited β] {f : Option β → Option β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getValue! k' (alterKey k f l) =
      if k == k' then
        (f (getValue? k l)).get!
      else
        getValue! k' l := by
  simp only [hl, getValue!_eq_getValue?, getValue?_alterKey, beq_iff_eq, Function.comp_apply,
    apply_ite Option.get!]

theorem getValueD_alterKey [EquivBEq α] {k k' : α} {fallback : β} {f : Option β → Option β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getValueD k' (alterKey k f l) fallback =
      if k == k' then
        f (getValue? k l) |>.getD fallback
      else
        getValueD k' l fallback := by
  simp only [hl, getValueD_eq_getValue?, getValue?_alterKey, beq_iff_eq, Function.comp_apply,
    apply_ite (Option.getD · fallback)]

theorem getKey?_alterKey [EquivBEq α] {k k' : α} {f : Option β → Option β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) :
    getKey? k' (alterKey k f l) =
      if k == k' then
        if (f (getValue? k l)).isSome then some k else none
      else
        getKey? k' l := by
  rw [alterKey]
  split <;> next heq => simp [hl, heq, getKey?_eraseKey, getKey?_insertEntry]

theorem getKey!_alterKey [EquivBEq α] [Inhabited α] {k k' : α} {f : Option β → Option β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getKey! k' (alterKey k f l) =
      if k == k' then
        if (f (getValue? k l)).isSome then k else default
      else
        getKey! k' l := by
  simp [hl, getKey!_eq_getKey?, getKey?_alterKey, apply_ite Option.get!]

theorem getKey_alterKey [EquivBEq α] [Inhabited α] {k k' : α} {f : Option β → Option β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) (hc : containsKey k' (alterKey k f l)) :
    getKey k' (alterKey k f l) hc =
      if heq : k == k' then
        k
      else
        haveI h' : containsKey k' l := by rwa [containsKey_alterKey hl, if_neg heq] at hc
        getKey k' l h' := by
  have := getKey?_alterKey (f := f) (k := k) (k' := k') _ hl
  rw [getKey?_eq_some_getKey hc] at this
  split
  · next heq =>
    apply Option.some_inj.mp
    simp_all
  · next heq =>
    apply Option.some_inj.mp
    simp_all only [Bool.false_eq_true, ite_false]
    rw [getKey?_eq_some_getKey]

theorem getKeyD_alterKey [EquivBEq α] {k k' fallback : α} {f : Option β → Option β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getKeyD k' (alterKey k f l) fallback =
      if k == k' then
        if (f (getValue? k l)).isSome then k else fallback
      else
        getKeyD k' l fallback := by
  simp only [hl, getKeyD_eq_getKey?, getKey?_alterKey, beq_iff_eq, Function.comp_apply]
  split
  · next heq =>
    split <;> rfl
  · rfl

end Const

theorem constAlterKey_eq_alterKey [BEq α] [LawfulBEq α] {β : Type v} {k : α}
    {f : Option β → Option β} {l : List ((_ : α) × β)} : Const.alterKey k f l = alterKey k f l := by
  rw [alterKey, Const.alterKey, getValue?_eq_getValueCast?]
  cases f (getValueCast? k l) <;> rfl

theorem DistinctKeys.constAlterKey [BEq α] [EquivBEq α] {β : Type v} {a : α}
    {f : Option β → Option β} {l : List ((_ : α) × β)} (hl : DistinctKeys l) :
    DistinctKeys (List.Const.alterKey a f l) := by
  dsimp only [List.Const.alterKey]
  split
  · exact DistinctKeys.eraseKey hl
  · exact DistinctKeys.insertEntry hl

end Alter

section Modify

/-- Internal implementation detail of the hash map -/
def modifyKey [BEq α] [LawfulBEq α] (k : α) (f : β k → β k)
    (l : List ((a : α) × β a)) : List ((a : α) × β a) :=
  match getValueCast? k l with
  | none => l
  | some v => replaceEntry k (f v) l

theorem isEmpty_modifyKey [BEq α] [LawfulBEq α] (k : α) (f : β k → β k) (l : List ((a : α) × β a)) :
    (modifyKey k f l).isEmpty = l.isEmpty := by
  match l with
  | [] => simp [modifyKey]
  | a :: as =>
    simp only [modifyKey, replaceEntry, cond_eq_if]
    repeat' split <;> simp

theorem length_modifyKey [BEq α] [LawfulBEq α] (k : α) (f : β k → β k) (l : List ((a : α) × β a)) :
    (modifyKey k f l).length = l.length := by
  induction l
  · rfl
  · next ih =>
    simp only [modifyKey]
    split <;> next h => simp only [length_replaceEntry, List.length_cons]

theorem containsKey_modifyKey [BEq α] [LawfulBEq α] (k k' : α) (f : β k → β k)
    (l : List ((a : α) × β a)) : containsKey k' (modifyKey k f l) = containsKey k' l := by
  induction l
  · simp only [modifyKey, getValueCast?_nil, eraseKey_nil, containsKey_nil, Bool.false_eq_true]
  · simp only [modifyKey, Bool.coe_iff_coe]
    split
    · rfl
    · rw [containsKey_replaceEntry]

theorem modifyKey_eq_alterKey [BEq α] [LawfulBEq α] (k : α) (f : β k → β k)
    (l : List ((a : α) × β a)) : modifyKey k f l = alterKey k (·.map f) l := by
  rw [modifyKey, alterKey, Option.map.eq_def]
  split <;> next h =>
    simp [h, insertEntry, containsKey_eq_isSome_getValueCast?, eraseKey_of_containsKey_eq_false]

theorem getValueCast?_modifyKey [BEq α] [LawfulBEq α] {k k' : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l):
    getValueCast? k' (modifyKey k f l) =
      if h : k == k' then
        (cast (congrArg (Option ∘ β) (eq_of_beq h)) ((getValueCast? k l).map f))
      else
        getValueCast? k' l := by
  simp [modifyKey_eq_alterKey, getValueCast?_alterKey, hl]

@[simp]
theorem getValueCast?_modifyKey_self [BEq α] [LawfulBEq α] {k : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getValueCast? k (modifyKey k f l) = (getValueCast? k l).map f := by
  simp [getValueCast?_modifyKey, hl]

theorem getValueCast_modifyKey [BEq α] [LawfulBEq α] {k k' : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) (h : containsKey k' (modifyKey k f l)) :
    getValueCast k' (modifyKey k f l) h =
      if heq : k == k' then
        haveI h' : containsKey k l := by rwa [containsKey_modifyKey, ← eq_of_beq heq] at h
        cast (congrArg β (eq_of_beq heq)) <| f (getValueCast k l h')
      else
        haveI h' : containsKey k' l := by rwa [containsKey_modifyKey] at h
        getValueCast k' l h' := by
  simp only [modifyKey_eq_alterKey, getValueCast_alterKey, hl]
  split
  · next heq =>
    cases eq_of_beq heq
    haveI h' : containsKey k l := by rwa [containsKey_modifyKey, ← eq_of_beq heq] at h
    simp [getValueCast?_eq_some_getValueCast, h']
  · rfl

@[simp]
theorem getValueCast_modifyKey_self [BEq α] [LawfulBEq α] {k : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) {h : containsKey k (modifyKey k f l)} :
    haveI h' : containsKey k l := by rwa [containsKey_modifyKey] at h
    getValueCast k (modifyKey k f l) h = f (getValueCast k l h') := by
  simp [getValueCast_modifyKey, hl]

theorem getValueCast!_modifyKey [BEq α] [LawfulBEq α] {k k' : α} [hi : Inhabited (β k')]
    {f : β k → β k} (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getValueCast! k' (modifyKey k f l) =
      if heq : k == k' then
        getValueCast? k l |>.map f |>.map (cast (congrArg β (eq_of_beq heq))) |>.get!
      else
        getValueCast! k' l := by
  simp only [modifyKey_eq_alterKey, getValueCast!_alterKey, hl]

@[simp]
theorem getValueCast!_modifyKey_self [BEq α] [LawfulBEq α] {k : α} [Inhabited (β k)]
    {f : β k → β k} (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getValueCast! k (modifyKey k f l) = ((getValueCast? k l).map f).get! := by
  simp [getValueCast!_modifyKey, hl, List.cast_eq_id, List.function_id_comp]

theorem getValueCastD_modifyKey [BEq α] [LawfulBEq α] {k k' : α} {fallback : β k'} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getValueCastD k' (modifyKey k f l) fallback =
      if heq : k == k' then
        getValueCast? k l |>.map f |>.map (cast (congrArg β <| eq_of_beq heq)) |>.getD fallback
      else
        getValueCastD k' l fallback := by
  simp [modifyKey_eq_alterKey, getValueCastD_alterKey, hl]

@[simp]
theorem getValueCastD_modifyKey_self [BEq α] [LawfulBEq α] {k : α} {fallback : β k} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getValueCastD k (modifyKey k f l) fallback = ((getValueCast? k l).map f).getD fallback := by
  simp [getValueCastD_modifyKey, hl, List.cast_eq_id, List.function_id_comp]

theorem getKey?_modifyKey [BEq α] [LawfulBEq α] {k k' : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKey? k' (modifyKey k f l) =
      if k == k' then
        if containsKey k l then some k else none
      else
        getKey? k' l := by
  simp [modifyKey_eq_alterKey, getKey?_alterKey, containsKey_eq_isSome_getValueCast?, hl]

theorem getKey?_modifyKey_self [BEq α] [LawfulBEq α] {k : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKey? k (modifyKey k f l) = if containsKey k l then some k else none := by
  simp [getKey?_modifyKey, hl]

theorem getKey!_modifyKey [BEq α] [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKey! k' (modifyKey k f l) =
      if k == k' then
        if containsKey k l then k else default
      else
        getKey! k' l := by
  simp [modifyKey_eq_alterKey, getKey!_alterKey, containsKey_eq_isSome_getValueCast?, hl]

theorem getKey!_modifyKey_self [BEq α] [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKey! k (modifyKey k f l) = if containsKey k l then k else default := by
  simp [getKey!_modifyKey, hl]

theorem getKey_modifyKey [BEq α] [LawfulBEq α] [Inhabited α] {k k' : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) (h : containsKey k' (modifyKey k f l)) :
    getKey k' (modifyKey k f l) h =
      if k == k' then
        k
      else
        haveI h' : containsKey k' l := by rwa [containsKey_modifyKey] at h
        getKey k' l h' := by
  simp [modifyKey_eq_alterKey, getKey_alterKey, hl, ← dite_eq_ite]

@[simp]
theorem getKey_modifyKey_self [BEq α] [LawfulBEq α] [Inhabited α] {k : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) (h : containsKey k (modifyKey k f l)) :
    getKey k (modifyKey k f l) h = k := by
  simp [getKey_modifyKey, hl]

theorem getKeyD_modifyKey [BEq α] [LawfulBEq α] {k k' fallback : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKeyD k' (modifyKey k f l) fallback =
      if k == k' then
        if containsKey k l then k else fallback
      else
        getKeyD k' l fallback := by
  simp [modifyKey_eq_alterKey, getKeyD_alterKey, containsKey_eq_isSome_getValueCast?, hl]

theorem getKeyD_modifyKey_self [BEq α] [LawfulBEq α] [Inhabited α] {k fallback : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKeyD k (modifyKey k f l) fallback = if containsKey k l then k else fallback := by
  simp [getKeyD_modifyKey, hl]

namespace Const

variable {β : Type v} [BEq α]

/-- Internal implementation detail of the hash map -/
def modifyKey (k : α) (f : β → β)
    (l : List ((_ : α) × β)) : List ((_ : α) × β) :=
  match getValue? k l with
  | none => l
  | some v => replaceEntry k (f v) l

theorem isEmpty_modifyKey (k : α) (f : β → β) (l : List ((_ : α) × β)) :
    (modifyKey k f l).isEmpty = l.isEmpty := by
  match l with
  | [] => simp [modifyKey]
  | a :: as =>
    simp only [modifyKey, replaceEntry, cond_eq_if]
    repeat' split <;> simp

theorem modifyKey_eq_alterKey (k : α) (f : β → β) (l : List ((_ : α) × β)) :
    modifyKey k f l = alterKey k (·.map f) l := by
  rw [modifyKey, alterKey, Option.map.eq_def]
  split <;> next h =>
    simp [h, insertEntry, containsKey_eq_isSome_getValue?, eraseKey_of_containsKey_eq_false]

theorem length_modifyKey (k : α) (f : β → β) (l : List ((_ : α) × β)) :
    (modifyKey k f l).length = l.length := by
  induction l
  · rfl
  · next ih =>
    simp only [modifyKey]
    split <;> next h => simp only [length_replaceEntry, List.length_cons]

theorem containsKey_modifyKey [EquivBEq α] (k k': α) (f : β → β) (l : List ((_ : α) × β)) :
    containsKey k' (modifyKey k f l) = containsKey k' l := by
  induction l
  · simp only [modifyKey, getValue?_nil, eraseKey_nil, containsKey_nil, Bool.false_eq_true]
  · simp only [modifyKey, Bool.coe_iff_coe]
    split
    · rfl
    · rw [containsKey_replaceEntry]

theorem getValue?_modifyKey [EquivBEq α] {k k' : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) :
    getValue? k' (modifyKey k f l)  =
      if k == k' then
        (getValue? k l).map f
      else
        getValue? k' l := by
  simp [modifyKey_eq_alterKey, getValue?_alterKey, hl]

@[simp]
theorem getValue?_modifyKey_self [EquivBEq α] {k : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) : getValue? k (modifyKey k f l) = (getValue? k l).map f := by
  simp [getValue?_modifyKey, hl]

theorem getValue_modifyKey [EquivBEq α] {k k' : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) (h : containsKey k' (modifyKey k f l)) :
    getValue k' (modifyKey k f l) h =
      if heq : k == k' then
        haveI h' : containsKey k l := by rwa [containsKey_modifyKey, ← containsKey_congr heq] at h
         f (getValue k l h')
      else
        haveI h' : containsKey k' l := by rwa [containsKey_modifyKey] at h
        getValue k' l h' := by
  simp only [modifyKey_eq_alterKey, getValue_alterKey, hl]
  split
  · next heq =>
    haveI h' : containsKey k l := by rwa [containsKey_modifyKey, ← containsKey_congr heq] at h
    simp [getValue?_eq_some_getValue, h']
  · rfl

@[simp]
theorem getValue_modifyKey_self [EquivBEq α] {k : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) {h : containsKey k (modifyKey k f l)} :
    haveI h' : containsKey k l := by rwa [containsKey_modifyKey] at h
    getValue k (modifyKey k f l) h = f (getValue k l h') := by
  simp [getValue_modifyKey, hl]

theorem getValue!_modifyKey [EquivBEq α] {k k' : α} [hi : Inhabited β] {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) : getValue! k' (modifyKey k f l) =
      if k == k' then
        getValue? k l |>.map f |>.get!
      else
        getValue! k' l := by
  simp [modifyKey_eq_alterKey, getValue!_alterKey, hl]

@[simp]
theorem getValue!_modifyKey_self [EquivBEq α] {k : α} [Inhabited (β)] {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getValue! k (modifyKey k f l) = ((getValue? k l).map f).get! := by
  simp [getValue!_modifyKey, hl]

theorem getValueD_modifyKey [EquivBEq α] {k k' : α} {fallback : β} {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getValueD k' (modifyKey k f l) fallback =
      if k == k' then
        getValue? k l |>.map f |>.getD fallback
      else
        getValueD k' l fallback := by
  simp [modifyKey_eq_alterKey, getValueD_alterKey, hl]

@[simp]
theorem getValueD_modifyKey_self [EquivBEq α] {k : α} {fallback : β} {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getValueD k (modifyKey k f l) fallback = ((getValue? k l).map f).getD fallback := by
  simp [getValueD_modifyKey, hl]

theorem getKey?_modifyKey [EquivBEq α] {k k' : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) :
    getKey? k' (modifyKey k f l) =
      if k == k' then
        if containsKey k l then some k else none
      else
        getKey? k' l := by
  simp [modifyKey_eq_alterKey, getKey?_alterKey, containsKey_eq_isSome_getValue?, hl]

theorem getKey?_modifyKey_self [EquivBEq α] {k : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) :
    getKey? k (modifyKey k f l) = if containsKey k l then some k else none := by
  simp [getKey?_modifyKey, hl]

theorem getKey!_modifyKey [EquivBEq α] [Inhabited α] {k k' : α} {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) : getKey! k' (modifyKey k f l) =
      if k == k' then
        if containsKey k l then k else default
      else
        getKey! k' l := by
  simp [modifyKey_eq_alterKey, getKey!_alterKey, containsKey_eq_isSome_getValue?, hl]

theorem getKey!_modifyKey_self [EquivBEq α] [Inhabited α] {k : α} {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getKey! k (modifyKey k f l) = if containsKey k l then k else default := by
  simp [getKey!_modifyKey, hl]

theorem getKey_modifyKey [EquivBEq α] [Inhabited α] {k k' : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) (h : containsKey k' (modifyKey k f l)) :
    getKey k' (modifyKey k f l) h =
      if k == k' then
        k
      else
        haveI h' : containsKey k' l := by rwa [containsKey_modifyKey] at h
        getKey k' l h' := by
  simp [modifyKey_eq_alterKey, getKey_alterKey, hl]
  rfl

@[simp]
theorem getKey_modifyKey_self [EquivBEq α] [Inhabited α] {k : α} {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) (h : containsKey k (modifyKey k f l)) :
    getKey k (modifyKey k f l) h = k := by
  simp [getKey_modifyKey, hl]

theorem getKeyD_modifyKey [EquivBEq α] {k k' fallback : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) :
    getKeyD k' (modifyKey k f l) fallback =
      if k == k' then
        if containsKey k l then k else fallback
      else
        getKeyD k' l fallback := by
  simp [modifyKey_eq_alterKey, getKeyD_alterKey, containsKey_eq_isSome_getValue?, hl]

theorem getKeyD_modifyKey_self [EquivBEq α] [Inhabited α] {k fallback : α} {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getKeyD k (modifyKey k f l) fallback = if containsKey k l then k else fallback := by
  simp [getKeyD_modifyKey, hl]

end Const

theorem constModifyKey_eq_modifyKey {β : Type v} [BEq α] [LawfulBEq α] {k : α} {f : β → β}
    {l : List ((_ : α) × β)} :
    Const.modifyKey k f l = modifyKey k f l := by
  rw [modifyKey, Const.modifyKey, getValue?_eq_getValueCast?]
  cases getValueCast? k l <;> rfl

end Modify

end Std.Internal.List
