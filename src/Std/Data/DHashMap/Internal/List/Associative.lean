/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.BEq
import Init.Data.Nat.Simproc
import Init.Data.List.Perm
import Std.Data.DHashMap.Internal.List.Defs

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

namespace Std.DHashMap.Internal.List

attribute [-simp] List.isEmpty_eq_false

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
  · simp [replaceEntry_cons, cond_eq_if]
    split <;> simp

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
      simp [getEntry?_cons_of_false h, getEntry?_cons_of_false hk]

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

/-- Internal implementation detail of the hash map -/
def insertEntry [BEq α]  (k : α) (v : β k) (l : List ((a : α) × β a)) : List ((a : α) × β a) :=
  bif containsKey k l then replaceEntry k v l else ⟨k, v⟩ :: l

@[simp]
theorem insertEntry_nil [BEq α] {k : α} {v : β k} :
    insertEntry k v ([] : List ((a : α) × β a)) = [⟨k, v⟩] := by
  simp [insertEntry]

theorem insertEntry_of_containsKey [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l) : insertEntry k v l = replaceEntry k v l := by
  simp [insertEntry, h]

theorem insertEntry_of_containsKey_eq_false [BEq α] {l : List ((a : α) × β a)} {k : α} {v : β k}
    (h : containsKey k l = false) : insertEntry k v l = ⟨k, v⟩ :: l := by
  simp [insertEntry, h]

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

end List
