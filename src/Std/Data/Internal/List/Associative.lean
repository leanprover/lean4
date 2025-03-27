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
import Init.Data.List.MinMax
import Init.Data.List.Monadic
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

theorem getEntry?_eq_find [BEq α] {k : α} {l : List ((a : α) × β a)} :
    getEntry? k l = l.find? (·.1 == k) := by
  induction l using assoc_induction with
  | nil => simp
  | cons k' v t ih => cases h : k' == k <;> simp_all [List.find?_cons, getEntry?_cons]

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

theorem beq_of_getEntry?_eq_some [BEq α] {l : List ((a : α) × β a)} {a : α} {p : (a : α) × β a}
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

theorem keys_eq_map {l : List ((a : α) × β a)} :
    keys l = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons => simp [keys, *]

theorem getEntry?_eq_some_iff [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {e} {k}
    (hd : DistinctKeys l) :
    getEntry? k l = some e ↔ k == e.1 ∧ e ∈ l := by
  replace hd := hd.distinct
  induction l using assoc_induction with
  | nil => simp
  | cons lk lv tail ih =>
    simp only [getEntry?_cons, cond_eq_if, List.mem_cons]
    split
    · rename_i hlkk
      simp only [Option.some.injEq]
      replace hd := pairwise_cons.mp hd
      refine ⟨fun heq => ⟨(congrArg (Sigma.fst) heq.symm) ▸ BEq.symm hlkk, Or.inl heq.symm⟩, ?_⟩
      rintro ⟨hbeq, ⟨rfl|h⟩⟩
      · rfl
      · exfalso
        rename_i h
        have := hd.1 _ <| keys_eq_map ▸ List.mem_map_of_mem h
        simp_all [BEq.trans hlkk hbeq]
    · rename_i h
      replace h := h.imp BEq.symm
      simp only [ih hd.tail, Sigma.ext_iff, and_congr_right_iff, iff_or_self, and_imp]
      intros; simp_all

theorem mem_iff_getEntry?_eq_some [BEq α] [EquivBEq α] {l : List ((a : α) × β a)}
    {p : (a : α) × β a} (h : DistinctKeys l) : p ∈ l ↔ getEntry? p.1 l = some p := by
  simp [getEntry?_eq_some_iff h]

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

private theorem Option.dmap_eq_some {o : Option α} {f : (a : α) → (o = some a) → β} (b : β) :
    (Option.dmap o f) = some b ↔ ∃ (a : α) (h : o = some a), f a h = b := by
  cases o with
  | none => simp
  | some a =>
    simp only [dmap_some, Option.some.injEq]
    exact ⟨by rintro rfl; exact ⟨a, rfl, rfl⟩, by rintro ⟨_, rfl, h⟩; exact h⟩

end

theorem getValueCast?_eq_getEntry? [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α} :
    getValueCast? a l = Option.dmap (getEntry? a l)
      (fun p h => cast (congrArg β (eq_of_beq (beq_of_getEntry?_eq_some h))) p.2) := by
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

theorem fst_mem_keys_of_mem [BEq α] [EquivBEq α] {a : (a : α) × β a} {l : List ((a : α) × β a)}
    (hm : a ∈ l) : a.1 ∈ keys l :=
  keys_eq_map ▸ List.mem_map_of_mem hm

theorem getKey?_eq_some_iff [BEq α] [EquivBEq α] {l : List ((a : α) × β a)} {k k'}
    (hd : DistinctKeys l) :
    getKey? k l = some k' ↔ k == k' ∧ k' ∈ keys l := by
  simp [getKey?_eq_getEntry?, getEntry?_eq_some_iff hd]
  apply Iff.intro
  · rintro ⟨a, ⟨hbeq, hm⟩, rfl⟩
    exact ⟨hbeq, fst_mem_keys_of_mem hm⟩
  · rintro ⟨hbeq, hm⟩
    simp only [keys_eq_map, List.mem_map] at hm
    obtain ⟨a, hm, rfl⟩ := hm
    refine ⟨a, ⟨hbeq, hm⟩, rfl⟩

theorem getKey?_beq [BEq α] {l : List ((a : α) × β a)} {a : α} :
    (getKey? a l).all (· == a) := by
  induction l using assoc_induction with
  | nil => rfl
  | cons k v l ih =>
    rw [getKey?_cons, cond_eq_if]
    split <;> assumption

theorem getKey?_congr [BEq α] [EquivBEq α] {l : List ((a : α) × β a)}
    {k k' : α} (h : k == k') : getKey? k l = getKey? k' l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [getKey?_cons, getKey?_cons, BEq.congr_right h, ih]

theorem containsKey_eq_isSome_getKey? [BEq α] {l : List ((a : α) × β a)} {a : α} :
    containsKey a l = (getKey? a l).isSome := by
  simp [containsKey_eq_isSome_getEntry?, getKey?_eq_getEntry?]

theorem getEntry?_eq_some_iff_getKey?_eq_some_getValue?_eq_some [BEq α] {β : Type v}
    {l : List ((_ : α) × β)} {k k' : α} {v : β} :
    getEntry? k l = some ⟨k', v⟩ ↔ getKey? k l = some k' ∧ getValue? k l = some v := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [getEntry?, getKey?, getValue?, cond_eq_if]
    split
    · rename_i h
      simp [Sigma.ext_iff]
    · rw [ih]

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

theorem getKey_beq [BEq α] {l : List ((a : α) × β a)} {a : α} (h : containsKey a l) :
    getKey a l h == a := by
  simpa only [getKey?_eq_some_getKey h] using getKey?_beq (l := l) (a := a)

@[simp]
theorem getKey_eq [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α} (h : containsKey a l) :
    getKey a l h = a := by
  simpa only [beq_iff_eq] using getKey_beq h

theorem getKey?_eq_some [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l) : getKey? a l = some a := by
  simp only [getKey?_eq_some_getKey h, getKey_eq]

theorem getKey_congr [BEq α] [EquivBEq α] {l : List ((a : α) × β a)}
    {k k' : α} (h : k == k') {h'} {h''} : getKey k l h' = getKey k' l h'' := by
  simpa only [getKey?_eq_some_getKey, h', h'', Option.some.injEq] using getKey?_congr (l := l) h

theorem getKey_eq_getEntry_fst [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)} {a : α}
    {h : containsKey a l} : getKey a l h = (getEntry a l h).fst := by
  simp [getKey, getKey?_eq_getEntry?, Option.get_map, getEntry]

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

theorem getKeyD_congr [BEq α] [EquivBEq α] {l : List ((a : α) × β a)}
    {k k' fallback : α} (h : k == k') : getKeyD k l fallback = getKeyD k' l fallback := by
  simp only [getKeyD_eq_getKey?, getKey?_congr h]

theorem getKeyD_eq_of_containsKey [BEq α] [LawfulBEq α]
    {l : List ((a : α) × β a)} {k fallback : α} (h : containsKey k l) :
    getKeyD k l fallback = k := by
  simp only [← getKey_eq_getKeyD h, getKey_eq]

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

theorem getKey!_congr [BEq α] [EquivBEq α] [Inhabited α] {l : List ((a : α) × β a)}
    {k k' : α} (h : k == k') : getKey! k l = getKey! k' l := by
  simp only [getKey!_eq_getKey?, getKey?_congr h]

theorem getKey!_eq_of_containsKey [BEq α] [LawfulBEq α] [Inhabited α]
    {l : List ((a : α) × β a)} {k : α} (h : containsKey k l) :
    getKey! k l = k := by
  simp only [← getKey_eq_getKey! h, getKey_eq]

theorem getKey?_eq_some_getKey! [BEq α] [Inhabited α] {l : List ((a : α) × β a)} {a : α}
    (h : containsKey a l = true) :
    getKey? a l = some (getKey! a l) := by
  rw [getKey?_eq_some_getKey h, getKey_eq_getKey!]

theorem getKey!_eq_getKeyD_default [BEq α] [EquivBEq α] [Inhabited α] {l : List ((a : α) × β a)}
    {a : α} : getKey! a l = getKeyD a l default := rfl

theorem getEntry?_eq_getValueCast? [BEq α] [LawfulBEq α] {l : List ((a : α) × β a)}
    {a : α} : getEntry? a l = (getValueCast? a l).map (fun v => ⟨a, v⟩) := by
  induction l using assoc_induction with
  | nil => rfl
  | cons k v l ih =>
    simp only [getEntry?_cons, getValueCast?_cons, cond_eq_if]
    split
    · rename_i h
      simp only [beq_iff_eq] at h
      subst h
      rfl
    · exact ih

theorem getEntry_eq_getKey_getValue [BEq α] {β : Type v} {l : List ((_ : α) × β)}
    {a : α} (h : containsKey a l) : getEntry a l h = ⟨getKey a l h, getValue a l h⟩ := by
  induction l using assoc_induction with
  | nil => contradiction
  | cons k v l ih =>
    match h' : k == a with
    | true =>
      simp only [getEntry_cons_of_beq, getKey_cons, getValue_cons_of_beq, h', reduceDIte]
    | false =>
      simp only [getEntry_cons_of_false, getKey_cons, getValue_cons_of_false, h',
        Bool.false_eq_true, reduceDIte]
      apply ih

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
theorem containsKey_replaceEntry [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)} {a k : α}
    {v : β k} : containsKey a (replaceEntry k v l) = containsKey a l := by
  by_cases h : (getEntry? k l).isSome ∧ k == a
  · simp only [containsKey_eq_isSome_getEntry?, getEntry?_replaceEntry, h, and_self, ↓reduceIte,
      Option.isSome_some, Bool.true_eq]
    rw [← getEntry?_congr h.2, h.1]
  · simp [containsKey_eq_isSome_getEntry?, getEntry?_replaceEntry, h]

theorem getEntry_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {a k : α} {v : β k} (hl) (h : k == a) :
    getEntry a (replaceEntry k v l) hl = ⟨k, v⟩ := by
  rw [containsKey_replaceEntry] at hl
  simp only [getEntry, getEntry?_replaceEntry]
  simp_all [containsKey_congr h]

theorem mem_getEntry [BEq α] {l : List ((a : α) × β a)} {k : α} (hl : containsKey k l) :
    getEntry k l hl ∈ l := by
  induction l using assoc_induction
  · simp at hl
  · next k' v' l ih =>
    simp [getEntry, getEntry?_cons, cond_eq_if]
    split
    · simp
    · simp only [containsKey_cons, Bool.or_eq_true] at hl
      simp_all [containsKey_cons_eq_true, getEntry]

theorem mem_replaceEntry_of_true [BEq α] [PartialEquivBEq α] {l : List ((a : α) × β a)}
    {k : α} {v : β k} (hl : containsKey k l = true) :
    ⟨k, v⟩ ∈ replaceEntry k v l := by
  induction l using assoc_induction
  · simp at hl
  · next k' v' l ih =>
    cases h : k' == k <;> simp_all [replaceEntry_cons, h]

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
    simp only [Decidable.not_and_iff_not_or_not] at h
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
    simp only [Decidable.not_and_iff_not_or_not] at h
    rcases h with h|h
    · rw [getEntry?_replaceEntry_of_containsKey_eq_false (Bool.eq_false_iff.2 h), getKey?_eq_getEntry?]
    · rw [getEntry?_replaceEntry_of_false (Bool.eq_false_iff.2 h), getKey?_eq_getEntry?]

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
    {l : List ((a : α) × β a)} (h : DistinctKeys l) :
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
  apply distinctKeys_of_sublist_keys (by simpa using erase_sublist)

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
  exact filter_sublist

theorem DistinctKeys.map [BEq α] {l : List ((a : α) × β a)} {f : (a : α) → β a → γ a}
    (h : DistinctKeys l) : DistinctKeys (l.map fun p => ⟨p.1, f p.1 p.2⟩) :=
  h.of_keys_eq keys_map.symm

theorem DistinctKeys.filter [BEq α] {l : List ((a : α) × β a)} {f : (a : α) → β a → Bool}
    (h : DistinctKeys l) : DistinctKeys (l.filter fun p => f p.1 p.2) :=
  distinctKeys_of_sublist filter_sublist h

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

theorem isEmpty_eq_isEmpty_eraseKey_and_not_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (k : α) :
    l.isEmpty = ((eraseKey k l).isEmpty && !(containsKey k l)) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.not_eq_true']
  simp only [isEmpty_iff_forall_containsKey, containsKey_eraseKey hd, Bool.and_eq_false_iff,
    Bool.not_eq_false']
  constructor
  · exact fun h => ⟨fun a => Or.inr (h a), h k⟩
  · rintro ⟨h₁, h₂⟩ a
    specialize h₁ a
    cases hbeq : k == a
    · simp_all
    · simp only [hbeq, true_or] at h₁
      exact containsKey_congr hbeq ▸ h₂

theorem isEmpty_eq_false_of_isEmpty_eraseKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k : α}
    (he : (eraseKey k l).isEmpty = false) :
    l.isEmpty = false := by
  simp_all [isEmpty_eq_isEmpty_eraseKey_and_not_containsKey hd k]

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

theorem getValueCast?_ext [BEq α] [LawfulBEq α] {l l' : List ((a : α) × β a)} (hl : DistinctKeys l)
    (hl' : DistinctKeys l') (h : ∀ a, getValueCast? a l = getValueCast? a l') : Perm l l' := by
  apply getEntry?_ext hl hl'
  intro a
  simp only [getEntry?_eq_getValueCast?, h]

theorem getKey?_getValue?_ext [BEq α] [EquivBEq α] {β : Type v}
    {l l' : List ((_ : α) × β)} (hl : DistinctKeys l) (hl' : DistinctKeys l')
    (hk : ∀ a, getKey? a l = getKey? a l') (hv : ∀ a, getValue? a l = getValue? a l') :
    Perm l l' := by
  apply getEntry?_ext hl hl'
  intro a
  specialize hk a; specialize hv a
  by_cases h' : containsKey a l'
  · simp only [getKey?_eq_some_getKey h'] at hk
    have h'' := containsKey_eq_isSome_getKey?.trans (hk ▸ rfl : (getKey? a l).isSome = true)
    simp only [getKey?_eq_some_getKey, getValue?_eq_some_getValue,
      getEntry?_eq_some_getEntry, h', h'', Option.some.injEq,
      getEntry_eq_getKey_getValue, Sigma.mk.injEq] at hk hv ⊢
    exact ⟨hk, hv ▸ .rfl⟩
  · simp only [getKey?_eq_none, h'] at hk
    have h'' := containsKey_eq_isSome_getKey?.trans (hk ▸ rfl : (getKey? a l).isSome = false)
    simp only [getEntry?_eq_none.mpr, h', h'']

theorem getKey?_ext [BEq α] [EquivBEq α]
    {l l' : List ((_ : α) × Unit)} (hl : DistinctKeys l) (hl' : DistinctKeys l')
    (h : ∀ a, getKey? a l = getKey? a l') : Perm l l' := by
  apply getKey?_getValue?_ext hl hl' h
  intro a
  specialize h a
  by_cases h' : containsKey a l'
  · rw [getKey?_eq_some_getKey h'] at h
    have h'' := containsKey_eq_isSome_getKey?.trans (h ▸ Option.isSome_some)
    simp only [getValue?_eq_some_getValue, h', h'']
  · rw [getKey?_eq_none ((Bool.not_eq_true _).mp h')] at h
    have h'' := containsKey_eq_isSome_getKey?.trans (h ▸ Option.isSome_none)
    simp only [getValue?_eq_none.mpr, h', h'']

theorem containsKey_ext [BEq α] [LawfulBEq α]
    {l l' : List ((_ : α) × Unit)} (hl : DistinctKeys l) (hl' : DistinctKeys l')
    (h : ∀ a, containsKey a l = containsKey a l') : Perm l l' := by
  apply getKey?_ext hl hl'
  intro a
  by_cases h' : containsKey a l'
  · simp only [getKey?_eq_some, h', (h a).trans h']
  · simp only [getKey?_eq_none, h', (h a).trans ((Bool.not_eq_true _).mp h')]

theorem replaceEntry_of_perm [BEq α] [EquivBEq α] {l l' : List ((a : α) × β a)} {k : α} {v : β k}
    (hl : DistinctKeys l) (h : Perm l l') : Perm (replaceEntry k v l) (replaceEntry k v l') := by
  apply getEntry?_ext hl.replaceEntry (hl.perm h.symm).replaceEntry
  simp [getEntry?_replaceEntry, getEntry?_of_perm hl h, containsKey_of_perm h]

theorem insertEntry_of_perm [BEq α] [EquivBEq α] {l l' : List ((a : α) × β a)} {k : α} {v : β k}
    (hl : DistinctKeys l) (h : Perm l l') : Perm (insertEntry k v l) (insertEntry k v l') := by
  apply getEntry?_ext hl.insertEntry (hl.perm h.symm).insertEntry
  simp [getEntry?_insertEntry, getEntry?_of_perm hl h]

theorem insertEntryIfNew_of_perm [BEq α] [EquivBEq α] {l l' : List ((a : α) × β a)}
    {k : α} {v : β k} (hl : DistinctKeys l) (h : Perm l l') :
    Perm (insertEntryIfNew k v l) (insertEntryIfNew k v l') := by
  apply getEntry?_ext hl.insertEntryIfNew (hl.perm h.symm).insertEntryIfNew
  simp [getEntry?_insertEntryIfNew, getEntry?_of_perm hl h, containsKey_of_perm h]

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

theorem mem_iff_getValueCast?_eq_some [BEq α] [LawfulBEq α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (h : DistinctKeys l) :
    ⟨k, v⟩ ∈ l ↔ getValueCast? k l = some v := by
  rw [mem_iff_getEntry?_eq_some h, getValueCast?_eq_getEntry?, Option.dmap_eq_some]
  refine ⟨?_, ?_⟩
  · intro hkv
    refine ⟨⟨k, v⟩, hkv, by simp⟩
  · rintro ⟨⟨k', v'⟩, hkv, hkv'⟩
    obtain rfl := beq_iff_eq.1 (beq_of_getEntry?_eq_some hkv)
    simpa [hkv]

theorem find?_eq_some_iff_getValueCast?_eq_some [BEq α] [LawfulBEq α]
    {l : List ((a : α) × β a)} {k : α} {v : β k} (h : DistinctKeys l) :
    List.find? (fun x => x.fst == k) l = some ⟨k, v⟩ ↔ getValueCast? k l = some v := by
  rw [← getEntry?_eq_find, ← mem_iff_getEntry?_eq_some (p := ⟨k, v⟩) h,
    ← mem_iff_getValueCast?_eq_some h]

theorem find?_eq_none_iff_containsKey_eq_false [BEq α] [PartialEquivBEq α]
    {l : List ((a : α) × β a)} {k : α} :
    List.find? (fun x => x.fst == k) l = none ↔ containsKey k l = false := by
  simp [List.find?_eq_none, containsKey_eq_false_iff, BEq.comm]

theorem pairwise_fst_eq_false [BEq α] {l : List ((a : α) × β a)} (h : DistinctKeys l) :
    List.Pairwise (fun a b => (a.fst == b.fst) = false) l := by
  rw [DistinctKeys.def] at h
  assumption

theorem map_fst_map_toProd_eq_keys {β : Type v} {l : List ((_ : α) × β)} :
    List.map Prod.fst (List.map (fun x => (x.fst, x.snd)) l) = List.keys l := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, keys]
    congr

theorem find?_map_eq_none_iff_containsKey_eq_false [BEq α] [PartialEquivBEq α]
    {β : Type v} {l : List ((_ : α) × β)} {k : α} :
    List.find? (fun x => x.fst == k) (l.map (fun x => (x.fst, x.snd))) = none ↔
      containsKey k l = false := by
  simp [List.find?_eq_none, containsKey_eq_false_iff, BEq.comm]

theorem mem_map_toProd_iff_mem {β : Type v} {k : α} {v : β} {l : List ((_ : α) × β)} :
    ⟨k, v⟩ ∈ l ↔ (k, v) ∈ l.map (fun x => (x.fst, x.snd)) := by
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · intro h
    exists ⟨k, v⟩
  · intro h
    rcases h with ⟨a, a_l, a_k, a_v⟩
    simp [← a_k, ←a_v, a_l]

theorem mem_iff_getValue?_eq_some [BEq α] [LawfulBEq α] {β : Type v} {k : α} {v : β}
    {l : List ((_ : α) × β)} (h : DistinctKeys l) :
    ⟨k, v⟩ ∈ l ↔ getValue? k l = some v := by
  simp only [mem_iff_getEntry?_eq_some h, getValue?_eq_getEntry?, Option.map_eq_some']
  constructor
  · intro h
    exists ⟨k, v⟩
  · intro h
    rcases h with ⟨a, h, a_v⟩
    simp [h, ← a_v, Sigma.ext_iff]
    apply LawfulBEq.eq_of_beq (beq_of_getEntry?_eq_some h)

theorem mem_map_toProd_iff_getValue?_eq_some [BEq α] [LawfulBEq α] {β : Type v} {k : α} {v : β}
    {l : List ((_ : α) × β)} (h : DistinctKeys l) :
    ⟨k, v⟩ ∈ l.map (fun x => (x.fst, x.snd)) ↔ getValue? k l = some v := by
  rw [← mem_map_toProd_iff_mem]
  exact mem_iff_getValue?_eq_some h

theorem find?_map_toProd_eq_some_iff_getKey?_eq_some_and_getValue?_eq_some [BEq α] [EquivBEq α]
    {β : Type v} {k k': α} {v : β} {l : List ((_ : α) × β)} :
    (l.map (fun x => (x.fst, x.snd))).find? (fun a => a.1 == k) = some (k', v) ↔
      getKey? k l = some k' ∧ getValue? k l = some v := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons_eq_some, Prod.mk.injEq, Bool.not_eq_eq_eq_not,
      Bool.not_true, Option.map_eq_some', getKey?, cond_eq_if, getValue?]
    by_cases hdfst_k: hd.fst == k
    · simp only [hdfst_k, true_and, Bool.true_eq_false, false_and, or_false, ↓reduceIte,
      Option.some.injEq]
    · simp only [hdfst_k, Bool.false_eq_true, false_and, true_and, false_or, ↓reduceIte]
      rw [ih]

theorem mem_iff_getKey?_eq_some_and_getValue?_eq_some [BEq α] [EquivBEq α]
    {β : Type v} {k: α} {v : β} {l : List ((_ : α) × β)} (h : DistinctKeys l) :
    ⟨k, v⟩ ∈ l ↔ getKey? k l = some k ∧ getValue? k l = some v := by
  rw [mem_iff_getEntry?_eq_some h, getEntry?_eq_some_iff_getKey?_eq_some_getValue?_eq_some]

theorem getValue?_eq_some_iff_exists_beq_and_mem_toList {β : Type v} [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {k: α} {v : β} (h : DistinctKeys l) :
    getValue? k l = some v ↔ ∃ k', (k == k') = true ∧ (k', v) ∈ l.map (fun x => (x.fst, x.snd)) := by
  simp only [getValue?_eq_getEntry?, Option.map_eq_some', ← mem_map_toProd_iff_mem,
    mem_iff_getEntry?_eq_some h]
  constructor
  · intro h'
    rcases h' with ⟨a, h', a_v⟩
    exists a.1
    have k_afst : a.fst == k := beq_of_getEntry?_eq_some h'
    simp [k_afst, getEntry?_congr k_afst, ← a_v, h', BEq.symm]
  · intro h'
    rcases h' with ⟨k', k_k', h'⟩
    exists ⟨k', v⟩
    simp only [and_true, getEntry?_congr k_k', h']


theorem mem_map_toProd_iff_getKey?_eq_some_and_getValue?_eq_some [BEq α] [EquivBEq α]
    {β : Type v} {k: α} {v : β} {l : List ((_ : α) × β)} (h : DistinctKeys l) :
    (k, v) ∈ l.map (fun x => (x.fst, x.snd)) ↔ getKey? k l = some k ∧ getValue? k l = some v := by
  rw [← mem_map_toProd_iff_mem]
  exact mem_iff_getKey?_eq_some_and_getValue?_eq_some h

theorem pairwise_fst_eq_false_map_toProd [BEq α] {β : Type v}
    {l : List ((_ : α) × β)} (h : DistinctKeys l) :
    List.Pairwise (fun a b => (a.fst == b.fst) = false) (List.map (fun x => (x.fst, x.snd)) l) := by
  rw [DistinctKeys.def] at h
  simp [List.pairwise_map]
  assumption

theorem foldlM_eq_foldlM_toProd {β : Type v} {δ : Type w} {m' : Type w → Type w} [Monad m']
    [LawfulMonad m'] {l : List ((_ : α) × β)} {f : δ → (a : α) → β → m' δ} {init : δ} :
    l.foldlM (fun a b => f a b.fst b.snd) init =
      (l.map fun x => (x.1, x.2)).foldlM (fun a b => f a b.fst b.snd) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem foldl_eq_foldl_toProd {β : Type v} {δ : Type w}
    {l : List ((_ : α) × β)} {f : δ → (a : α) → β → δ} {init : δ} :
    l.foldl (fun a b => f a b.fst b.snd) init =
      (l.map fun x => (x.1, x.2)).foldl (fun a b => f a b.fst b.snd) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem foldrM_eq_foldrM_toProd {β : Type v} {δ : Type w} {m' : Type w → Type w} [Monad m']
    [LawfulMonad m'] {l : List ((_ : α) × β)} {f : (a : α) → β → δ → m' δ} {init : δ} :
    l.foldrM (fun a b => f a.1 a.2 b) init =
      (l.map fun x => (x.1, x.2)).foldrM (fun a b => f a.1 a.2 b) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem foldrM_eq_foldrM_toProd' {β : Type v} {δ : Type w} {m' : Type w → Type w} [Monad m']
    [LawfulMonad m'] {l : List ((_ : α) × β)} {f : δ → (a : α) → β → m' δ} {init : δ} :
    l.foldrM (fun a b => f b a.1 a.2) init =
      (l.map fun x => (x.1, x.2)).foldrM (fun a b => f b a.1 a.2) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem foldr_eq_foldr_toProd {β : Type v} {δ : Type w}
    {l : List ((_ : α) × β)} {f : (a : α) → β → δ → δ} {init : δ} :
    l.foldr (fun a b => f a.1 a.2 b) init =
      (l.map fun x => (x.1, x.2)).foldr (fun a b => f a.1 a.2 b) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem foldr_eq_foldr_toProd' {β : Type v} {δ : Type w}
    {l : List ((_ : α) × β)} {f : δ → (a : α) → β → δ} {init : δ} :
    l.foldr (fun a b => f b a.1 a.2) init =
      (l.map fun x => (x.1, x.2)).foldr (fun a b => f b a.1 a.2) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [ih]

theorem forM_eq_forM_toProd {β : Type v} {m' : Type w → Type w} [Monad m']
    [LawfulMonad m'] {l : List ((_ : α) × β)} {f : (a : α) → β → m' PUnit} :
    forM l (fun a => f a.1 a.2) = forM (l.map (fun x => (x.1, x.2))) fun a => f a.1 a.2 := by
  cases l with
  | nil => simp
  | cons hd tl => simp

theorem forIn_eq_forIn_toProd {β : Type v} {δ : Type w} {m' : Type w → Type w} [Monad m']
    [LawfulMonad m'] {l : List ((_ : α) × β)} {f : (a : α) → β → δ → m' (ForInStep δ)} {init : δ} :
    ForIn.forIn l init (fun a d => f a.1 a.2 d) =
      ForIn.forIn (l.map (fun x => (x.1, x.2))) init fun a d => f a.1 a.2 d := by
  cases l  with
  | nil => simp
  | cons hd tl => simp

theorem foldlM_eq_foldlM_keys {δ : Type w} {m' : Type w → Type w} [Monad m'] [LawfulMonad m']
    {l : List ((a : α) × β a)} {f : δ → α → m' δ} {init : δ} :
    l.foldlM (fun a b => f a b.1) init = (keys l).foldlM f init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldlM_cons, keys]
    congr
    simp [ih]

theorem foldl_eq_foldl_keys {δ : Type w}
    {l : List ((a : α) × β a)} {f : δ → α → δ} {init : δ} :
    l.foldl (fun a b => f a b.1) init = (keys l).foldl f init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [List.foldlM_cons, keys, ih]

theorem foldrM_eq_foldrM_keys {δ : Type w} {m' : Type w → Type w} [Monad m'] [LawfulMonad m']
    {l : List ((a : α) × β a)} {f : α → δ → m' δ} {init : δ} :
    l.foldrM (fun a b => f a.1 b) init = (keys l).foldrM f init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp [keys, ih]

theorem foldrM_eq_foldrM_keys' {δ : Type w} {m' : Type w → Type w} [Monad m'] [LawfulMonad m']
    {l : List ((a : α) × β a)} {f : δ → α → m' δ} {init : δ} :
    l.foldrM (fun a b => f b a.1) init = (keys l).foldrM (fun a b => f b a) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp [keys, ih]

theorem foldr_eq_foldr_keys {δ : Type w}
    {l : List ((a : α) × β a)} {f : α → δ → δ} {init : δ} :
    l.foldr (fun a b => f a.1 b) init = (keys l).foldr f init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [keys, ih]

theorem foldr_eq_foldr_keys' {δ : Type w}
    {l : List ((a : α) × β a)} {f : δ → α → δ} {init : δ} :
    l.foldr (fun a b => f b a.1) init = (keys l).foldr (fun a b => f b a) init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp [keys, ih]

theorem forM_eq_forM_keys {m' : Type w → Type w} [Monad m'] [LawfulMonad m']
    {l : List ((a : α) × β a)} {f : α → m' PUnit} :
    l.forM (fun a => f a.1) = (keys l).forM f := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.forM_eq_forM, List.forM_cons, keys]
    congr
    funext x
    apply ih

theorem forIn_eq_forIn_keys {δ : Type w} {m' : Type w → Type w} [Monad m'] [LawfulMonad m']
    {f : α → δ → m' (ForInStep δ)} {init : δ} {l : List ((a : α) × β a)} :
    ForIn.forIn l init (fun a d => f a.fst d) = ForIn.forIn (keys l) init f := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp [keys]
    congr
    funext x
    cases x <;> simp[ih]

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
    have := List.rel_of_pairwise_cons hl₂ List.mem_cons_self
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
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k') {v : β k}
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
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k') (v : β k)
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert)
    {h} :
    getValueCast k' (insertList l toInsert) h =
    cast (by congr; exact LawfulBEq.eq_of_beq k_beq) v := by
  rw [← Option.some_inj, ← getValueCast?_eq_some_getValueCast,
    getValueCast?_insertList_of_mem distinct_l k_beq distinct_toInsert mem]

theorem getValueCast!_insertList_of_contains_eq_false [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (not_contains : (toInsert.map Sigma.fst).contains k = false) :
    getValueCast! k (insertList l toInsert) = getValueCast! k l := by
  rw [getValueCast!_eq_getValueCast?, getValueCast!_eq_getValueCast?,
    getValueCast?_insertList_of_contains_eq_false not_contains]

theorem getValueCast!_insertList_of_mem [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k') (v : β k) [Inhabited (β k')]
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValueCast! k' (insertList l toInsert) =
    cast (by congr; exact LawfulBEq.eq_of_beq k_beq) v := by
  rw [getValueCast!_eq_getValueCast?,
    getValueCast?_insertList_of_mem distinct_l k_beq distinct_toInsert mem, Option.get!_some]

theorem getValueCastD_insertList_of_contains_eq_false [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α} {fallback : β k}
    (not_mem : (toInsert.map Sigma.fst).contains k = false) :
    getValueCastD k (insertList l toInsert) fallback = getValueCastD k l fallback := by
  rw [getValueCastD_eq_getValueCast?, getValueCastD_eq_getValueCast?,
    getValueCast?_insertList_of_contains_eq_false not_mem]

theorem getValueCastD_insertList_of_mem [BEq α] [LawfulBEq α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k') {v : β k} {fallback : β k'}
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValueCastD k' (insertList l toInsert) fallback =
    cast (by congr; exact LawfulBEq.eq_of_beq k_beq) v := by
  rw [getValueCastD_eq_getValueCast?,
    getValueCast?_insertList_of_mem distinct_l k_beq distinct_toInsert mem, Option.getD_some]

theorem getKey?_insertList_of_contains_eq_false [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (not_contains : (toInsert.map Sigma.fst).contains k = false) :
    getKey? k (insertList l toInsert) = getKey? k l := by
  rw [← containsKey_eq_contains_map_fst] at not_contains
  rw [getKey?_eq_getEntry?, getKey?_eq_getEntry?,
    getEntry?_insertList_of_contains_eq_false not_contains]

theorem getKey?_insertList_of_mem [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k')
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
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Sigma.fst)
    {h} :
    getKey k' (insertList l toInsert) h = k := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey,
    getKey?_insertList_of_mem distinct_l k_beq distinct_toInsert mem]

theorem getKey!_insertList_of_contains_eq_false [BEq α] [EquivBEq α] [Inhabited α]
    {l toInsert : List ((a : α) × β a)} {k : α}
    (contains_false : (toInsert.map Sigma.fst).contains k = false) :
    getKey! k (insertList l toInsert) = getKey! k l := by
  rw [getKey!_eq_getKey?, getKey?_insertList_of_contains_eq_false contains_false, getKey!_eq_getKey?]

theorem getKey!_insertList_of_mem [BEq α] [EquivBEq α] [Inhabited α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Sigma.fst) :
    getKey! k' (insertList l toInsert) = k := by
  rw [getKey!_eq_getKey?, getKey?_insertList_of_mem distinct_l k_beq distinct_toInsert mem,
    Option.get!_some]

theorem getKeyD_insertList_of_contains_eq_false [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)} {k fallback : α}
    (not_contains : (toInsert.map Sigma.fst).contains k = false) :
    getKeyD k (insertList l toInsert) fallback = getKeyD k l fallback := by
  rw [getKeyD_eq_getKey?, getKey?_insertList_of_contains_eq_false not_contains, getKeyD_eq_getKey?]

theorem getKeyD_insertList_of_mem [BEq α] [EquivBEq α]
    {l toInsert : List ((a : α) × β a)}
    (distinct_l : DistinctKeys l)
    {k k' fallback : α} (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Sigma.fst) :
    getKeyD k' (insertList l toInsert) fallback = k := by
  rw [getKeyD_eq_getKey?, getKey?_insertList_of_mem distinct_l k_beq distinct_toInsert mem,
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
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst) :
    getKey? k' (insertListConst l toInsert) = some k := by
  unfold insertListConst
  apply getKey?_insertList_of_mem distinct_l k_beq
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
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst)
    {h} :
    getKey k' (insertListConst l toInsert) h = k := by
  rw [← Option.some_inj, ← getKey?_eq_some_getKey,
    getKey?_insertListConst_of_mem distinct_l k_beq distinct_toInsert mem]

theorem getKey!_insertListConst_of_contains_eq_false [BEq α] [EquivBEq α] [Inhabited α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getKey! k (insertListConst l toInsert) = getKey! k l := by
  rw [getKey!_eq_getKey?, getKey?_insertListConst_of_contains_eq_false not_contains,
    getKey!_eq_getKey?]

theorem getKey!_insertListConst_of_mem [BEq α] [EquivBEq α] [Inhabited α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst) :
    getKey! k' (insertListConst l toInsert) = k := by
  rw [getKey!_eq_getKey?, getKey?_insertListConst_of_mem distinct_l k_beq distinct_toInsert mem,
    Option.get!_some]

theorem getKeyD_insertListConst_of_contains_eq_false [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k fallback : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getKeyD k (insertListConst l toInsert) fallback = getKeyD k l fallback := by
  rw [getKeyD_eq_getKey?, getKey?_insertListConst_of_contains_eq_false not_contains,
    getKeyD_eq_getKey?]

theorem getKeyD_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)}
    (distinct_l : DistinctKeys l)
    {k k' fallback : α} (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : k ∈ toInsert.map Prod.fst) :
    getKeyD k' (insertListConst l toInsert) fallback = k := by
  rw [getKeyD_eq_getKey?, getKey?_insertListConst_of_mem distinct_l k_beq distinct_toInsert mem,
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
  rw [← List.length_map Prod.toSigma]
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
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k') {v : β}
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
    (distinct_l : DistinctKeys l)
    {k k' : α} (k_beq : k == k') {v : β}
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert)
    {h} :
    getValue k' (insertListConst l toInsert) h = v := by
  rw [← Option.some_inj, ← getValue?_eq_some_getValue,
    getValue?_insertListConst_of_mem distinct_l k_beq distinct_toInsert mem]

theorem getValue!_insertListConst_of_contains_eq_false [BEq α] [PartialEquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getValue! k (insertListConst l toInsert) = getValue! k l := by
  simp only [getValue!_eq_getValue?]
  rw [getValue?_insertListConst_of_contains_eq_false not_contains]

theorem getValue!_insertListConst_of_mem [BEq α] [EquivBEq α] [Inhabited β]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k k' : α} {v: β}
    (distinct_l : DistinctKeys l)
    (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValue! k' (insertListConst l toInsert) = v := by
  rw [getValue!_eq_getValue?,
    getValue?_insertListConst_of_mem distinct_l k_beq distinct_toInsert mem, Option.get!_some]

theorem getValueD_insertListConst_of_contains_eq_false [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k : α} {fallback : β}
    (not_contains : (toInsert.map Prod.fst).contains k = false) :
    getValueD k (insertListConst l toInsert) fallback = getValueD k l fallback := by
  simp only [getValueD_eq_getValue?]
  rw [getValue?_insertListConst_of_contains_eq_false not_contains]

theorem getValueD_insertListConst_of_mem [BEq α] [EquivBEq α]
    {l : List ((_ : α) × β)} {toInsert : List (α × β)} {k k' : α} {v fallback: β}
    (distinct_l : DistinctKeys l)
    (k_beq : k == k')
    (distinct_toInsert : toInsert.Pairwise (fun a b => (a.1 == b.1) = false))
    (mem : ⟨k, v⟩ ∈ toInsert) :
    getValueD k' (insertListConst l toInsert) fallback= v := by
  simp only [getValueD_eq_getValue?]
  rw [getValue?_insertListConst_of_mem distinct_l k_beq distinct_toInsert mem, Option.getD_some]

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
    {toInsert : List α} (distinct: DistinctKeys l) :
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
    (distinct : toInsert.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ toInsert) :
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
    (h : containsKey k l = true) :
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
    (contains : containsKey k l = true) {h} :
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
    {l : List ((_ : α) × Unit)} {toInsert : List α} :
    l.length ≤ (insertListIfNewUnit l toInsert).length := by
  induction toInsert generalizing l with
  | nil => apply Nat.le_refl
  | cons hd tl ih => exact Nat.le_trans length_le_length_insertEntryIfNew ih

theorem length_insertListIfNewUnit_le [BEq α] [EquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α} :
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

theorem getValue?_list_unit [BEq α] {l : List ((_ : α) × Unit)} {k : α} :
    getValue? k l = if containsKey k l = true then some () else none := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [getValue?, containsKey, Bool.or_eq_true, Bool.cond_eq_ite_iff]
    by_cases hd_k: (hd.fst == k) = true
    · simp [hd_k]
    · simp [hd_k, ih]

theorem getValue?_insertListIfNewUnit [BEq α] [PartialEquivBEq α]
    {l : List ((_ : α) × Unit)} {toInsert : List α} {k : α} :
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
      if containsKey k l ∧ (f (getValueCast? k l)).isNone then
        l.length - 1
      else if containsKey k l = false ∧ (f (getValueCast? k l)).isSome then
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

theorem getKey_alterKey {k k' : α} {f : Option (β k) → Option (β k)}
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
      if containsKey k l ∧ (f (getValue? k l)).isNone then
        l.length - 1
      else if containsKey k l = false ∧ (f (getValue? k l)).isSome then
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

theorem getKey_alterKey [EquivBEq α] {k k' : α} {f : Option β → Option β}
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

theorem DistinctKeys.modifyKey [BEq α] [LawfulBEq α] {a f} {l : List ((a : α) × β a)}
    (hd : DistinctKeys l) : DistinctKeys (modifyKey a f l) := by
  simpa [modifyKey_eq_alterKey] using hd.alterKey

theorem modifyKey_of_perm [BEq α] [LawfulBEq α] {l l' : List ((a : α) × β a)}
    {k : α} {f : β k → β k} (hl : DistinctKeys l) (h : Perm l l') :
    Perm (modifyKey k f l) (modifyKey k f l') := by
  simp only [modifyKey_eq_alterKey, alterKey_of_perm hl h]

theorem getValueCast?_modifyKey [BEq α] [LawfulBEq α] {k k' : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
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

theorem getKey_modifyKey [BEq α] [LawfulBEq α] {k k' : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) (h : containsKey k' (modifyKey k f l)) :
    getKey k' (modifyKey k f l) h =
      if k == k' then
        k
      else
        haveI h' : containsKey k' l := by rwa [containsKey_modifyKey] at h
        getKey k' l h' := by
  simp only [modifyKey_eq_alterKey, getKey_alterKey, hl, ← dite_eq_ite]

@[simp]
theorem getKey_modifyKey_self [BEq α] [LawfulBEq α] {k : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (_ : DistinctKeys l) (h : containsKey k (modifyKey k f l)) :
    getKey k (modifyKey k f l) h = k := by
  simp only [getKey_eq]

theorem getKeyD_modifyKey [BEq α] [LawfulBEq α] {k k' fallback : α} {f : β k → β k}
    (l : List ((a : α) × β a)) (hl : DistinctKeys l) :
    getKeyD k' (modifyKey k f l) fallback =
      if k == k' then
        if containsKey k l then k else fallback
      else
        getKeyD k' l fallback := by
  simp [modifyKey_eq_alterKey, getKeyD_alterKey, containsKey_eq_isSome_getValueCast?, hl]

theorem getKeyD_modifyKey_self [BEq α] [LawfulBEq α] {k fallback : α} {f : β k → β k}
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

theorem modifyKey_of_perm [EquivBEq α] {l l' : List ((_ : α) × β)} {k : α} {f : β → β}
    (hl : DistinctKeys l) (h : Perm l l') :
    Perm (modifyKey k f l) (modifyKey k f l') := by
  simp only [modifyKey_eq_alterKey, alterKey_of_perm hl h]

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

theorem getKey_modifyKey [EquivBEq α] {k k' : α} {f : β → β} (l : List ((_ : α) × β))
    (hl : DistinctKeys l) (h : containsKey k' (modifyKey k f l)) :
    getKey k' (modifyKey k f l) h =
      if k == k' then
        k
      else
        haveI h' : containsKey k' l := by rwa [containsKey_modifyKey] at h
        getKey k' l h' := by
  simp only [modifyKey_eq_alterKey, getKey_alterKey, hl]
  rfl

@[simp]
theorem getKey_modifyKey_self [EquivBEq α] {k : α} {f : β → β}
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

theorem getKeyD_modifyKey_self [EquivBEq α] {k fallback : α} {f : β → β}
    (l : List ((_ : α) × β)) (hl : DistinctKeys l) :
    getKeyD k (modifyKey k f l) fallback = if containsKey k l then k else fallback := by
  simp [getKeyD_modifyKey, hl]

end Const

theorem constModifyKey_eq_modifyKey {β : Type v} [BEq α] [LawfulBEq α] {k : α} {f : β → β}
    {l : List ((_ : α) × β)} :
    Const.modifyKey k f l = modifyKey k f l := by
  rw [modifyKey, Const.modifyKey, getValue?_eq_getValueCast?]
  cases getValueCast? k l <;> rfl

theorem DistinctKeys.constModifyKey {β : Type v} [BEq α] [EquivBEq α] {a f} {l : List ((_ : α) × β)}
    (hd : DistinctKeys l) : DistinctKeys (Const.modifyKey a f l) := by
  simpa [Const.modifyKey_eq_alterKey] using hd.constAlterKey

end Modify

section Min

private local instance leSigmaOfOrd [Ord α] : LE ((a : α) × β a) where
  le a b := (compare a.1 b.1).isLE

private local instance [Ord α] : DecidableLE ((a : α) × β a) :=
  fun a b => inferInstanceAs <| Decidable (compare a.1 b.1).isLE

private theorem leSigmaOfOrd_total [Ord α] [OrientedOrd α] (a b : (a : α) × β a) :
    a ≤ b ∨ b ≤ a := by
  simp only [leSigmaOfOrd]
  rw [← OrientedCmp.isGE_iff_isLE]
  cases compare b.fst a.fst <;> trivial

private local instance minSigmaOfOrd [Ord α] : Min ((a : α) × β a) where
  min a b := if compare a.1 b.1 |>.isLE then a else b

theorem min_def [Ord α] {p q : (a : α) × β a} :
    min p q = if compare p.1 q.1 |>.isLE then p else q :=
  rfl

private local instance [Ord α] [TransOrd α] :
    Std.Associative (min : (a : α) × β a → (a : α) × β a → (a : α) × β a) where
  assoc a b c := by
    simp only [min_def]
    split <;> split <;> (try split) <;> try rfl
    · rename_i hab hac hbc
      refine absurd ?_ hac
      exact TransCmp.isLE_trans hab hbc
    · rename_i hab hbc hac
      refine absurd hac ?_
      simp only [Bool.not_eq_true, Ordering.isLE_eq_false] at ⊢ hab hbc
      exact TransCmp.gt_trans hab hbc

/-- Like `List.min?`, but using an `Ord` typeclass instead of a `Min` typeclass. -/
def minEntry? [Ord α] (xs : List ((a : α) × β a)) : Option ((a : α) × β a) :=
  xs.min?

/-- Returns the smallest key in an associative list. -/
def minKey? [Ord α] (xs : List ((a : α) × β a)) : Option α :=
  minEntry? xs |>.map Sigma.fst

theorem DistinctKeys.eq_of_mem_of_beq [BEq α] [EquivBEq α] {a b : (a : α) × β a}
    {l : List ((a : α) × β a)} (hma : a ∈ l) (hmb : b ∈ l) (he : a.1 == b.1) (hd : DistinctKeys l) :
    a = b := by
  replace hd := hd.distinct
  induction hma
  · cases hmb
    · rfl
    · simp [pairwise_cons.mp hd |>.1 b.1 <| fst_mem_keys_of_mem ‹_›] at he
  · rename_i _ ih
    have hd := pairwise_cons.mp hd
    cases hmb
    · simp [BEq.symm_false <| hd.1 a.1 <| fst_mem_keys_of_mem ‹_›] at he
    · exact ih ‹_› hd.2

theorem min_eq_or [Ord α] {p q : (a : α) × β a} : min p q = p ∨ min p q = q := by
  rw [min_def]
  split <;> simp

theorem min_eq_left [Ord α] {p q : (a : α) × β a} (h : compare p.1 q.1 |>.isLE) : min p q = p := by
  simp [min_def, h]

theorem min_eq_left_of_lt [Ord α] {p q : (a : α) × β a} (h : compare p.1 q.1 = .lt) : min p q = p :=
  min_eq_left (Ordering.isLE_of_eq_lt h)

theorem minEntry?_eq_head? [Ord α] {l : List ((a : α) × β a)}
    (hl : l.Pairwise (fun a b => compare a.1 b.1 = .lt)) : minEntry? l = l.head? := by
  rw [minEntry?, List.min?_eq_head? (hl.imp min_eq_left_of_lt)]

@[simp]
theorem minEntry?_nil [Ord α] : minEntry? ([] : List ((a : α) × β a)) = none := by
  simp [minEntry?, List.min?]

theorem minEntry?_cons [Ord α] [TransOrd α] (e : (a : α) × β a) (l : List ((a : α) × β a)) :
    minEntry? (e :: l) = some (match minEntry? l with
    | none => e
    | some w => min e w) := by
  simp only [minEntry?, List.min?_cons]
  split <;> simp_all only [List.min?_eq_none_iff, List.min?_nil, Option.elim_none, Option.elim_some]

theorem isSome_minEntry?_of_isEmpty_eq_false [Ord α] {l : List ((a : α) × β a)} (hl : l.isEmpty = false) :
    (minEntry? l).isSome := by
  cases l
  · simp_all [minEntry?]
  · simp [minEntry?, List.min?]

theorem le_min_iff [Ord α] [TransOrd α] {a b c : (a : α) × β a} :
    a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
  simp only [min_def]
  split
  · simp only [iff_self_and]
    exact fun h => TransCmp.isLE_trans h ‹_›
  · simp only [Bool.not_eq_true, Ordering.isLE_eq_false, OrientedCmp.gt_iff_lt, iff_and_self] at *
    exact fun h => Ordering.isLE_of_eq_lt <| TransCmp.lt_of_isLE_of_lt h ‹_›

theorem minEntry?_eq_some_iff [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] (a : (a : α) × β a) {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minEntry? l = some a ↔ a ∈ l ∧ ∀ b : α, containsKey b l → (compare a.fst b).isLE := by
  rw [minEntry?, List.min?_eq_some_iff _ _ _ _]
  · simp only [and_congr_right_iff]
    intro hm
    apply Iff.intro
    · intro h k hk
      obtain ⟨e, hel, hek⟩ := containsKey_eq_true_iff_exists_mem.mp hk
      exact TransCmp.isLE_trans (h _ hel) <| Ordering.isLE_of_eq_eq <| compare_eq_iff_beq.mpr hek
    · intro h e he
      exact h _ <| containsKey_of_mem he
  · exact fun _ => ReflCmp.isLE_rfl
  · exact fun _ _ => min_eq_or
  · exact fun a b c => le_min_iff
  · intro e e' he he' hee' he'e
    exact hd.eq_of_mem_of_beq he he' <| compare_eq_iff_beq.mp <| TransCmp.isLE_antisymm hee' he'e

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minKey? l = some k ↔ getKey? k l = some k ∧ ∀ k' : α, containsKey k' l → (compare k k').isLE := by
  simp only [minKey?, Option.map_eq_some', minEntry?_eq_some_iff _ hd]
  simp only [getKey?_eq_getEntry?, Option.map_eq_some', getEntry?_eq_some_iff hd]
  apply Iff.intro
  · rintro ⟨_, ⟨hm, hcmp⟩, rfl⟩
    exact ⟨⟨_, ⟨BEq.refl, hm⟩, rfl⟩, hcmp⟩
  · rintro ⟨⟨_, ⟨_, hm⟩, rfl⟩, hcmp⟩
    exact ⟨_, ⟨hm, hcmp⟩, rfl⟩

theorem minKey?_eq_some_iff_mem_and_forall [Ord α] [LawfulEqOrd α] [TransOrd α] [BEq α]
    [LawfulBEqOrd α] {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minKey? l = some k ↔ containsKey k l ∧ ∀ k' : α, containsKey k' l → (compare k k').isLE := by
  simp only [minKey?, Option.map_eq_some', minEntry?_eq_some_iff _ hd]
  apply Iff.intro
  · rintro ⟨_, ⟨hm, hcmp⟩, rfl⟩
    exact ⟨containsKey_of_mem hm, hcmp⟩
  · rintro ⟨hc, hle⟩
    have heq := beq_iff_eq.mp <| getKey_eq_getEntry_fst (α := α) ▸ getKey_beq hc
    refine ⟨getEntry k l hc, ⟨mem_getEntry hc, ?_⟩, heq⟩
    intro k' hk'
    rw [heq]
    exact hle _ hk'

theorem minEntry?_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l l' : List ((a : α) × β a)} (hl : DistinctKeys l) (hp : l.Perm l') :
    minEntry? l = minEntry? l' := by
  cases l
  case nil => simp_all only [List.nil_perm]
  case cons e es =>
    ext
    simp only [Option.mem_def, minEntry?_eq_some_iff _ hl, hp.mem_iff, containsKey_of_perm hp]
    exact minEntry?_eq_some_iff _ (hl.perm hp.symm) |>.symm

theorem minKey?_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l l' : List ((a : α) × β a)}
    (hl : DistinctKeys l) (hp : l.Perm l') :
    minKey? l = minKey? l' := by
  simp only [minKey?, minEntry?_of_perm hl hp]

theorem minEntry?_eq_none_iff_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    minEntry? l = none ↔ l.isEmpty := by
  simp only [List.isEmpty_iff, minEntry?, List.min?_eq_none_iff]

theorem minKey?_eq_none_iff_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    minKey? l = none ↔ l.isEmpty := by
  simp [minKey?, minEntry?_eq_none_iff_isEmpty]

theorem minKey?_of_isEmpty [Ord α] [TransOrd α] {l : List ((a : α) × β a)} (he : l.isEmpty) :
    minKey? l = none :=
  minKey?_eq_none_iff_isEmpty.mpr he

theorem isNone_minEntry?_eq_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    (minEntry? l).isNone = l.isEmpty := by
  rw [Bool.eq_iff_iff]
  simp only [Option.isNone_iff_eq_none, minEntry?_eq_none_iff_isEmpty, List.isEmpty_iff]

theorem isNone_minKey?_eq_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    (minKey? l).isNone = l.isEmpty := by
  simpa [minKey?] using isNone_minEntry?_eq_isEmpty

theorem isSome_minEntry?_eq_not_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    (minEntry? l).isSome = !l.isEmpty := by
  rw [← Bool.not_inj_iff, Bool.not_not, Bool.eq_iff_iff, Bool.not_eq_true', Option.not_isSome,
    Option.isNone_iff_eq_none]
  apply minEntry?_eq_none_iff_isEmpty

theorem isSome_minKey?_eq_not_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    (minKey? l).isSome = !l.isEmpty := by
  simpa [minKey?] using isSome_minEntry?_eq_not_isEmpty

theorem isSome_minKey?_iff_isEmpty_eq_false [Ord α] {l : List ((a : α) × β a)} :
    (minKey? l).isSome ↔ l.isEmpty = false := by
  simp [isSome_minKey?_eq_not_isEmpty]

theorem min_apply [Ord α] {e₁ e₂ : (a : α) × β a} {f : (a : α) × β a → (a : α) × β a}
    (hf : compare e₁.1 e₂.1 = compare (f e₁).1 (f e₂).1) :
   min (f e₁) (f e₂) = f (min e₁ e₂) := by
  simp only [min_def, hf, apply_ite f]

theorem minEntry?_map [Ord α] (l : List ((a : α) × β a)) (f : (a : α) × β a → (a : α) × β a)
    (hf : ∀ e₁ e₂, compare e₁.1 e₂.1 = compare (f e₁).1 (f e₂).1) :
    minEntry? (l.map f) = (minEntry? l).map f := by
  simp only [minEntry?, List.min?]
  cases l <;> try rfl
  rename_i e es
  simp only [List.map_cons, Option.map_some', Option.some.injEq]
  rw [← List.foldr_reverse, ← List.foldr_reverse, ← List.map_reverse]
  induction es.reverse with
  | nil => rfl
  | cons _ _ ih =>
    simp [ih, min_apply (hf ..)]

theorem replaceEntry_eq_map [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k v}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    replaceEntry k v l = l.map fun e => if e.1 == k then ⟨k, v⟩ else e := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [replaceEntry, cond_eq_if, List.map_cons]
    split
    · rename_i heq
      simp only [List.cons.injEq, true_and]
      replace hl : containsKey k es = false := containsKey_congr heq ▸ hl.containsKey_eq_false
      clear ih
      induction es with
      | nil => rfl
      | cons e' es ih =>
        simp only [List.map_cons, List.cons.injEq]
        rw [containsKey_cons] at hl
        simp only [Bool.or_eq_false_iff] at hl
        simpa [hl.1] using ih hl.2
    · simp [ih hl.tail]

theorem minEntry?_replaceEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    minEntry? (replaceEntry k v l) =
      (minEntry? l).map fun e => if e.1 == k then ⟨k, v⟩ else e := by
  rw [replaceEntry_eq_map hl, minEntry?_map]
  intro e₁ e₂
  refine (TransCmp.congr_left ?_).trans (TransCmp.congr_right ?_)
  all_goals
    split
    · exact compare_eq_iff_beq.mpr ‹_›
    · exact compare_self

theorem isSome_minEntry?_of_contains [Ord α] [BEq α] {l : List ((a : α) × β a)} {b : α}
    (hb : containsKey b l) :
    (minEntry? l).isSome := by
  apply isSome_minEntry?_of_isEmpty_eq_false
  match l with
  | [] => contradiction
  | x :: xs => simp

theorem minEntry?_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    minEntry? (insertEntry k v l) =
      some (match minEntry? l with
        | none => ⟨k, v⟩
        | some w => if compare k w.fst |>.isLE then ⟨k, v⟩ else w) := by
  simp only [insertEntry]
  cases h : containsKey k l
  · simp only [cond_false, minEntry?_cons, Option.some.injEq]
    rfl
  · rw [cond_true, minEntry?_replaceEntry hl, Option.map_eq_some']
    have := isSome_minEntry?_of_contains ‹_›
    simp only [Option.isSome_iff_exists] at this
    obtain ⟨a, ha⟩ := this
    refine ⟨a, ha, ?_⟩
    simp only [ha]
    simp only [minEntry?_eq_some_iff _ hl] at ha
    replace ha := ha.2 k ‹_›
    cases hc : (compare k a.fst).isLE
    · simp_all [OrientedCmp.gt_iff_lt, ← compare_eq_iff_beq]
    · simp_all [TransCmp.isLE_antisymm ha hc, ← compare_eq_iff_beq]

theorem minKey?_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    minKey? (insertEntry k v l) =
      some ((minKey? l).elim k fun k' => if compare k k' |>.isLE then k else k') := by
  simp only [minKey?, minEntry?_insertEntry hl]
  cases minEntry? l <;> simp [apply_ite Sigma.fst]

theorem isSome_minEntry?_insert [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    minEntry? (insertEntry k v l) |>.isSome := by
  simp [minEntry?_insertEntry hl]

theorem isSome_minKey?_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    minKey? (insertEntry k v l) |>.isSome := by
  simp only [minKey?_insertEntry hl, Option.isSome_some]

theorem isSome_minEntry?_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k}
    {l : List ((a : α) × β a)} (hc : containsKey k l) :
    minEntry? l |>.isSome := by
  simp [isSome_minEntry?_eq_not_isEmpty, isEmpty_eq_false_of_containsKey hc]

theorem isSome_minKey?_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k}
    {l : List ((a : α) × β a)} (hc : containsKey k l) :
    minKey? l |>.isSome := by
  simpa [minKey?] using isSome_minEntry?_of_containsKey hc

theorem getEntry?_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {em} (hem : minEntry? l = some em) :
    getEntry? em.1 l = some em := by
  simp only [minEntry?_eq_some_iff _ hd] at hem
  exact getEntry?_of_mem hd BEq.refl hem.1

theorem minKey?_bind_getEntry? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    (minKey? l |>.bind fun k => getEntry? k l) = minEntry? l := by
  rw [minKey?]
  cases h : minEntry? l
  · rfl
  · simp [getEntry?_minKey? hd h]

theorem getKey?_minKey? [Ord α] [TransOrd α] [BEq α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km} (hkm : minKey? l = some km) :
    getKey? km l = some km := by
  simp_all [minKey?_eq_some_iff_getKey?_eq_self_and_forall hd]

private theorem Option.get_eq_iff_eq_some {o : Option α} {h k} :
    o.get h = k ↔ o = some k := by
  simp [Option.eq_some_iff_get_eq, exists_prop_of_true h]

private theorem Option.eq_get_iff_some_eq {o : Option α} {h k} :
    k = o.get h ↔ some k = o := by
  conv => congr <;> rw [eq_comm]
  exact get_eq_iff_eq_some

theorem getKey_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km hc} :
    (hkm : (minKey? l |>.get <| isSome_minKey?_of_containsKey hc) = km) → getKey km l hc = km := by
  have := (Option.eq_some_iff_get_eq.mp <| getKey?_eq_some_getKey hc).2
  simp only [← this, Option.get_eq_iff_eq_some]
  exact getKey?_minKey? hd

theorem getKey!_minKey? [Ord α] [TransOrd α] [Inhabited α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km} :
    (hkm : minKey? l = some km) → getKey! km l = km := by
  intro h
  simp [getKey!_eq_getKey?, getKey?_minKey? hd h]

theorem getKeyD_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km fallback} :
    (hkm : minKey? l = some km) → getKeyD km l fallback = km := by
  intro h
  simp [getKeyD_eq_getKey?, getKey?_minKey? hd h]

theorem minKey?_bind_getKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    (minKey? l |>.bind fun k => getKey? k l) = minKey? l := by
  cases h : minKey? l
  · rfl
  · simpa using getKey?_minKey? hd h

theorem containsKey_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l : List ((a : α) × β a)}
    (hd : DistinctKeys l) {km} (hkm : minKey? l = some km) :
    containsKey km l := by
  simp only [minKey?, Option.map_eq_some', minEntry?_eq_some_iff _ hd] at hkm
  obtain ⟨e, ⟨hm, _⟩, rfl⟩ := hkm
  exact containsKey_of_mem hm

theorem minKey?_eraseKey_eq_iff_beq_minKey?_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minKey? (eraseKey k l) = minKey? l ↔ ∀ {km}, minKey? l = some km → (k == km) = false := by
  cases h : minKey? l
  · simp_all [minKey?_eq_none_iff_isEmpty]
  · simp only [minKey?_eq_some_iff_getKey?_eq_self_and_forall, getKey?_eraseKey,
      containsKey_eraseKey, compare_eq_iff_beq, hd, hd.eraseKey] at ⊢ h
    simp_all

theorem minKey?_eraseKey_eq_of_beq_minKey?_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (hc : ∀ {km}, minKey? l = some km → (k == km) = false) :
    minKey? (eraseKey k l) = minKey? l := by
  rw [minKey?_eraseKey_eq_iff_beq_minKey?_eq_false hd |>.mpr]
  revert hc
  cases minKey? l <;> simp [Ordering.isNe_iff_ne_eq]

theorem minKey?_insertEntry_le_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hl : DistinctKeys l) {km kmi} (hkm : minKey? l = some km)
    (hkmi : (insertEntry k v l |> minKey? |>.get <| isSome_minKey?_insertEntry hl) = kmi) :
    compare kmi km |>.isLE := by
  simp only [← hkmi, minKey?_insertEntry hl, hkm, Option.get_some, Option.elim_some]
  split <;> simp [*]

theorem minKey?_insertEntry_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hl : DistinctKeys l) {kmi}
    (hkmi : (insertEntry k v l |> minKey? |>.get <| isSome_minKey?_insertEntry hl) = kmi) :
    compare kmi k |>.isLE := by
  simp only [← hkmi, minKey?_insertEntry hl, Option.get_some]
  cases minKey? l
  · simp
  · dsimp only [Option.elim_some]
    cases hcmp : compare k _ <;> simp_all [OrientedCmp.gt_iff_lt]

theorem minKey?_le_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k km}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (hc : containsKey k l)
    (hkm : (minKey? l |>.get <| isSome_minKey?_of_containsKey hc) = km) :
    compare km k |>.isLE := by
  simpa only [← hkm] using
    minKey?_eq_some_iff_getKey?_eq_self_and_forall hd |>.mp (by simp) |>.2 _ hc

theorem le_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k} {l : List ((a : α) × β a)}
    (hd : DistinctKeys l) :
    (∀ k', minKey? l = some k' → (compare k k').isLE) ↔
      (∀ k', containsKey k' l → (compare k k').isLE) := by
  apply Iff.intro
  · intro h k' hk'
    have := isSome_minKey?_of_containsKey hk'
    specialize h (minKey? l |>.get <| isSome_minKey?_of_containsKey hk') (by simp)
    exact TransCmp.isLE_trans h <| minKey?_le_of_containsKey hd hk' rfl
  · intro h k' hk'
    exact h k' (containsKey_minKey? hd hk')

theorem isSome_minKey?_of_isSome_minKey?_eraseKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k}
    {l : List ((a : α) × β a)} (hs : eraseKey k l |> minKey? |>.isSome) :
    minKey? l |>.isSome := by
  simp_all [isSome_minKey?_eq_not_isEmpty, isEmpty_eraseKey]

theorem containsKey_minKey?_eraseKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {kme}
    (hkme : (eraseKey k l |> minKey?) = some kme) :
    containsKey kme l := by
  apply containsKey_of_containsKey_eraseKey hd
  apply containsKey_minKey? hd.eraseKey hkme

theorem minKey?_le_minKey?_eraseKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k km kme}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (hkme : (eraseKey k l |> minKey?) = some kme)
    (hkm : (minKey? l |>.get <|
      isSome_minKey?_of_isSome_minKey?_eraseKey <| hkme ▸ Option.isSome_some) = km) :
    compare km kme |>.isLE := by
  apply minKey?_le_of_containsKey hd _ hkm
  apply containsKey_minKey?_eraseKey hd hkme

theorem minKey?_cons [Ord α] [TransOrd α] (e : (a : α) × β a) (l : List ((a : α) × β a)) :
    minKey? (e :: l) = some (match minKey? l with
    | none => e.1
    | some w => if compare e.1 w |>.isLE then e.1 else w) := by
  simp [minKey?, minEntry?_cons]
  cases minEntry? l
  · rfl
  · simp [min_def, apply_ite Sigma.fst]

theorem minEntry?_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minEntry? (insertEntryIfNew k v l) =
      some (match minEntry? l with
        | none => ⟨k, v⟩
        | some e => if compare k e.1 = .lt then ⟨k, v⟩ else e) := by
  simp [insertEntryIfNew]
  cases hc : containsKey k l
  · simp only [cond_false, minEntry?_cons, Option.some.injEq]
    cases he : minEntry? l
    · simp
    · rename_i e
      simp [min_def]
      cases hcmp : compare k e.fst
      · simp
      · simp
        rw [containsKey_congr <| compare_eq_iff_beq.mp hcmp] at hc
        rw [containsKey_minKey? hd] at hc
        · contradiction
        · simp_all [minKey?]
      · simp
  · simp only [cond_true]
    have := isSome_minEntry?_of_containsKey hc
    cases h : minEntry? l
    · simp_all
    · simp
      split
      · have := minKey?_le_of_containsKey hd hc (by simp [minKey?, h]; rfl)
        simp_all [← OrientedCmp.gt_iff_lt]
      · rfl

theorem minKey?_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minKey? (insertEntryIfNew k v l) =
      some ((minKey? l).elim k fun k' => if compare k k' = .lt then k else k') := by
  simp [minKey?, minEntry?_insertEntryIfNew hd]
  cases minEntry? l <;> simp [apply_ite Sigma.fst]

theorem isSome_minEntry?_insertIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    minEntry? (insertEntryIfNew k v l) |>.isSome := by
  simp [minEntry?_insertEntryIfNew hl]

theorem isSome_minKey?_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hl : DistinctKeys l) :
    minKey? (insertEntryIfNew k v l) |>.isSome := by
  simp [minKey?_insertEntryIfNew  hl]

theorem minKey?_insertEntryIfNew_le_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hl : DistinctKeys l) {km kmi} (hkm : minKey? l = some km)
    (hkmi : (insertEntryIfNew k v l |> minKey? |>.get <| isSome_minKey?_insertEntryIfNew hl) = kmi) :
    compare kmi km |>.isLE := by
  simp only [← hkmi, minKey?_insertEntryIfNew hl, hkm, Option.get_some, Option.elim_some]
  split <;> simp [*]

theorem minKey?_insertEntryIfNew_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k kmi : α}
    {v : β k} {l : List ((a : α) × β a)} (hl : DistinctKeys l)
    (hkmi : (insertEntryIfNew k v l |> minKey? |>.get <| isSome_minKey?_insertEntryIfNew hl) = kmi) :
    compare kmi k |>.isLE := by
  simp only [← hkmi, minKey?_insertEntryIfNew hl, Option.get_some]
  cases minKey? l
  · simp
  · simp only [Option.elim_some]
    cases hcmp : compare k _ <;> (try simp; done)
    all_goals
      rw [OrientedCmp.eq_swap (cmp := compare)]
      simp_all

theorem minKey?_eq_head?_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) :
    minKey? l = (keys l).head? := by
  simp [minKey?, minEntry?_eq_head? ho, keys_eq_map]

theorem minKey?_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α] {k f}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minKey? (modifyKey k f l) = minKey? l := by
  cases hkm : minKey? l
  · simp_all [minKey?_eq_none_iff_isEmpty, modifyKey]
  · simp_all [minKey?_eq_some_iff_mem_and_forall, hd.modifyKey, containsKey_modifyKey]

theorem minKey?_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {k f} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    minKey? (alterKey k f l) = some k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simp only [minKey?_eq_some_iff_getKey?_eq_self_and_forall hd.alterKey, getKey?_alterKey _ hd,
    beq_self_eq_true, ↓reduceIte, ite_eq_left_iff, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, reduceCtorEq, imp_false, ← Option.isSome_iff_ne_none,
    containsKey_alterKey hd, beq_iff_eq, Bool.ite_eq_true_distrib, and_congr_right_iff]
  intro hf
  apply Iff.intro
  · intro hk k' hk'
    simpa [hk', hf] using hk k'
  · intro hk k' hk'
    simp only [hf, if_true_left] at hk'
    by_cases hbeq : k == k'
    · simp [compare_eq_iff_beq.mpr hbeq]
    · exact hk k' (hk' hbeq)

namespace Const

variable {β : Type v}

theorem minKey?_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f}
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) :
    minKey? (modifyKey k f l) = (minKey? l).map fun km => if km == k then k else km := by
  cases hkm : minKey? l
  · simp_all [minKey?_eq_none_iff_isEmpty, modifyKey]
  · simp_all [minKey?_eq_some_iff_getKey?_eq_self_and_forall, hd.constModifyKey, getKey?_modifyKey]
    cases h : _ == k
    · simp_all [BEq.symm_false h, containsKey_modifyKey]
    · simp_all [containsKey_congr (BEq.symm h), containsKey_eq_isSome_getKey?,
        containsKey_modifyKey, getKey?_modifyKey]
      intro k' hk'
      cases hcmp : compare k k' <;> try rfl
      replace hkm := hkm.2 k'
      simp only [← compare_eq_iff_beq] at *
      simp only [hcmp, reduceCtorEq, ↓reduceIte] at hk'
      specialize hkm hk'
      simp only [OrientedCmp.gt_iff_lt, Ordering.isLE_gt, Bool.false_eq_true] at *
      have := TransCmp.lt_of_isLE_of_lt hkm hcmp
      simp [this] at h

theorem minKey?_modifyKey_eq_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {k f} {l : List ((_ : α) × β)} (hd : DistinctKeys l) :
    minKey? (modifyKey k f l) = minKey? l := by
  simp only [minKey?_modifyKey hd]
  cases minKey? l
  · rfl
  · simp only [beq_iff_eq, Option.map_some', Option.some.injEq, ite_eq_right_iff]
    exact Eq.symm

theorem isSome_minKey?_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f}
    {l : List ((_ : α) × β)} :
    (modifyKey k f l |> minKey?).isSome = !l.isEmpty := by
  simp [Option.isSome_map', isSome_minKey?_eq_not_isEmpty, isEmpty_modifyKey]

theorem isSome_minKey?_modifyKey_eq_isSome [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f}
    {l : List ((_ : α) × β)} :
    (modifyKey k f l |> minKey?).isSome = (minKey? l).isSome := by
  simp [Option.isSome_map', isSome_minKey?_eq_not_isEmpty, isEmpty_modifyKey]

theorem minKey?_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f km kmm}
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) (hkm : minKey? l = some km)
    (hkmm : (modifyKey k f l |> minKey? |>.get <|
        isSome_minKey?_modifyKey_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) :
    kmm == km := by
  simp only [minKey?_modifyKey hd, Option.get_map] at hkmm
  simp only [Option.eq_some_iff_get_eq] at hkm
  simp only [← hkmm, ← hkm.2]
  split
  · exact BEq.symm ‹_›
  · exact BEq.refl

theorem minKey?_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k f} {l : List ((_ : α) × β)} (hd : DistinctKeys l) :
    minKey? (alterKey k f l) = some k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simp only [minKey?_eq_some_iff_getKey?_eq_self_and_forall hd.constAlterKey, getKey?_alterKey _ hd,
    ← compare_eq_iff_beq, compare_self, ↓reduceIte, ite_eq_left_iff, Bool.not_eq_true,
    Option.not_isSome, Option.isNone_iff_eq_none, reduceCtorEq, imp_false,
    ← Option.isSome_iff_ne_none, containsKey_alterKey hd, Bool.ite_eq_true_distrib,
    and_congr_right_iff]
  intro hf
  apply Iff.intro
  · intro hk k' hk'
    simpa [hk', hf] using hk k'
  · intro hk k' hk'
    simp only [hf, if_true_left] at hk'
    by_cases heq : compare k k' = .eq
    · simp [heq]
    · exact hk k' (hk' heq)

end Const

/-- Given a proof that the list is nonempty, returns the smallest key in an associative list. -/
def minKey [Ord α] (xs : List ((a : α) × β a)) (h : xs.isEmpty = false) : α :=
  minKey? xs |>.get (by simp [isSome_minKey?_eq_not_isEmpty, h])

theorem minKey_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l l' : List ((a : α) × β a)}
    {hl} (hd : DistinctKeys l) (hp : l.Perm l') :
    minKey l hl = minKey l' (hp.isEmpty_eq ▸ hl) := by
  simp [minKey, minKey?_of_perm hd hp]

theorem minKey_eq_get_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {he} :
    minKey l he = (minKey? l |>.get (by simp [isSome_minKey?_eq_not_isEmpty, he])) :=
  rfl

theorem minKey?_eq_some_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {he} :
    minKey? l = some (minKey l he) := by
  simp [minKey_eq_get_minKey?]

theorem minKey_eq_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he km} :
    minKey l he = km ↔ getKey? km l = some km ∧ ∀ k, containsKey k l → (compare km k).isLE := by
  simp [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some,
    minKey?_eq_some_iff_getKey?_eq_self_and_forall hd]

theorem minKey_eq_iff_mem_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he km} :
    minKey l he = km ↔ containsKey km l ∧ ∀ k, containsKey k l → (compare km k).isLE := by
  simp [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some, minKey?_eq_some_iff_mem_and_forall hd]

theorem minKey_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l : List ((a : α) × β a)}
    (hd : DistinctKeys l) {k v} :
    (insertEntry k v l |> minKey <| isEmpty_insertEntry) =
      ((minKey? l).elim k fun k' => if compare k k' |>.isLE then k else k') := by
  simp [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some, minKey?_insertEntry hd]

theorem minKey_insertEntry_le_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v he} :
    compare (insertEntry k v l |> minKey <| isEmpty_insertEntry) (minKey l he) |>.isLE := by
  simp only [minKey_eq_get_minKey?]
  exact minKey?_insertEntry_le_minKey? hd (by simp) rfl

theorem minKey_insertEntry_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare (insertEntry k v l |> minKey <| isEmpty_insertEntry) k |>.isLE := by
  simp only [minKey_eq_get_minKey?]
  exact minKey?_insertEntry_le_self hd rfl

theorem containsKey_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    containsKey (minKey l he) l :=
  containsKey_minKey? hd minKey?_eq_some_minKey

theorem minKey_le_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (hc : containsKey k l) :
    compare (minKey l <| isEmpty_eq_false_iff_exists_containsKey.mpr ⟨k, hc⟩) k |>.isLE :=
   minKey?_le_of_containsKey hd hc minKey_eq_get_minKey?.symm

theorem le_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    (compare k (minKey l he)).isLE ↔ (∀ k', containsKey k' l → (compare k k').isLE) := by
  simp only [minKey_eq_get_minKey?, ← le_minKey? hd, Option.eq_some_iff_get_eq]
  simp only [exists_prop_of_true (isSome_minKey?_iff_isEmpty_eq_false.mpr he), forall_eq']

theorem getKey?_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey? (minKey l he) l = some (minKey l he) :=
  getKey?_minKey? hd minKey?_eq_some_minKey

theorem getKey_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey (minKey l he) l (containsKey_minKey hd) = minKey l he := by
  simpa [getKey?_eq_some_getKey (containsKey_minKey hd)] using getKey?_minKey hd (he := he)

theorem getKey!_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey! (minKey l he) l = minKey l he := by
  simpa [getKey_eq_getKey!] using getKey_minKey hd

theorem getKeyD_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he fallback} :
    getKeyD (minKey l he) l fallback = minKey l he := by
  simpa [getKey_eq_getKeyD (fallback := fallback)] using getKey_minKey hd

theorem minKey_eraseKey_eq_iff_beq_minKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    (eraseKey k l |> minKey <| he) =
        minKey l (isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he) ↔
      (k == (minKey l <| isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he)) = false := by
  simp only [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some, Option.some_get]
  constructor
  · intro h
    exact minKey?_eraseKey_eq_iff_beq_minKey?_eq_false hd |>.mp h (by rw [Option.some_get])
  · intro h
    apply minKey?_eraseKey_eq_iff_beq_minKey?_eq_false hd |>.mpr
    intro km hkm
    simp_all only [Option.get_some]

theorem minKey_eraseKey_eq_of_beq_minKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    (hc : (k == (minKey l (isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he))) = false) →
    (eraseKey k l |> minKey <| he) =
      minKey l (isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he) :=
  minKey_eraseKey_eq_iff_beq_minKey_eq_false hd |>.mpr

theorem minKey_le_minKey_erase [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    compare (minKey l <| isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he)
      (eraseKey k l |> minKey <| he) |>.isLE :=
  minKey?_le_minKey?_eraseKey hd minKey?_eq_some_minKey minKey_eq_get_minKey?.symm

theorem minKey_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    (insertEntryIfNew k v l |> minKey <| isEmpty_insertEntryIfNew) =
      (minKey? l).elim k fun k' => if compare k k' = .lt then k else k' := by
  simp [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some, ← minKey?_insertEntryIfNew hd (v := v)]

theorem minKey_insertEntryIfNew_le_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v he} :
    compare (insertEntryIfNew k v l |> minKey <| isEmpty_insertEntryIfNew)
      (minKey l he) |>.isLE :=
  minKey?_insertEntryIfNew_le_minKey? hd minKey?_eq_some_minKey minKey_eq_get_minKey?.symm

theorem minKey_insertEntryIfNew_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare (insertEntryIfNew k v l  |> minKey <| isEmpty_insertEntryIfNew) k |>.isLE :=
  minKey?_insertEntryIfNew_le_self hd minKey_eq_get_minKey?.symm

theorem minKey_eq_head_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) {he} :
    minKey l he = (keys l).head (by simp_all [keys_eq_map, List.isEmpty_eq_false_iff]) := by
  simp [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some, ← List.head?_eq_head,
    minKey?_eq_head?_keys ho]

theorem minKey_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α] {k f}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    (modifyKey k f l |> minKey <| he) = minKey l (isEmpty_modifyKey k f l ▸ he):= by
  simp [minKey_eq_get_minKey?, minKey?_modifyKey hd]

theorem minKey_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f he} :
    (alterKey k f l |> minKey <| he) = k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simp [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some, minKey?_alterKey_eq_self hd]

namespace Const

variable {β : Type v}

theorem minKey_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (modifyKey k f l |> minKey <| he) =
      if (minKey l <| isEmpty_modifyKey k f l ▸ he) == k then
        k
      else
        (minKey l <| isEmpty_modifyKey k f l ▸ he) := by
  simp [minKey_eq_get_minKey?, minKey?_modifyKey hd, Option.get_map]

theorem minKey_modifyKey_eq_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (modifyKey k f l |> minKey <| he) = minKey l (isEmpty_modifyKey k f l ▸ he) := by
  simp [minKey_eq_get_minKey?, minKey?_modifyKey_eq_minKey? hd]

theorem minKey_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (modifyKey k f l |> minKey <| he) == (minKey l <| isEmpty_modifyKey k f l ▸ he) :=
  minKey?_modifyKey_beq hd minKey?_eq_some_minKey rfl

theorem minKey_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (alterKey k f l |> minKey <| he) = k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simp [minKey_eq_get_minKey?, Option.get_eq_iff_eq_some, minKey?_alterKey_eq_self hd]

end Const

/-- Returns the smallest key in an associative list or panics if the list is empty. -/
def minKey! [Ord α] [Inhabited α] (xs : List ((a : α) × β a)) : α :=
  minKey? xs |>.get!

theorem minKey!_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l l' : List ((a : α) × β a)} (hd : DistinctKeys l) (hp : l.Perm l') :
    minKey! l = minKey! l' := by
  simp [minKey!, minKey?_of_perm hd hp]

theorem minKey!_eq_get!_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} :
    minKey! l = (minKey? l).get! :=
  rfl

theorem minKey_eq_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} {he} :
    minKey l he = minKey! l := by
  simp [minKey_eq_get_minKey?, minKey!_eq_get!_minKey?, Option.get_eq_get!]

theorem minKey?_eq_some_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (he : l.isEmpty = false) :
    minKey? l = some (minKey! l) := by
  simp [← minKey_eq_minKey! (he := he), minKey_eq_get_minKey?]

theorem minKey!_eq_default [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (h : l.isEmpty) :
    minKey! l = default := by
  simp [minKey!, minKey?_eq_none_iff_isEmpty.mpr h]

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {km} :
    minKey! l = km ↔ getKey? km l = some km ∧ ∀ k, containsKey k l → (compare km k).isLE := by
  simpa [minKey_eq_minKey!] using minKey_eq_iff_getKey?_eq_self_and_forall hd (he := he)

theorem minKey!_eq_iff_mem_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (he : l.isEmpty = false) {km} :
    minKey! l = km ↔ containsKey km l ∧ ∀ k, containsKey k l → (compare km k).isLE := by
  simpa [minKey_eq_minKey!] using minKey_eq_iff_mem_and_forall hd (he := he)

theorem minKey!_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    (insertEntry k v l |> minKey!) =
      ((minKey? l).elim k fun k' => if compare k k' |>.isLE then k else k') := by
  simpa [minKey_eq_minKey!] using minKey_insertEntry hd

theorem minKey!_insertEntry_le_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v} :
    compare (insertEntry k v l |> minKey!) (minKey! l) |>.isLE := by
  simpa [minKey_eq_minKey!] using minKey_insertEntry_le_minKey hd (he := he)

theorem minKey!_insertEntry_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare (insertEntry k v l |> minKey!) k |>.isLE := by
  simpa [minKey_eq_minKey!] using minKey_insertEntry_le_self hd

theorem containsKey_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) :
    containsKey (minKey! l) l := by
  simpa [minKey_eq_minKey!] using containsKey_minKey hd (he := he)

theorem minKey!_le_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (hc : containsKey k l) :
    compare (minKey! l) k |>.isLE := by
   simpa [minKey_eq_minKey!] using minKey_le_of_containsKey hd hc

theorem le_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k} :
    (compare k (minKey! l)).isLE ↔ (∀ k', containsKey k' l → (compare k k').isLE) := by
  simpa [minKey_eq_minKey!] using le_minKey hd (he := he)

theorem getKey?_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) :
    getKey? (minKey! l) l = some (minKey! l) := by
  simpa [minKey_eq_minKey!] using getKey?_minKey hd (he := he)

theorem getKey_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey (minKey! l) l he = minKey! l := by
  simpa [minKey_eq_minKey!] using getKey_minKey hd (he := isEmpty_eq_false_of_containsKey he)

theorem getKey_minKey!_eq_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey (minKey! l) l he = minKey l (isEmpty_eq_false_of_containsKey he) := by
  simpa [minKey_eq_minKey!] using getKey_minKey hd (he := isEmpty_eq_false_of_containsKey he)

theorem getKey!_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) :
    getKey! (minKey! l) l = minKey! l := by
  simpa [minKey_eq_minKey!] using getKey!_minKey hd (he := he)

theorem getKeyD_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    getKeyD (minKey! l) l fallback = minKey! l := by
  simpa [minKey_eq_minKey!] using getKeyD_minKey hd (he := he)

theorem minKey!_eraseKey_eq_iff_beq_minKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> minKey!) = minKey! l ↔ (k == (minKey! l)) = false := by
  simpa [minKey_eq_minKey!] using minKey_eraseKey_eq_iff_beq_minKey_eq_false hd (he := he)

theorem minKey!_eraseKey_eq_iff_beq_minKey!_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> minKey!) = minKey! l ↔ (k == (minKey! l)) = false := by
  simpa [minKey_eq_minKey!] using minKey_eraseKey_eq_iff_beq_minKey_eq_false hd (he := he)

theorem minKey!_eraseKey_eq_of_beq_minKey!_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k}
    (he : (eraseKey k l).isEmpty = false) : (heq : (k == minKey! l) = false) →
    (eraseKey k l |> minKey!) = minKey! l := by
  simpa only [minKey_eq_minKey!] using minKey_eraseKey_eq_of_beq_minKey_eq_false hd (he := he)

theorem minKey!_le_minKey!_erase [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (he : (eraseKey k l).isEmpty = false) :
    compare (minKey! l) (eraseKey k l |> minKey!) |>.isLE := by
  simpa only [minKey_eq_minKey!] using minKey_le_minKey_erase hd (he := he)

theorem minKey!_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    (insertEntryIfNew k v l |> minKey!) =
      (minKey? l).elim k fun k' => if compare k k' = .lt then k else k' := by
  simpa only [minKey_eq_minKey!] using minKey_insertEntryIfNew hd

theorem minKey!_insertEntryIfNew_le_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v} :
    compare (insertEntryIfNew k v l |> minKey!) (minKey! l) |>.isLE := by
  simpa only [minKey_eq_minKey!] using minKey_insertEntryIfNew_le_minKey hd (he := he)

theorem minKey!_insertEntryIfNew_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare (insertEntryIfNew k v l |> minKey!) k |>.isLE := by
  simpa only [minKey_eq_minKey!] using minKey_insertEntryIfNew_le_self hd

theorem minKey!_eq_head!_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) :
    minKey! l = (keys l).head! := by
  cases l
  · rfl
  · simp only [minKey!_eq_get!_minKey?, minKey?_eq_head?_keys ho]
    rfl

theorem minKey!_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f} :
    (modifyKey k f l |> minKey!) = minKey! l := by
  cases he : l.isEmpty
  · have := minKey_modifyKey hd (he := isEmpty_modifyKey k f l ▸ he)
    -- fails after inlining `this`
    simpa [minKey_eq_minKey!] using this
  · simp_all [modifyKey]

theorem minKey!_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f}
    (he : (alterKey k f l).isEmpty = false) :
    (alterKey k f l |> minKey!) = k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simpa only [minKey_eq_minKey!] using minKey_alterKey_eq_self hd (he := he)

namespace Const

variable {β : Type v}

theorem minKey!_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (modifyKey k f l).isEmpty = false) :
    (modifyKey k f l |> minKey!) = if (minKey! l) == k then k else (minKey! l) := by
  simpa only [minKey_eq_minKey!] using minKey_modifyKey hd (he := he)

theorem minKey!_modifyKey_eq_minKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    [Inhabited α] {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} :
    (modifyKey k f l |> minKey!) = minKey! l := by
  cases he : l.isEmpty
  · have := minKey_modifyKey_eq_minKey hd (he := isEmpty_modifyKey k f l ▸ he)
    -- fails after inlining `this`
    simpa [minKey_eq_minKey!] using this
  · simp_all [modifyKey]

theorem minKey!_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} :
    (modifyKey k f l |> minKey!) == (minKey! l) := by
  cases he : l.isEmpty
  · have := minKey_modifyKey_beq hd (he := isEmpty_modifyKey k f l ▸ he)
    -- fails after inlining `this`
    simpa [minKey_eq_minKey!] using this
  · simp_all [modifyKey]

theorem minKey!_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (alterKey k f l).isEmpty = false) :
    (alterKey k f l |> minKey!) = k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simpa only [minKey_eq_minKey!] using minKey_alterKey_eq_self hd (he := he)

end Const

/-- Returns the smallest key in an associative list or `fallback` if the list is empty. -/
def minKeyD [Ord α] (xs : List ((a : α) × β a)) (fallback : α) : α :=
  minKey? xs |>.getD fallback

theorem minKeyD_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l l' : List ((a : α) × β a)} {fallback} (hd : DistinctKeys l) (hp : l.Perm l') :
    minKeyD l fallback = minKeyD l' fallback := by
  simp [minKeyD, minKey?_of_perm hd hp]

theorem minKeyD_eq_getD_minKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {fallback} :
    minKeyD l fallback = (minKey? l).getD fallback :=
  rfl

theorem minKey_eq_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {he fallback} :
    minKey l he = minKeyD l fallback := by
  simp [minKey_eq_get_minKey?, minKeyD_eq_getD_minKey?, Option.get_eq_getD (fallback := fallback)]

theorem minKey?_eq_some_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {fallback} (he : l.isEmpty = false) :
    minKey? l = some (minKeyD l fallback) := by
  simp [← minKey_eq_minKeyD (he := he), minKey_eq_get_minKey?]

theorem minKey!_eq_minKeyD_default [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} :
    minKey! l = minKeyD l default := by
  simp [minKey!_eq_get!_minKey?, minKeyD_eq_getD_minKey?, Option.get!_eq_getD]

theorem minKeyD_eq_fallback [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {fallback} (h : l.isEmpty) :
    minKeyD l fallback = fallback := by
  simp [minKeyD, minKey?_eq_none_iff_isEmpty.mpr h]

theorem minKeyD_eq_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {km fallback} :
    minKeyD l fallback = km ↔
      getKey? km l = some km ∧ ∀ k, containsKey k l → (compare km k).isLE := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using
    minKey_eq_iff_getKey?_eq_self_and_forall hd (he := he)

theorem minKeyD_eq_iff_mem_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (he : l.isEmpty = false) {km fallback} :
    minKeyD l fallback = km ↔ containsKey km l ∧ ∀ k, containsKey k l → (compare km k).isLE := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using
    minKey_eq_iff_mem_and_forall hd (he := he)

theorem minKeyD_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    (insertEntry k v l |> minKeyD <| fallback) =
      ((minKey? l).elim k fun k' => if compare k k' |>.isLE then k else k') := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using minKey_insertEntry hd

theorem minKeyD_insertEntry_le_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v fallback} :
    compare (insertEntry k v l |> minKeyD <| fallback) (minKeyD l fallback) |>.isLE := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using minKey_insertEntry_le_minKey hd (he := he)

theorem minKeyD_insertEntry_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    compare (insertEntry k v l |> minKeyD <| fallback) k |>.isLE := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using minKey_insertEntry_le_self hd

theorem containsKey_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    containsKey (minKeyD l fallback) l := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using containsKey_minKey hd (he := he)

theorem minKeyD_le_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (hc : containsKey k l) {fallback} :
    compare (minKeyD l fallback) k |>.isLE := by
   simpa [minKey_eq_minKeyD (fallback := fallback)] using minKey_le_of_containsKey hd hc

theorem le_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k fallback} :
    (compare k (minKeyD l fallback)).isLE ↔ (∀ k', containsKey k' l → (compare k k').isLE) := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using le_minKey hd (he := he)

theorem getKey?_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    getKey? (minKeyD l fallback) l = some (minKeyD l fallback) := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using getKey?_minKey hd (he := he)

theorem getKey_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {fallback he} :
    getKey (minKeyD l fallback) l he = minKeyD l fallback := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using
    getKey_minKey hd (he := isEmpty_eq_false_of_containsKey he)

theorem getKey_minKeyD_eq_minKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {fallback he} :
    getKey (minKeyD l fallback) l he = minKey l (isEmpty_eq_false_of_containsKey he) := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using
    getKey_minKey hd (he := isEmpty_eq_false_of_containsKey he)

theorem getKey!_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    getKey! (minKeyD l fallback) l = minKeyD l fallback := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using getKey!_minKey hd (he := he)

theorem getKeyD_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback fallback'} :
    getKeyD (minKeyD l fallback) l fallback' = minKeyD l fallback := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using getKeyD_minKey hd (he := he)

theorem minKeyD_eraseKey_eq_iff_beq_minKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k fallback}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> minKeyD <| fallback) = minKeyD l fallback ↔
      (k == (minKeyD l fallback)) = false := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using
    minKey_eraseKey_eq_iff_beq_minKey_eq_false hd (he := he)

theorem minKeyD_eraseKey_eq_iff_beq_minKeyD_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k fallback}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> minKeyD <| fallback) = minKeyD l fallback ↔
      (k == (minKeyD l fallback)) = false := by
  simpa [minKey_eq_minKeyD (fallback := fallback)] using
    minKey_eraseKey_eq_iff_beq_minKey_eq_false hd (he := he)

theorem minKeyD_eraseKey_eq_of_beq_minKeyD_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k fallback}
    (he : (eraseKey k l).isEmpty = false) : (heq : (k == minKeyD l fallback) = false) →
    (eraseKey k l |> minKeyD <| fallback) = minKeyD l fallback:= by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using
    minKey_eraseKey_eq_of_beq_minKey_eq_false hd (he := he)

theorem minKeyD_le_minKeyD_erase [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (he : (eraseKey k l).isEmpty = false)
    {fallback} :
    compare (minKeyD l fallback) (eraseKey k l |> minKeyD <| fallback) |>.isLE := by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using
    minKey_le_minKey_erase hd (he := he)

theorem minKeyD_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    (insertEntryIfNew k v l |> minKeyD <| fallback) =
      (minKey? l).elim k fun k' => if compare k k' = .lt then k else k' := by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using minKey_insertEntryIfNew hd

theorem minKeyD_insertEntryIfNew_le_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v fallback} :
    compare (insertEntryIfNew k v l |> minKeyD <| fallback) (minKeyD l fallback) |>.isLE := by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using
    minKey_insertEntryIfNew_le_minKey hd (he := he)

theorem minKeyD_insertEntryIfNew_le_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    compare (insertEntryIfNew k v l |> minKeyD <| fallback) k |>.isLE := by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using minKey_insertEntryIfNew_le_self hd

theorem minKeyD_eq_headD_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) {fallback} :
    minKeyD l fallback = (keys l).headD fallback := by
  simp [minKeyD_eq_getD_minKey?, minKey?_eq_head?_keys ho]

theorem minKeyD_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f fallback} :
    (modifyKey k f l |> minKeyD <| fallback) = minKeyD l fallback := by
  cases he : l.isEmpty
  · have := minKey_modifyKey hd (he := isEmpty_modifyKey k f l ▸ he)
    -- fails after inlining `this`
    simpa [minKey_eq_minKeyD (fallback := fallback)] using this
  · simp_all [modifyKey]

theorem minKeyD_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f fallback}
    (he : (alterKey k f l).isEmpty = false) :
    (alterKey k f l |> minKeyD <| fallback) = k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using minKey_alterKey_eq_self hd (he := he)

namespace Const

variable {β : Type v}

theorem minKeyD_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (modifyKey k f l).isEmpty = false)
    {fallback} :
    (modifyKey k f l |> minKeyD <| fallback) = if (minKeyD l fallback) == k then k else (minKeyD l fallback) := by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using minKey_modifyKey hd (he := he)

theorem minKeyD_modifyKey_eq_minKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f fallback} :
    (modifyKey k f l |> minKeyD <| fallback) = minKeyD l fallback := by
  cases he : l.isEmpty
  · have := minKey_modifyKey_eq_minKey hd (he := isEmpty_modifyKey k f l ▸ he)
    -- fails after inlining `this`
    simpa [minKey_eq_minKeyD (fallback := fallback)] using this
  · simp_all [modifyKey]

theorem minKeyD_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f fallback} :
    (modifyKey k f l |> minKeyD <| fallback) == (minKeyD l fallback) := by
  cases he : l.isEmpty
  · have := minKey_modifyKey_beq hd (he := isEmpty_modifyKey k f l ▸ he)
    -- fails after inlining `this`
    simpa [minKey_eq_minKeyD (fallback := fallback)] using this
  · simp_all [modifyKey]

theorem minKeyD_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (alterKey k f l).isEmpty = false)
    {fallback} :
    (alterKey k f l |> minKeyD <| fallback) = k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k k').isLE := by
  simpa only [minKey_eq_minKeyD (fallback := fallback)] using minKey_alterKey_eq_self hd (he := he)

end Const

end Min

section Max

/-- Returns the largest key in an associative list. -/
abbrev maxKey? [Ord α] (xs : List ((a : α) × β a)) : Option α :=
  letI : Ord α := .opposite inferInstance
  minKey? xs

theorem maxKey?_eq_some_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? l = some k ↔ getKey? k l = some k ∧ ∀ k' : α, containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey?_eq_some_iff_getKey?_eq_self_and_forall hd

theorem maxKey?_eq_some_iff_mem_and_forall [Ord α] [LawfulEqOrd α] [TransOrd α] [BEq α]
    [LawfulBEqOrd α] {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? l = some k ↔ containsKey k l ∧ ∀ k' : α, containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey?_eq_some_iff_mem_and_forall hd

theorem maxKey?_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l l' : List ((a : α) × β a)}
    (hl : DistinctKeys l) (hp : l.Perm l') :
    maxKey? l = maxKey? l' :=
  letI : Ord α := .opposite inferInstance
  minKey?_of_perm hl hp

theorem maxKey?_eq_none_iff_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    maxKey? l = none ↔ l.isEmpty :=
  letI : Ord α := .opposite inferInstance
  minKey?_eq_none_iff_isEmpty

theorem maxKey?_of_isEmpty [Ord α] [TransOrd α] {l : List ((a : α) × β a)} (he : l.isEmpty) :
    maxKey? l = none :=
  letI : Ord α := .opposite inferInstance
  minKey?_of_isEmpty he

theorem isNone_maxKey?_eq_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    (maxKey? l).isNone = l.isEmpty :=
  letI : Ord α := .opposite inferInstance
  isNone_minKey?_eq_isEmpty

theorem isSome_maxKey?_eq_not_isEmpty [Ord α] {l : List ((a : α) × β a)} :
    (maxKey? l).isSome = !l.isEmpty :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_eq_not_isEmpty

theorem isSome_maxKey?_iff_isEmpty_eq_false [Ord α] {l : List ((a : α) × β a)} :
    (maxKey? l).isSome ↔ l.isEmpty = false :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_iff_isEmpty_eq_false

theorem maxKey?_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? (insertEntry k v l) =
      some ((maxKey? l).elim k fun k' => if compare k' k |>.isLE then k else k') :=
  letI : Ord α := .opposite inferInstance
  minKey?_insertEntry hd

theorem isSome_maxKey?_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? (insertEntry k v l) |>.isSome :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_insertEntry hd

theorem isSome_maxKey?_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k}
    {l : List ((a : α) × β a)} (hc : containsKey k l) :
    maxKey? l |>.isSome :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_of_containsKey hc

theorem getKey?_maxKey? [Ord α] [TransOrd α] [BEq α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km} (hkm : maxKey? l = some km) :
    getKey? km l = some km :=
  letI : Ord α := .opposite inferInstance
  getKey?_minKey? hd hkm

theorem getKey_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km hc} :
    (hkm : (maxKey? l |>.get <| isSome_maxKey?_of_containsKey hc) = km) → getKey km l hc = km :=
  letI : Ord α := .opposite inferInstance
  getKey_minKey? hd

theorem getKey!_maxKey? [Ord α] [TransOrd α] [Inhabited α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km} :
    (hkm : maxKey? l = some km) → getKey! km l = km :=
  letI : Ord α := .opposite inferInstance
  getKey!_minKey? hd

theorem getKeyD_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km fallback} :
    (hkm : maxKey? l = some km) → getKeyD km l fallback = km :=
  letI : Ord α := .opposite inferInstance
  getKeyD_minKey? hd

theorem maxKey?_bind_getKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    (maxKey? l |>.bind fun k => getKey? k l) = maxKey? l :=
  letI : Ord α := .opposite inferInstance
  minKey?_bind_getKey? hd

theorem containsKey_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l : List ((a : α) × β a)}
    (hd : DistinctKeys l) {km} (hkm : maxKey? l = some km) :
    containsKey km l :=
  letI : Ord α := .opposite inferInstance
  containsKey_minKey? hd hkm

theorem maxKey?_eraseKey_eq_iff_beq_maxKey?_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? (eraseKey k l) = maxKey? l ↔ ∀ {km}, maxKey? l = some km → (k == km) = false :=
  letI : Ord α := .opposite inferInstance
  minKey?_eraseKey_eq_iff_beq_minKey?_eq_false hd

theorem maxKey?_eraseKey_eq_of_beq_maxKey?_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k} {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (hc : ∀ {km}, maxKey? l = some km → (k == km) = false) :
    maxKey? (eraseKey k l) = maxKey? l :=
  letI : Ord α := .opposite inferInstance
  minKey?_eraseKey_eq_of_beq_minKey?_eq_false hd hc

theorem maxKey?_le_maxKey?_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km kmi} (hkm : maxKey? l = some km)
    (hkmi : (insertEntry k v l |> maxKey? |>.get <| isSome_maxKey?_insertEntry hd) = kmi) :
    compare km kmi |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey?_insertEntry_le_minKey? hd hkm hkmi

theorem self_le_maxKey?_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) {kmi}
    (hkmi : (insertEntry k v l |> maxKey? |>.get <| isSome_maxKey?_insertEntry hd) = kmi) :
    compare k kmi |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey?_insertEntry_le_self hd hkmi

theorem maxKey?_le_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k km}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (hc : containsKey k l)
    (hkm : (maxKey? l |>.get <| isSome_maxKey?_of_containsKey hc) = km) :
    compare k km |>.isLE :=
  letI : Ord α := .opposite inferInstance
  (minKey?_le_of_containsKey hd hc hkm :)

theorem maxKey?_le [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k} {l : List ((a : α) × β a)}
    (hd : DistinctKeys l) :
    (∀ k', maxKey? l = some k' → (compare k' k).isLE) ↔
      (∀ k', containsKey k' l → (compare k' k).isLE) :=
  letI : Ord α := .opposite inferInstance
  le_minKey? hd

theorem isSome_maxKey?_of_isSome_maxKey?_eraseKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k}
    {l : List ((a : α) × β a)} (hs : eraseKey k l |> maxKey? |>.isSome) :
    maxKey? l |>.isSome :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_of_isSome_minKey?_eraseKey hs

theorem containsKey_maxKey?_eraseKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {kme}
    (hkme : (eraseKey k l |> maxKey?) = some kme) :
    containsKey kme l := by
  apply containsKey_of_containsKey_eraseKey hd
  apply containsKey_maxKey? hd.eraseKey hkme

theorem maxKey?_eraseKey_le_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k km kme}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (hkme : (eraseKey k l |> maxKey?) = some kme)
    (hkm : (maxKey? l |>.get <|
      isSome_maxKey?_of_isSome_maxKey?_eraseKey <| hkme ▸ Option.isSome_some) = km) :
    compare kme km |>.isLE :=
  letI : Ord α := .opposite inferInstance
  (minKey?_le_minKey?_eraseKey hd hkme hkm :)

theorem maxKey?_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α} {v : β k}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? (insertEntryIfNew k v l) =
      some ((maxKey? l).elim k fun k' => if compare k' k = .lt then k else k') :=
  letI : Ord α := .opposite inferInstance
  minKey?_insertEntryIfNew hd

theorem isSome_maxKey?_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? (insertEntryIfNew k v l) |>.isSome :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_insertEntryIfNew hd

theorem maxKey?_le_maxKey?_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k : α}
    {v : β k} {l : List ((a : α) × β a)} (hd : DistinctKeys l) {km kmi} (hkm : maxKey? l = some km)
    (hkmi : (insertEntryIfNew k v l |> maxKey? |>.get <| isSome_maxKey?_insertEntryIfNew hd) = kmi) :
    compare km kmi |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey?_insertEntryIfNew_le_minKey? hd hkm hkmi

theorem self_le_maxKey?_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k kmi : α}
    {v : β k} {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (hkmi : (insertEntryIfNew k v l |> maxKey? |>.get <| isSome_maxKey?_insertEntryIfNew hd) = kmi) :
    compare k kmi |>.isLE :=
  letI : Ord α := .opposite inferInstance
  (minKey?_insertEntryIfNew_le_self hd hkmi :)

theorem reverse_keys {l : List ((a : α) × β a)} :
    (keys l).reverse = keys l.reverse := by
  simp [keys_eq_map]

theorem maxKey?_eq_getLast?_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) :
    maxKey? l = (keys l).getLast? := by
  rw [← List.head?_reverse, reverse_keys, maxKey?_of_perm hd (List.reverse_perm l).symm]
  letI : Ord α := .opposite inferInstance
  exact minKey?_eq_head?_keys (List.pairwise_reverse.mpr ho)

theorem maxKey?_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α] {k f}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? (modifyKey k f l) = maxKey? l :=
  letI : Ord α := .opposite inferInstance
  minKey?_modifyKey hd

theorem maxKey?_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {k f} {l : List ((a : α) × β a)} (hd : DistinctKeys l) :
    maxKey? (alterKey k f l) = some k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey?_alterKey_eq_self hd

namespace Const

variable {β : Type v}

theorem maxKey?_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f}
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) :
    maxKey? (modifyKey k f l) = (maxKey? l).map fun km => if km == k then k else km :=
  letI : Ord α := .opposite inferInstance
  minKey?_modifyKey hd

theorem maxKey?_modifyKey_eq_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {k f} {l : List ((_ : α) × β)} (hd : DistinctKeys l) :
    maxKey? (modifyKey k f l) = maxKey? l :=
  letI : Ord α := .opposite inferInstance
  minKey?_modifyKey_eq_minKey? hd

theorem isSome_maxKey?_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f}
    {l : List ((_ : α) × β)} :
    (modifyKey k f l |> maxKey?).isSome = !l.isEmpty :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_modifyKey

theorem isSome_maxKey?_modifyKey_eq_isSome [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f}
    {l : List ((_ : α) × β)} :
    (modifyKey k f l |> maxKey?).isSome = (maxKey? l).isSome :=
  letI : Ord α := .opposite inferInstance
  isSome_minKey?_modifyKey_eq_isSome

theorem maxKey?_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {k f km kmm}
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) (hkm : maxKey? l = some km)
    (hkmm : (modifyKey k f l |> maxKey? |>.get <|
        isSome_maxKey?_modifyKey_eq_isSome.trans <| hkm ▸ Option.isSome_some) = kmm) :
    kmm == km :=
  letI : Ord α := .opposite inferInstance
  minKey?_modifyKey_beq hd hkm hkmm

theorem maxKey?_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {k f} {l : List ((_ : α) × β)} (hd : DistinctKeys l) :
    maxKey? (alterKey k f l) = some k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey?_alterKey_eq_self hd

end Const

/-- Given a proof that the list is nonempty, returns the largest key in an associative list. -/
abbrev maxKey [Ord α] (xs : List ((a : α) × β a)) (h : xs.isEmpty = false) : α :=
  letI : Ord α := .opposite inferInstance; minKey xs h

theorem maxKey_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l l' : List ((a : α) × β a)}
    {hl} (hd : DistinctKeys l) (hp : l.Perm l') :
    maxKey l hl = maxKey l' (hp.isEmpty_eq ▸ hl) :=
  letI : Ord α := .opposite inferInstance
  minKey_of_perm hd hp

theorem maxKey_eq_get_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {he} :
    maxKey l he = (maxKey? l |>.get (by simp [isSome_maxKey?_eq_not_isEmpty, he])) :=
  rfl

theorem maxKey?_eq_some_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {he} :
    maxKey? l = some (maxKey l he) :=
  letI : Ord α := .opposite inferInstance
  minKey?_eq_some_minKey

theorem maxKey_eq_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he km} :
    maxKey l he = km ↔ getKey? km l = some km ∧ ∀ k, containsKey k l → (compare k km).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_eq_iff_getKey?_eq_self_and_forall hd

theorem maxKey_eq_iff_mem_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he km} :
    maxKey l he = km ↔ containsKey km l ∧ ∀ k, containsKey k l → (compare k km).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_eq_iff_mem_and_forall hd

theorem maxKey_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] {l : List ((a : α) × β a)}
    (hd : DistinctKeys l) {k v} :
    (insertEntry k v l |> maxKey <| isEmpty_insertEntry) =
      ((maxKey? l).elim k fun k' => if compare k' k |>.isLE then k else k') :=
  letI : Ord α := .opposite inferInstance
  minKey_insertEntry hd

theorem maxKey_le_maxKey_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v he} :
    compare (maxKey l he) (insertEntry k v l |> maxKey <| isEmpty_insertEntry) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_insertEntry_le_minKey hd

theorem self_le_maxKey_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare k (insertEntry k v l |> maxKey <| isEmpty_insertEntry) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_insertEntry_le_self hd

theorem containsKey_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    containsKey (maxKey l he) l :=
  letI : Ord α := .opposite inferInstance
  containsKey_minKey hd

theorem le_maxKey_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (hc : containsKey k l) :
    compare k (maxKey l <| isEmpty_eq_false_iff_exists_containsKey.mpr ⟨k, hc⟩) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_le_of_containsKey hd hc

theorem maxKey_le [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    (compare (maxKey l he) k).isLE ↔ (∀ k', containsKey k' l → (compare k' k).isLE) :=
  letI : Ord α := .opposite inferInstance
  le_minKey hd

theorem getKey?_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey? (maxKey l he) l = some (maxKey l he) :=
  letI : Ord α := .opposite inferInstance
  getKey?_minKey hd

theorem getKey_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey (maxKey l he) l (containsKey_maxKey hd) = maxKey l he :=
  letI : Ord α := .opposite inferInstance
  getKey_minKey hd

theorem getKey!_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey! (maxKey l he) l = maxKey l he :=
  letI : Ord α := .opposite inferInstance
  getKey!_minKey hd

theorem getKeyD_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he fallback} :
    getKeyD (maxKey l he) l fallback = maxKey l he :=
  letI : Ord α := .opposite inferInstance
  getKeyD_minKey hd

theorem maxKey_eraseKey_eq_iff_beq_maxKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    (eraseKey k l |> maxKey <| he) =
        maxKey l (isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he) ↔
      (k == (maxKey l <| isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he)) = false :=
  letI : Ord α := .opposite inferInstance
  minKey_eraseKey_eq_iff_beq_minKey_eq_false hd

theorem maxKey_eraseKey_eq_of_beq_maxKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    (hc : (k == (maxKey l (isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he))) = false) →
    (eraseKey k l |> maxKey <| he) =
      maxKey l (isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he) :=
  letI : Ord α := .opposite inferInstance
  minKey_eraseKey_eq_of_beq_minKey_eq_false hd

theorem maxKey_eraseKey_le_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k he} :
    compare (eraseKey k l |> maxKey <| he)
      (maxKey l <| isEmpty_eq_false_of_isEmpty_eraseKey_eq_false hd he) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_le_minKey_erase hd

theorem maxKey_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    (insertEntryIfNew k v l |> maxKey <| isEmpty_insertEntryIfNew) =
      (maxKey? l).elim k fun k' => if compare k' k = .lt then k else k' :=
  letI : Ord α := .opposite inferInstance
  minKey_insertEntryIfNew hd

theorem maxKey_le_maxKey_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v he} :
    compare (maxKey l he)
      (insertEntryIfNew k v l |> maxKey <| isEmpty_insertEntryIfNew) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_insertEntryIfNew_le_minKey hd

theorem self_le_maxKey_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare k (insertEntryIfNew k v l  |> maxKey <| isEmpty_insertEntryIfNew) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_insertEntryIfNew_le_self hd

theorem maxKey_eq_getLast_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) {he} :
    maxKey l he = (keys l).getLast (by simp_all [keys_eq_map, List.isEmpty_eq_false_iff]) := by
  simp only [List.getLast_eq_head_reverse, reverse_keys, maxKey_of_perm hd (List.reverse_perm l).symm]
  letI : Ord α := .opposite inferInstance
  exact minKey_eq_head_keys (List.pairwise_reverse.mpr ho)

theorem maxKey_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α] {k f}
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    (modifyKey k f l |> maxKey <| he) = maxKey l (isEmpty_modifyKey k f l ▸ he):=
  letI : Ord α := .opposite inferInstance
  minKey_modifyKey hd

theorem maxKey_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f he} :
    (alterKey k f l |> maxKey <| he) = k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_alterKey_eq_self hd

namespace Const

variable {β : Type v}

theorem maxKey_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (modifyKey k f l |> maxKey <| he) =
      if (maxKey l <| isEmpty_modifyKey k f l ▸ he) == k then
        k
      else
        (maxKey l <| isEmpty_modifyKey k f l ▸ he) :=
  letI : Ord α := .opposite inferInstance
  minKey_modifyKey hd

theorem maxKey_modifyKey_eq_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (modifyKey k f l |> maxKey <| he) = maxKey l (isEmpty_modifyKey k f l ▸ he) :=
  letI : Ord α := .opposite inferInstance
  minKey_modifyKey_eq_minKey hd

theorem maxKey_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (modifyKey k f l |> maxKey <| he) == (maxKey l <| isEmpty_modifyKey k f l ▸ he) :=
  letI : Ord α := .opposite inferInstance
  minKey_modifyKey_beq hd

theorem maxKey_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f he} :
    (alterKey k f l |> maxKey <| he) = k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey_alterKey_eq_self hd

end Const

/-- Given a proof that the list is nonempty, returns the smallest key in an associative list. -/
def maxKey! [Ord α] [Inhabited α] (xs : List ((a : α) × β a)) : α :=
  maxKey? xs |>.get!

theorem maxKey!_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l l' : List ((a : α) × β a)} (hd : DistinctKeys l) (hp : l.Perm l') :
    maxKey! l = maxKey! l' :=
  letI : Ord α := .opposite inferInstance
  minKey!_of_perm hd hp

theorem maxKey!_eq_get!_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} :
    maxKey! l = (maxKey? l).get! :=
  letI : Ord α := .opposite inferInstance
  minKey!_eq_get!_minKey?

theorem maxKey_eq_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} {he} :
    maxKey l he = maxKey! l :=
  letI : Ord α := .opposite inferInstance
  minKey_eq_minKey!

theorem maxKey?_eq_some_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (he : l.isEmpty = false) :
    maxKey? l = some (maxKey! l) :=
  letI : Ord α := .opposite inferInstance
  minKey?_eq_some_minKey! he

theorem maxKey!_eq_default [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (h : l.isEmpty) :
    maxKey! l = default :=
  letI : Ord α := .opposite inferInstance
  minKey!_eq_default h

theorem maxKey!_eq_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {km} :
    maxKey! l = km ↔ getKey? km l = some km ∧ ∀ k, containsKey k l → (compare k km).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_eq_iff_getKey?_eq_self_and_forall hd he

theorem maxKey!_eq_iff_mem_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (he : l.isEmpty = false) {km} :
    maxKey! l = km ↔ containsKey km l ∧ ∀ k, containsKey k l → (compare k km).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_eq_iff_mem_and_forall hd he

theorem maxKey!_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    (insertEntry k v l |> maxKey!) =
      ((maxKey? l).elim k fun k' => if compare k' k |>.isLE then k else k') :=
  letI : Ord α := .opposite inferInstance
  minKey!_insertEntry hd

theorem maxKey!_le_maxKey!_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v} :
    compare (maxKey! l) (insertEntry k v l |> maxKey!) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_insertEntry_le_minKey! hd he

theorem self_le_maxKey!_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare k (insertEntry k v l |> maxKey!) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_insertEntry_le_self hd

theorem containsKey_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) :
    containsKey (maxKey! l) l :=
  letI : Ord α := .opposite inferInstance
  containsKey_minKey! hd he

theorem le_maxKey!_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (hc : containsKey k l) :
    compare k (maxKey! l) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_le_of_containsKey hd hc

theorem maxKey!_le [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k} :
    (compare (maxKey! l) k).isLE ↔ (∀ k', containsKey k' l → (compare k' k).isLE) :=
  letI : Ord α := .opposite inferInstance
  le_minKey! hd he

theorem getKey?_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) :
    getKey? (maxKey! l) l = some (maxKey! l) :=
  letI : Ord α := .opposite inferInstance
  getKey?_minKey! hd he

theorem getKey_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey (maxKey! l) l he = maxKey! l :=
  letI : Ord α := .opposite inferInstance
  getKey_minKey! hd

theorem getKey_maxKey!_eq_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {he} :
    getKey (maxKey! l) l he = maxKey l (isEmpty_eq_false_of_containsKey he) :=
  letI : Ord α := .opposite inferInstance
  getKey_minKey!_eq_minKey hd

theorem getKey!_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) :
    getKey! (maxKey! l) l = maxKey! l :=
  letI : Ord α := .opposite inferInstance
  getKey!_minKey! hd he

theorem getKeyD_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    getKeyD (maxKey! l) l fallback = maxKey! l :=
  letI : Ord α := .opposite inferInstance
  getKeyD_minKey! hd he

theorem maxKey!_eraseKey_eq_iff_beq_maxKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> maxKey!) = maxKey! l ↔ (k == (maxKey! l)) = false :=
  letI : Ord α := .opposite inferInstance
  minKey!_eraseKey_eq_iff_beq_minKey_eq_false hd he

theorem maxKey!_eraseKey_eq_iff_beq_maxKey!_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> maxKey!) = maxKey! l ↔ (k == (maxKey! l)) = false :=
  letI : Ord α := .opposite inferInstance
  minKey!_eraseKey_eq_iff_beq_minKey!_eq_false hd he

theorem maxKey!_eraseKey_eq_of_beq_maxKey!_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k}
    (he : (eraseKey k l).isEmpty = false) : (heq : (k == maxKey! l) = false) →
    (eraseKey k l |> maxKey!) = maxKey! l :=
  letI : Ord α := .opposite inferInstance
  minKey!_eraseKey_eq_of_beq_minKey!_eq_false hd he

theorem maxKey!_erase_le_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (he : (eraseKey k l).isEmpty = false) :
    compare (eraseKey k l |> maxKey!) (maxKey! l) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_le_minKey!_erase hd he

theorem maxKey!_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    (insertEntryIfNew k v l |> maxKey!) =
      (maxKey? l).elim k fun k' => if compare k' k = .lt then k else k' :=
  letI : Ord α := .opposite inferInstance
  minKey!_insertEntryIfNew hd

theorem maxKey!_le_maxKey!_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v} :
    compare (maxKey! l) (insertEntryIfNew k v l |> maxKey!) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_insertEntryIfNew_le_minKey! hd he

theorem self_le_maxKey!_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v} :
    compare k (insertEntryIfNew k v l |> maxKey!) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_insertEntryIfNew_le_self hd

theorem maxKey!_eq_getLast!_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) :
    maxKey! l = (keys l).getLast! := by
  simp only [List.getLast!_eq_getLast?_getD, maxKey!_eq_get!_maxKey?,
    Option.get!_eq_getD, maxKey?_eq_getLast?_keys hd ho]

theorem maxKey!_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f} :
    (modifyKey k f l |> maxKey!) = maxKey! l :=
  letI : Ord α := .opposite inferInstance
  minKey!_modifyKey hd

theorem maxKey!_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    [Inhabited α] {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f}
    (he : (alterKey k f l).isEmpty = false) :
    (alterKey k f l |> maxKey!) = k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_alterKey_eq_self hd he

namespace Const

variable {β : Type v}

theorem maxKey!_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (modifyKey k f l).isEmpty = false) :
    (modifyKey k f l |> maxKey!) = if (maxKey! l) == k then k else (maxKey! l) :=
  letI : Ord α := .opposite inferInstance
  minKey!_modifyKey hd he

theorem maxKey!_modifyKey_eq_maxKey! [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    [Inhabited α] {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} :
    (modifyKey k f l |> maxKey!) = maxKey! l :=
  letI : Ord α := .opposite inferInstance
  minKey!_modifyKey_eq_minKey! hd

theorem maxKey!_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} :
    (modifyKey k f l |> maxKey!) == (maxKey! l) :=
  letI : Ord α := .opposite inferInstance
  minKey!_modifyKey_beq hd

theorem maxKey!_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (alterKey k f l).isEmpty = false):
    (alterKey k f l |> maxKey!) = k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKey!_alterKey_eq_self hd he

end Const

/-- Returns the smallest key in an associative list or `fallback` if the list is empty. -/
abbrev maxKeyD [Ord α] (xs : List ((a : α) × β a)) (fallback : α) : α :=
  letI : Ord α := .opposite inferInstance; minKeyD xs fallback

theorem maxKeyD_of_perm [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l l' : List ((a : α) × β a)} {fallback} (hd : DistinctKeys l) (hp : l.Perm l') :
    maxKeyD l fallback = maxKeyD l' fallback :=
  letI : Ord α := .opposite inferInstance
  minKeyD_of_perm hd hp

theorem maxKeyD_eq_getD_maxKey? [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {fallback} :
    maxKeyD l fallback = (maxKey? l).getD fallback :=
  letI : Ord α := .opposite inferInstance
  minKeyD_eq_getD_minKey?

theorem maxKey_eq_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {he fallback} :
    maxKey l he = maxKeyD l fallback :=
  letI : Ord α := .opposite inferInstance
  minKey_eq_minKeyD

theorem maxKey?_eq_some_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {fallback} (he : l.isEmpty = false) :
    maxKey? l = some (maxKeyD l fallback) :=
  letI : Ord α := .opposite inferInstance
  minKey?_eq_some_minKeyD he

theorem maxKey!_eq_maxKeyD_default [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} :
    maxKey! l = maxKeyD l default :=
  letI : Ord α := .opposite inferInstance
  minKey!_eq_minKeyD_default

theorem maxKeyD_eq_fallback [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} {fallback} (h : l.isEmpty) :
    maxKeyD l fallback = fallback :=
  letI : Ord α := .opposite inferInstance
  minKeyD_eq_fallback h

theorem maxKeyD_eq_iff_getKey?_eq_self_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {km fallback} :
    maxKeyD l fallback = km ↔
      getKey? km l = some km ∧ ∀ k, containsKey k l → (compare k km).isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_eq_iff_getKey?_eq_self_and_forall hd he

theorem maxKeyD_eq_iff_mem_and_forall [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    [LawfulEqOrd α] {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (he : l.isEmpty = false) {km fallback} :
    maxKeyD l fallback = km ↔ containsKey km l ∧ ∀ k, containsKey k l → (compare k km).isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_eq_iff_mem_and_forall hd he

theorem maxKeyD_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    (insertEntry k v l |> maxKeyD <| fallback) =
      ((maxKey? l).elim k fun k' => if compare k' k |>.isLE then k else k') :=
  letI : Ord α := .opposite inferInstance
  minKeyD_insertEntry hd

theorem maxKeyD_le_maxKeyD_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v fallback} :
    compare (maxKeyD l fallback) (insertEntry k v l |> maxKeyD <| fallback) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_insertEntry_le_minKeyD hd he

theorem self_le_maxKeyD_insertEntry [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    compare k (insertEntry k v l |> maxKeyD <| fallback) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_insertEntry_le_self hd

theorem containsKey_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    containsKey (maxKeyD l fallback) l :=
  letI : Ord α := .opposite inferInstance
  containsKey_minKeyD hd he

theorem le_maxKeyD_of_containsKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (hc : containsKey k l) {fallback} :
    compare k (maxKeyD l fallback) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_le_of_containsKey hd hc

theorem maxKeyD_le [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k fallback} :
    (compare (maxKeyD l fallback) k).isLE ↔ (∀ k', containsKey k' l → (compare k' k).isLE) :=
  letI : Ord α := .opposite inferInstance
  le_minKeyD hd he

theorem getKey?_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    getKey? (maxKeyD l fallback) l = some (maxKeyD l fallback) :=
  letI : Ord α := .opposite inferInstance
  getKey?_minKeyD hd he

theorem getKey_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {fallback he} :
    getKey (maxKeyD l fallback) l he = maxKeyD l fallback :=
  letI : Ord α := .opposite inferInstance
  getKey_minKeyD hd

theorem getKey_maxKeyD_eq_maxKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {fallback he} :
    getKey (maxKeyD l fallback) l he = maxKey l (isEmpty_eq_false_of_containsKey he) :=
  letI : Ord α := .opposite inferInstance
  getKey_minKeyD_eq_minKey hd

theorem getKey!_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [Inhabited α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback} :
    getKey! (maxKeyD l fallback) l = maxKeyD l fallback :=
  letI : Ord α := .opposite inferInstance
  getKey!_minKeyD hd he

theorem getKeyD_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {fallback fallback'} :
    getKeyD (maxKeyD l fallback) l fallback' = maxKeyD l fallback :=
  letI : Ord α := .opposite inferInstance
  getKeyD_minKeyD hd he

theorem maxKeyD_eraseKey_eq_iff_beq_maxKey_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k fallback}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> maxKeyD <| fallback) = maxKeyD l fallback ↔
      (k == (maxKeyD l fallback)) = false :=
  letI : Ord α := .opposite inferInstance
  minKeyD_eraseKey_eq_iff_beq_minKey_eq_false hd he

theorem maxKeyD_eraseKey_eq_iff_beq_maxKeyD_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k fallback}
    (he : (eraseKey k l).isEmpty = false) :
    (eraseKey k l |> maxKeyD <| fallback) = maxKeyD l fallback ↔
      (k == (maxKeyD l fallback)) = false :=
  letI : Ord α := .opposite inferInstance
  minKeyD_eraseKey_eq_iff_beq_minKeyD_eq_false hd he

theorem maxKeyD_eraseKey_eq_of_beq_maxKeyD_eq_false [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k fallback}
    (he : (eraseKey k l).isEmpty = false) : (heq : (k == maxKeyD l fallback) = false) →
    (eraseKey k l |> maxKeyD <| fallback) = maxKeyD l fallback:=
  letI : Ord α := .opposite inferInstance
  minKeyD_eraseKey_eq_of_beq_minKeyD_eq_false hd he

theorem maxKeyD_eraseKey_le_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k} (he : (eraseKey k l).isEmpty = false)
    {fallback} :
    compare (eraseKey k l |> maxKeyD <| fallback) (maxKeyD l fallback) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_le_minKeyD_erase hd he

theorem maxKeyD_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    (insertEntryIfNew k v l |> maxKeyD <| fallback) =
      (maxKey? l).elim k fun k' => if compare k' k = .lt then k else k' :=
  letI : Ord α := .opposite inferInstance
  minKeyD_insertEntryIfNew hd

theorem maxKeyD_le_maxKeyD_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) (he : l.isEmpty = false) {k v fallback} :
    compare (maxKeyD l fallback) (insertEntryIfNew k v l |> maxKeyD <| fallback) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_insertEntryIfNew_le_minKeyD hd he

theorem self_le_maxKeyD_insertEntryIfNew [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k v fallback} :
    compare k (insertEntryIfNew k v l |> maxKeyD <| fallback) |>.isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_insertEntryIfNew_le_self hd

theorem maxKeyD_eq_getLastD_keys [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l)
    (ho : l.Pairwise fun a b => compare a.1 b.1 = .lt) {fallback} :
    maxKeyD l fallback = (keys l).getLastD fallback := by
  simp only [List.getLastD_eq_getLast?, maxKeyD_eq_getD_maxKey?,
    Option.get!_eq_getD, maxKey?_eq_getLast?_keys hd ho]

theorem maxKeyD_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f fallback} :
    (modifyKey k f l |> maxKeyD <| fallback) = maxKeyD l fallback :=
  letI : Ord α := .opposite inferInstance
  minKeyD_modifyKey hd

theorem maxKeyD_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((a : α) × β a)} (hd : DistinctKeys l) {k f fallback}
    (he : (alterKey k f l).isEmpty = false) :
    (alterKey k f l |> maxKeyD <| fallback) = k ↔
      (f (getValueCast? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_alterKey_eq_self hd he

namespace Const

variable {β : Type v}

theorem maxKeyD_modifyKey [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (modifyKey k f l).isEmpty = false)
    {fallback} :
    (modifyKey k f l |> maxKeyD <| fallback) = if (maxKeyD l fallback) == k then k else (maxKeyD l fallback) :=
  letI : Ord α := .opposite inferInstance
  minKeyD_modifyKey hd he

theorem maxKeyD_modifyKey_eq_maxKeyD [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α] [LawfulEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f fallback} :
    (modifyKey k f l |> maxKeyD <| fallback) = maxKeyD l fallback :=
  letI : Ord α := .opposite inferInstance
  minKeyD_modifyKey_eq_minKeyD hd

theorem maxKeyD_modifyKey_beq [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f fallback} :
    (modifyKey k f l |> maxKeyD <| fallback) == (maxKeyD l fallback) :=
  letI : Ord α := .opposite inferInstance
  minKeyD_modifyKey_beq hd

theorem maxKeyD_alterKey_eq_self [Ord α] [TransOrd α] [BEq α] [LawfulBEqOrd α]
    {l : List ((_ : α) × β)} (hd : DistinctKeys l) {k f} (he : (alterKey k f l).isEmpty = false)
    {fallback} :
    (alterKey k f l |> maxKeyD <| fallback) = k ↔
      (f (getValue? k l)).isSome ∧ ∀ k', containsKey k' l → (compare k' k).isLE :=
  letI : Ord α := .opposite inferInstance
  minKeyD_alterKey_eq_self hd he

end Const

end Max

end Std.Internal.List
