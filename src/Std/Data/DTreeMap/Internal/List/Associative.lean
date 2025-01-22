/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Data.DHashMap.Internal.List.Associative
import Orderedtree.Classes.TransOrd

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

-- theorem Option.unattach_eq_some {α : Type u} {p : α → Prop} {a : α} {o : Option { x // p x}} : o.unattach = some a ↔ ∃ h : p a, o = some ⟨a, h⟩ :=
--   o.rec (by simp) (fun h => ⟨by simp only [unattach_some, some.injEq]; rintro rfl; exact ⟨h.2, rfl⟩,
--     by simp only [some.injEq, unattach_some, forall_exists_index]; rintro hx rfl; rfl⟩)

-- unused
-- theorem List.min?_mem₂ {α : Type u} [Min α] {xs : List α} (min_eq_or : ∀ a b : α, a ∈ xs → b ∈ xs → min a b = a ∨ min a b = b) {a : α} :
--     xs.min? = some a → a ∈ xs := by
--   match xs with
--   | List.nil => simp
--   | x :: xs =>
--     simp only [List.min?_cons', Option.some.injEq, List.mem_cons]
--     intro eq
--     induction xs generalizing x with
--     | nil =>
--       simp at eq
--       simp [eq]
--     | cons y xs ind =>
--       simp at eq
--       have hxy : min x y = x ∨ min x y = y := min_eq_or x y (List.mem_cons_self _ _) (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
--       have p := ind _ ?_ eq
--       · cases p with
--         | inl p =>
--           cases hxy with | _ q => simp [p, q]
--         | inr p => simp [p, List.mem_cons]
--       · intro a b ha hb
--         apply min_eq_or
--         · refine hxy.elim (fun hxy => (List.mem_cons.1 ha).elim ?_ ?_) (fun hxy => (List.mem_cons.1 ha).elim ?_ ?_)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_self _ _
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
--         · refine hxy.elim (fun hxy => (List.mem_cons.1 hb).elim ?_ ?_) (fun hxy => (List.mem_cons.1 hb).elim ?_ ?_)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_self _ _
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
--           · exact fun h => h ▸ hxy.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_self _ _)
--           · exact fun h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem List.min?_eq_head? {α : Type u} [Min α] {l : List α} (h : l.Pairwise (fun a b => min a b = a)) : l.min? = l.head? := by
  cases l with
  | nil => simp
  | cons x l =>
    rw [List.head?_cons, List.min?_cons', Option.some.injEq]
    induction l generalizing x with
    | nil => simp
    | cons y l ih =>
      have hx : min x y = x := List.rel_of_pairwise_cons h (List.mem_cons_self _ _)
      rw [List.foldl_cons, ih _ (hx.symm ▸ h.sublist (by simp)), hx]


variable {α : Type u} {β : α → Type v}

namespace Std.DHashMap.Internal.List

@[simp]
theorem getEntry_fst [BEq α] {xs : List ((a : α) × β a)} {k : α} (h : containsKey k xs) :
    (getEntry k xs h).1 = getKey k xs h := by
  induction xs using assoc_induction
  · simp at h
  · next k' v' l ih =>
    cases hkk' : k' == k
    · rw [getEntry_cons_of_false hkk', getKey_cons]
      simp [hkk', ih]
    · rw [getEntry_cons_of_beq hkk', getKey_cons]
      simp [hkk']

theorem getKey_beq [BEq α] {xs : List ((a : α) × β a)} {k : α} (h : containsKey k xs) :
    getKey k xs h == k := by
  induction xs using assoc_induction
  · simp at h
  · next k' v' l ih =>
    rw [getKey_cons]
    split
    · assumption
    · apply ih

end Std.DHashMap.Internal.List

-- TODO: mark Ordering.isLE as @[inline]

def minSigmaOfOrd [Ord α] : Min ((a : α) × β a) where
  min a b := if compare a.1 b.1 |>.isLE then a else b

attribute [local instance] minSigmaOfOrd

-- TODO: duplicate in WF.lean
@[local instance]
def beqOfOrd [Ord α] : BEq α where
  beq a b := compare a b == .eq

theorem beq_eq [Ord α] {a b : α} : (a == b) = (compare a b == .eq) :=
  rfl

@[local instance]
theorem equivBEq_of_transOrd [Ord α] [TransOrd α] : EquivBEq α where
  symm {a b} h := by simp_all [OrientedCmp.eq_comm, beq_eq]
  trans h₁ h₂ := by simp_all only [beq_eq, beq_iff_eq]; exact TransCmp.eq_trans h₁ h₂
  refl := by simp [beq_eq]

theorem min_def [Ord α] {p q : (a : α) × β a} : min p q = if compare p.1 q.1 |>.isLE then p else q := rfl

theorem min_eq_or [Ord α] {p q : (a : α) × β a} : min p q = p ∨ min p q = q := by
  rw [min_def]
  split <;> simp

theorem min_eq_left [Ord α] {p q : (a : α) × β a} (h : compare p.1 q.1 |>.isLE) : min p q = p := by
  simp [min_def, h]

theorem min_eq_left_of_lt [Ord α] {p q : (a : α) × β a} (h : compare p.1 q.1 = .lt) : min p q = p :=
  min_eq_left (Ordering.isLE_of_eq_lt h)

-- Is this provable without `TransOrd`?
local instance [Ord α] [TransOrd α] : Std.Associative (min : (a : α) × β a → (a : α) × β a → (a : α) × β a) where
  assoc a b c := by
    simp only [min_def]
    split <;> split <;> (try split) <;> try rfl
    · rename_i hab hac hbc
      have := TransCmp.le_trans hab hbc
      contradiction
    · rename_i hab hbc hac
      simp only [Bool.not_eq_true, Ordering.isLE_eq_false] at hab hbc
      refine absurd hac ?_
      simp only [Bool.not_eq_true, Ordering.isLE_eq_false]
      exact OrientedCmp.gt_of_lt (TransCmp.lt_trans (OrientedCmp.lt_of_gt hbc) (OrientedCmp.lt_of_gt hab))

namespace Std.DHashMap.Internal.List

/-- The smallest element of `xs` that is not less than `k`. -/
def lookupGE [Ord α] (k : α) (xs : List ((a : α) × β a)) : Option ((a : α) × β a) :=
  xs.filter (fun p => compare k p.1 |>.isLE) |>.min?

/-- Like `List.min?`, but using an `Ord` typeclass instead of a `Min` typeclass. -/
def min?' [Ord α] (xs : List ((a : α) × β a)) : Option ((a : α) × β a) :=
  xs.min?

theorem lookupGE_mem [Ord α] {xs : List ((a : α) × β a)} {k : α} {p : (a : α) × β a} (h : lookupGE k xs = some p) :
    p ∈ xs := by
  rw [lookupGE] at h
  have := List.min?_mem (@min_eq_or _ _ _) h
  simp at this
  exact this.1

/-- The smallest element of `xs` that is greater than `k`. -/
def lookupGT [Ord α] (xs : List ((a : α) × β a)) (k : α) : Option ((a : α) × β a) :=
  xs.filter (fun p => compare k p.1 = .lt) |>.min?

@[simp]
theorem lookupGE_nil [Ord α] {k : α} : lookupGE k ([] : List ((a : α) × β a)) = none := rfl

@[simp]
theorem min?_nil [Ord α] [TransOrd α] : min?' ([] : List ((a : α) × β a)) = none := by
  simp [min?']

theorem min?_cons [Ord α] [TransOrd α] (e : (a : α) × β a) (l : List ((a : α) × β a)) :
    min?' (e :: l) = some (match min?' l with
    | none => e
    | some w => min e w) := by
  simp [min?', List.min?]
  induction l generalizing e
  · simp
  · next tail ih =>
    simp
    simp [ih]
    cases tail
    · simp
    · simp [Associative.assoc]

theorem min?_eq_none [Ord α] (l : List ((a : α) × β a)) :
    min?' l = none ↔ l = [] := by
  simp [min?']

theorem min?_isSome_of_isEmpty_eq_false [Ord α] {l : List ((a : α) × β a)} (hl : l.isEmpty = false) :
    (min?' l).isSome := by
  cases l
  · simp_all [min?']
  · simp [min?', List.min?]

theorem min?_isSome_of_mem [Ord α] {l : List ((a : α) × β a)} {e : (a : α) × β a} (he : e ∈ l) :
    (min?' l).isSome := by
  apply min?_isSome_of_isEmpty_eq_false
  match l with
  | [] => contradiction
  | x :: xs => simp

theorem min?_isSome_of_contains [Ord α] {l : List ((a : α) × β a)} {b : α} (hb : containsKey b l) :
    (min?' l).isSome := by
  apply min?_isSome_of_isEmpty_eq_false
  match l with
  | [] => contradiction
  | x :: xs => simp

theorem min?_fst [Ord α] (a b : ((a : α) × β a)) :
    (min a b).fst = if compare a.fst b.fst |>.isLE then a.fst else b.fst := by
  simp [min]
  split <;> rfl

theorem le_min? [Ord α] [TransOrd α] (l : List ((a : α) × β a)) (e : (a : α) × β a) (he : e ∈ l) :
    (compare ((min?' l).get (min?_isSome_of_mem he)).fst e.fst).isLE := by
  induction l
  · contradiction
  · next head tail ih =>
    simp [min?_cons]
    simp at he
    cases he
    · next he =>
      cases he.symm
      cases min?' tail
      · simp [Ordering.isLE]
      · simp [min?_fst]
        split
        · simp [Ordering.isLE]
        · next h₁ =>
          rw [OrientedCmp.eq_swap (cmp := compare)]
          cases h₂ :compare e.fst _
          · simp [Ordering.isLE, Ordering.swap, h₂] at h₁
          · simp [Ordering.isLE]
          · simp [Ordering.isLE, Ordering.swap]
    · have ih := ih (by assumption)
      have := min?_isSome_of_mem (by assumption)
      cases ht : min?' tail
      · simp [ht] at this
      · simp
        simp [ht] at ih
        simp [min]
        split
        · apply TransOrd.le_trans
          · assumption
          · exact ih
        · exact ih

theorem le_min?' [Ord α] [TransOrd α] (l : List ((a : α) × β a)) (b : α) (hb : containsKey b l) :
    (compare ((min?' l).get (min?_isSome_of_contains hb)).fst b).isLE := by
  induction l
  · contradiction
  · next head tail ih =>
    simp [min?_cons]
    simp [containsKey] at hb
    cases hb
    · next heq =>
      rw [beq_eq, beq_iff_eq] at heq
      rw [← TransCmp.congr_right (cmp := compare) heq]
      split
      · simp
      · rw [min?_fst]
        split
        · simp
        · next h =>
          simp at h
          rw [OrientedCmp.eq_swap (cmp := compare)]
          simp [h]
    · have ih := ih (by assumption)
      have := min?_isSome_of_contains (by assumption)
      cases ht : min?' tail
      · simp [ht] at this
      · simp
        simp [ht] at ih
        simp [min]
        split
        · apply TransOrd.le_trans
          · assumption
          · exact ih
        · exact ih

theorem min?_lower_bound [Ord α] [TransOrd α] (l : List ((a : α) × β a)) (he : l.isEmpty = false) :
    ∀ e ∈ l, (compare ((min?' l).get (min?_isSome_of_isEmpty_eq_false he)).fst e.fst).isLE := by
  induction l
  · simp
  · next ih =>
    intro f hf
    apply le_min?
    assumption

theorem min?_lower_bound' [Ord α] [TransOrd α] (l : List ((a : α) × β a)) (he : l.isEmpty = false) :
    ∀ b : α, containsKey b l → (compare ((min?' l).get (min?_isSome_of_isEmpty_eq_false he)).fst b).isLE := by
  induction l
  · simp
  · next ih =>
    intro f hf
    apply le_min?'
    assumption

theorem mem_min? [Ord α] [TransOrd α] (l : List ((a : α) × β a)) (he : l.isEmpty = false) :
    (min?' l).get (min?_isSome_of_isEmpty_eq_false he) ∈ l := by
  induction l
  · simp at he
  · next head tail ih =>
    simp [min?_cons]
    cases h : tail.isEmpty
    · cases h' : min?' tail
      · simp
      · next w =>
        simp
        have ih := ih h
        simp [h'] at ih
        cases min_eq_or (p := head) (q := w)
        · next h =>
          exact Or.inl h
        · next h =>
          rw [h]
          exact Or.inr ih
    · simp at h
      simp [h]

theorem mem_min?' [Ord α] [TransOrd α] (l : List ((a : α) × β a)) {he : (min?' l).isSome} :
    (min?' l).get he ∈ l := by
  apply mem_min?
  cases l
  · simp_all
  · simp

theorem eq_of_beq_and_mem [BEq α] [EquivBEq α] {a b : (a : α) × β a} {l : List ((a : α) × β a)} (he : a.1 == b.1) (hma : a ∈ l) (hmb : b ∈ l) (hd : DistinctKeys l) :
    a = b := by
  induction l
  · contradiction
  · next head tail ih =>
    simp at hma hmb
    cases hma <;> cases hmb
    · simp_all
    · next h₁ h₂ =>
      cases head
      next hk hv =>
      simp [distinctKeys_cons_iff] at hd
      cases h₁
      simp [containsKey_congr he] at hd
      simp [containsKey_of_mem h₂] at hd
    · next h₁ h₂ =>
      cases h₂
      cases b
      simp [distinctKeys_cons_iff, ← containsKey_congr he, containsKey_of_mem h₁] at hd
    · apply ih <;> try assumption
      exact hd.tail

theorem eq_min?_iff [Ord α] [TransOrd α] (a : (a : α) × β a) {l : List ((a : α) × β a)} (he : l.isEmpty = false) (hd : DistinctKeys l) :
    a = (min?' l).get (min?_isSome_of_isEmpty_eq_false he) ↔ a ∈ l ∧ ∀ e ∈ l, (compare a.fst e.fst).isLE := by
  apply Iff.intro
  · intro h
    simp [h]
    apply And.intro
    · exact mem_min? _ he
    · exact min?_lower_bound _ he
  · intro ⟨h₁, h₂⟩
    have h₃ := mem_min? _ he
    have h₄ := min?_lower_bound _ he
    apply eq_of_beq_and_mem
    · rw [beq_eq, beq_iff_eq]
      apply TransCmp.eq_of_lt_of_lt
      · apply h₂
        exact h₃
      · apply h₄
        exact h₁
    · exact h₁
    · exact h₃
    · exact hd

theorem eq_min?_iff' [Ord α] [TransOrd α] (a : (a : α) × β a) {l : List ((a : α) × β a)} (he : l.isEmpty = false) (hd : DistinctKeys l) :
    a = (min?' l).get (min?_isSome_of_isEmpty_eq_false he) ↔ a ∈ l ∧ ∀ b : α, containsKey b l → (compare a.fst b).isLE := by
  apply Iff.intro
  · intro h
    simp [h]
    apply And.intro
    · exact mem_min? _ he
    · exact min?_lower_bound' _ he
  · intro ⟨h₁, h₂⟩
    have h₃ := mem_min? _ he
    have h₄ := min?_lower_bound' _ he
    apply eq_of_beq_and_mem
    · rw [beq_eq, beq_iff_eq]
      apply TransCmp.eq_of_lt_of_lt
      · apply h₂
        exact containsKey_of_mem h₃
      · apply h₄
        exact containsKey_of_mem h₁
    · exact h₁
    · exact h₃
    · exact hd

theorem some_eq_min?_iff [Ord α] [TransOrd α] (a : (a : α) × β a) {l : List ((a : α) × β a)} (he : l.isEmpty = false) (hd : DistinctKeys l) :
    some a = min?' l ↔ a ∈ l ∧ ∀ e ∈ l, (compare a.fst e.fst).isLE := by
  have := min?_isSome_of_isEmpty_eq_false he
  rw [← eq_min?_iff a he hd]
  apply Iff.intro
  · intro h
    simp [← h]
  · intro h
    simp [h]

theorem some_eq_min?_iff' [Ord α] [TransOrd α] (a : (a : α) × β a) {l : List ((a : α) × β a)} (he : l.isEmpty = false) (hd : DistinctKeys l) :
    some a = min?' l ↔ a ∈ l ∧ ∀ b : α, containsKey b l → (compare a.fst b).isLE := by
  have := min?_isSome_of_isEmpty_eq_false he
  rw [← eq_min?_iff' a he hd]
  apply Iff.intro
  · intro h
    simp [← h]
  · intro h
    simp [h]

theorem mem_replaceEntry_of_containsKey [BEq α] {k : α} (v : β k) {l : List ((a : α) × β a)}
    (hc : containsKey k l) :
    ⟨k, v⟩ ∈ replaceEntry k v l := by
  induction l
  · simp at hc
  · next head tail ih =>
    simp [replaceEntry]
    cases h : head.fst == k
    · simp
      cases head
      simp [containsKey_cons, h] at hc
      exact Or.inr <| ih hc
    · simp

theorem mem_replaceEntry_of_bne_containsKey [BEq α] [EquivBEq α] (e : (a : α) × β a) {k : α} (v : β k) {l : List ((a : α) × β a)}
    (hne : (k == e.fst) = false) (hc : e ∈ l) :
    e ∈ replaceEntry k v l := by
  induction l
  · simp_all
  · simp at hc
    next head tail ih =>
    simp [replaceEntry]
    cases h : head.fst == k
    · simp
      cases hc
      · next h => exact Or.inl h
      · next h => exact Or.inr <| ih h
    · simp
      cases hc
      · next h' =>
        rw [h'] at hne
        have hne := BEq.symm_false hne
        simp [hne] at h
      · next h => exact Or.inr h

theorem containsKey_getKey [BEq α] [EquivBEq α] {k : α} {l : List ((a : α) × β a)}
    (hc : containsKey k l) :
    containsKey (getKey k l hc) l := by
  rw [containsKey_congr <| getKey_beq hc]
  exact hc

theorem min?_replaceEntry [Ord α] [TransOrd α] (k : α) (v : β k) (l : List ((a : α) × β a))
    (hl : DistinctKeys l) :
    min?' (replaceEntry k v l) =
      if containsKey k l then
        some (match min?' l with
          | none => ⟨k, v⟩
          | some w => if compare k w.fst |>.isLE then ⟨k, v⟩ else w)
      else
        min?' l := by
  cases h : containsKey k l
  · rw [replaceEntry_of_containsKey_eq_false]
    · simp
    · exact h
  · simp
    apply Eq.symm
    apply some_eq_min?_iff .. |>.mpr
    · apply And.intro
      · split
        · next heq =>
          have := min?_isSome_of_isEmpty_eq_false <| isEmpty_eq_false_of_containsKey h
          simp [heq] at this
        · next w heq =>
          split
          · next heq₂ =>
            have := mem_min? l (isEmpty_eq_false_of_containsKey h)
            rw [Option.eq_some_iff_get_eq] at heq
            simp [heq.2] at this
            have := containsKey_of_mem this
            exact mem_replaceEntry_of_containsKey v h
          · next h₁ =>
            apply mem_replaceEntry_of_bne_containsKey
            · simp at h₁
              simp [beq_eq, h₁]
            · rw [Option.eq_some_iff_get_eq] at heq
              simp [heq.2.symm]
              apply mem_min?'
      · intro e he
        cases h' : min?' l
        · have := min?_isSome_of_isEmpty_eq_false (isEmpty_eq_false_of_containsKey (by assumption))
          rw [h'] at this
          contradiction
        · have h' := h'.symm
          simp
          rw [some_eq_min?_iff'] at h'
          · split
            · next heq =>
              refine TransCmp.le_trans heq ?_
              apply h'.2
              have hce := containsKey_of_mem he
              simpa using hce
            · apply h'.2
              have hce := containsKey_of_mem he
              simpa using hce
          · exact isEmpty_eq_false_of_containsKey h
          · exact hl
    · simp [isEmpty_replaceEntry, isEmpty_eq_false_of_containsKey h]
    · exact hl.replaceEntry

theorem min?_insertKey [Ord α] [TransOrd α] (k : α) (v : β k) (l : List ((a : α) × β a))
    (hl : DistinctKeys l) :
    min?' (insertEntry k v l) =
      some (match min?' l with
        | none => ⟨k, v⟩
        | some w => if compare k w.fst |>.isLE then ⟨k, v⟩ else w) := by
  simp [insertEntry]
  cases h : containsKey k l
  · simp [min?_cons]
    rfl
  · simp
    rw [min?_replaceEntry, if_pos h]
    exact hl

theorem min?_of_perm [Ord α] [TransOrd α] {l l' : List ((a : α) × β a)}
    (hl : DistinctKeys l) (hp : l.Perm l') :
    min?' l = min?' l' := by
  cases he : l.isEmpty
  · have he' : l'.isEmpty = false := hp.isEmpty_eq ▸ he
    have hs : (min?' l).isSome := min?_isSome_of_isEmpty_eq_false he
    have hs' : (min?' l').isSome := min?_isSome_of_isEmpty_eq_false he'
    ext
    simp
    conv => congr <;> rw [eq_comm]
    rw [some_eq_min?_iff' _ he hl, some_eq_min?_iff' _ he' <| hl.perm hp.symm]
    simp [hp.mem_iff, containsKey_of_perm hp]
  · simp_all

-- theorem lookupGE_cons [Ord α] [TransOrd α] (l : List ((a : α) × β a)) (k : α) (v : β k) (a : α) :
--     lookupGE (⟨k, v⟩ :: l) a =
--       if compare k a = .lt then lookupGE l a else some ((lookupGE l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   rw [lookupGE, List.filter_cons]
--   simp only [decide_eq_true_eq]
--   split
--   · rw [List.min?_cons]
--     split
--     · exact False.elim (not_lt_self (lt_of_le_of_lt (b := k) ‹_› ‹_›))
--     · rfl
--   · next h =>
--     rw [not_le_iff_lt] at h
--     simp [h, lookupGE]

-- theorem lookupGE_cons_eq_self [TransOrd α] {l : List ((a : α) × β a)} {p : (a : α) × β a} {k : α}
--     (hp : k ≤ p.1) (hl : ∀ q ∈ l, q.1 < k ∨ p.1 ≤ q.1) : lookupGE (p :: l) k = some p := by
--   rw [lookupGE_cons]
--   simp only [not_lt_iff_le.2 hp, ↓reduceIte, Option.some.injEq]
--   rw [lookupGE]
--   cases h : (l.filter (fun p => k ≤ p.1)).min? with
--   | none => simp
--   | some q =>
--     have := List.mem_filter.1 (List.min?_mem (fun _ _ => min_eq_or) h)
--     simp only [decide_eq_true_eq] at this
--     suffices p.1 ≤ q.1 by simpa using min_eq_left' this
--     exact (hl _ this.1).resolve_left (not_lt_iff_le.2 this.2)

-- theorem min_comm_of_lt_or_lt [OrientedOrd α] {p p' : (a : α) × β a} (h : p.1 < p'.1 ∨ p'.1 < p.1) :
--     min p p' = min p' p := by
--   rcases h with h|h <;> simp [min_def', le_of_lt h, not_le_iff_lt.2 h]

-- theorem lt_or_lt_of_containsKey_eq_false [TransOrd α] {l : List ((a : α) × β a)} {p : (a : α) × β a} {k : α}
--     (hp : p ∈ l) (hk : containsKey k l = false) : p.1 < k ∨ k < p.1 := by
--   rcases lt_or_lt_or_beq p.1 k with h|h|h
--   · exact Or.inl h
--   · exact Or.inr h
--   · rw [containsKey_congr (BEq.symm h), containsKey_of_mem hp] at hk
--     contradiction

-- theorem lookupGE_of_perm [TransOrd α] {l l' : List ((a : α) × β a)} (hll' : List.Perm l l') {k : α} (hl : DistinctKeys l) :
--     lookupGE l k = lookupGE l' k := by
--   induction hll' with
--   | nil => rfl
--   | @cons x l l' _ ih => rw [lookupGE_cons, lookupGE_cons, ih hl.tail]
--   | swap x y l =>
--     rw [lookupGE_cons, lookupGE_cons, lookupGE_cons, lookupGE_cons]
--     split <;> split <;> try (simp; done)
--     rename_i hyk hxk
--     have hxy : x.1 < y.1 ∨ y.1 < x.1 :=
--       lt_or_lt_of_containsKey_eq_false (List.mem_cons_self _ _) hl.containsKey_eq_false
--     cases lookupGE l k with
--     | none => simpa using (min_comm_of_lt_or_lt hxy).symm
--     | some p => simp [← Std.Associative.assoc (op := min), min_comm_of_lt_or_lt hxy]
--   | trans h₁ _ ih₁ ih₂ => rw [ih₁ hl, ih₂ (hl.perm h₁.symm)]

-- theorem lookupGE_replaceEntry_cons_of_beq [TransOrd α] {l : List ((a : α) × β a)}
--     {k a : α} {v : β k} {p : (a : α) × β a} (h : p.1 == k) : lookupGE (replaceEntry k v (p :: l)) a =
--       if k < a then lookupGE l a else some ((lookupGE l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   rw [replaceEntry_cons_of_true h, lookupGE_cons]

-- theorem lookupGE_replaceEntry_of_containsKey_eq_true [TransOrd α] {l : List ((a : α) × β a)}
--       {k : α} {v : β k} {a : α} (h : containsKey k l) (hl : DistinctKeys l) :
--     lookupGE (replaceEntry k v l) a = if k < a then lookupGE l a else some ((lookupGE l a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   obtain ⟨l', hl'⟩ := perm_cons_getEntry h
--   rw [lookupGE_of_perm (replaceEntry_of_perm hl hl') hl.replaceEntry]
--   rw [lookupGE_replaceEntry_cons_of_beq (by simpa using getKey_beq _)]
--   rw [lookupGE_of_perm hl' hl, lookupGE_cons]
--   split <;> split
--   · rfl
--   · rename_i h₁ h₂
--     simp only [getEntry_fst] at h₂
--     have h₁' := lt_of_beq_of_lt (getKey_beq h) h₁
--     contradiction
--   · simp
--   · have hk : k ≤ getKey k l h := le_of_beq (BEq.symm (getKey_beq h))
--     cases lookupGE l' a with
--     | none => simp [min_def', hk]
--     | some p =>
--       simp only [Option.elim_some, Option.some.injEq]
--       rw [← Std.Associative.assoc (op := min)]
--       congr 1
--       simp [min_def', hk]

-- theorem lookupGE_insertEntry [TransOrd α] (xs : List ((a : α) × β a)) (k : α) (v : β k) (a : α) (h : DistinctKeys xs) :
--     lookupGE (insertEntry k v xs) a =
--       if k < a then lookupGE xs a else some ((lookupGE xs a).elim ⟨k, v⟩ (min ⟨k, v⟩)) := by
--   rw [insertEntry]
--   cases hc : containsKey k xs
--   · rw [cond_false, lookupGE_cons]
--   · rw [cond_true, lookupGE_replaceEntry_of_containsKey_eq_true hc h]

theorem lookupGE_append_of_forall_mem_left [Ord α] [TransOrd α] {l₁ l₂ : List ((a : α) × β a)}
    {k : α} (h : ∀ p ∈ l₁, compare k p.1 = .gt) :
    lookupGE k (l₁ ++ l₂) = lookupGE k l₂ := by
  rw [lookupGE, lookupGE, List.filter_append, List.filter_eq_nil_iff.2, List.nil_append]
  refine fun p hp => by simpa using h p hp

theorem min?'_eq_head? [Ord α] {l : List ((a : α) × β a)}
    (hl : l.Pairwise (fun a b => compare a.1 b.1 = .lt)) : min?' l = l.head? := by
  rw [min?', List.min?_eq_head? (hl.imp min_eq_left_of_lt)]

theorem lookupGE_eq_head? [Ord α] {l : List ((a : α) × β a)} {k : α} (h : ∀ p ∈ l, compare k p.1 |>.isLE)
    (hl : l.Pairwise (fun a b => compare a.1 b.1 = .lt)) : lookupGE k l = l.head? := by
  rw [lookupGE, List.filter_eq_self.2 h, List.min?_eq_head? (hl.imp min_eq_left_of_lt)]

/-
/-- The number of entries whose key is strictly less than the given key. -/
def rank (k : α) (l : List ((a : α) × β a)) : Nat :=
  l.filter (·.1 < k) |>.length

theorem rank_append_eq_left [OrientedOrd α] {k : α} {l₁ l₂ : List ((a : α) × β a)} (hl₂ : ∀ p ∈ l₂, k ≤ p.1) :
    rank k (l₁ ++ l₂) = rank k l₁ := by
  simpa [rank, not_lt_iff_le]

theorem rank_eq_length {k : α} {l : List ((a : α) × β a)} (hl : ∀ p ∈ l, p.1 < k) :
    rank k l = l.length := by
  simpa [rank]-/

end Std.DHashMap.Internal.List
