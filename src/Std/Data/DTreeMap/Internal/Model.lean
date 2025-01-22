/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.DTreeMap.Internal.Impl
import Orderedtree.DTreeMap.Internal.Cell

/-!
# Model implementations of tree map functions
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w}

namespace Std.DTreeMap.Internal

namespace Impl

/-!
## General infrastructure
-/

/-- Internal implementation detail of the ordered set -/
def contains' [Ord α] (k : α → Ordering) (l : Impl α β) : Bool :=
  match l with
  | .leaf => false
  | .inner _ k' _ l r =>
    match k k' with
    | .lt => contains' k l
    | .gt => contains' k r
    | .eq => true

theorem contains'_compare [Ord α] {k : α} {l : Impl α β} :
    l.contains' (compare k) = l.contains k := by
  induction l <;> simp_all [contains, contains'] <;> rfl

/-- Internal implementation detail of the ordered set. General tree-traversal function. -/
def applyPartition [Ord α] (k : α → Ordering) (l : Impl α β)
    (f : List ((a : α) × β a) → (c : Cell α β k) → (l.contains' k → c.contains) → List ((a : α) × β a) → δ) : δ :=
  go [] l id []
where
  go (ll : List ((a : α) × β a)) (m : Impl α β) (hm : l.contains' k → m.contains' k) (rr : List ((a : α) × β a)) : δ :=
  match m with
  | .leaf => f ll .empty (by simp [contains'] at hm; simp [hm]) rr
  | .inner _ k' v' l r =>
    match h : k k' with
    | .lt => go ll l (fun hc => have := hm hc; by rw [← this, contains']; simp_all) (⟨k', v'⟩ :: r.toListModel ++ rr)
    | .eq => f (ll ++ l.toListModel) (.ofEq k' v' h) (by simp) (r.toListModel ++ rr)
    | .gt => go (ll ++ l.toListModel ++ [⟨k', v'⟩]) r (fun hc => have := hm hc; by rw [← this, contains']; simp_all) rr

/-- Internal implementation detail of the ordered set -/
def applyCell [Ord α] (k : α) (l : Impl α β)
    (f : (c : Cell α β (compare k)) → (l.contains' (compare k) → c.contains) → δ) : δ :=
  match l with
  | .leaf => f .empty (by simp [contains'])
  | .inner _ k' v' l r =>
    match hcmp : compare k k' with
    | .lt => applyCell k l (fun c h => f c fun h' => h (by simpa [contains', hcmp] using h'))
    | .eq => f (.ofEq k' v' hcmp) (by simp)
    | .gt => applyCell k r (fun c h => f c fun h' => h (by simpa [contains', hcmp] using h'))

/-- Internal implementation detail of the ordered set -/
theorem applyCell_eq_applyPartition [Ord α] (k : α) (l : Impl α β)
    (f : (c : Cell α β (compare k)) → (l.contains' (compare k) → c.contains) → δ) :
    applyCell k l f = applyPartition (compare k) l (fun _ c hc _ => f c hc) := by
  rw [applyPartition]
  suffices ∀ L u v, (hL : l.contains' (compare k) ↔ L.contains' (compare k)) →
      applyCell k l f = applyPartition.go (compare k) L (fun _ c hc _ => f c (hc ∘ hL.1)) u l hL.2 v from
    this l [] [] Iff.rfl
  intro L u v hL
  induction l generalizing u v L
  · rename_i sz k' v' l r ih₁ ih₂
    simp only [applyCell, applyPartition.go]
    split <;> rename_i hcmp
    · exact ih₁ _ _ _ _ (by simpa [contains', hcmp] using hL)
    · rfl
    · exact ih₂ _ _ _ _ (by simpa [contains', hcmp] using hL)
  · simp [applyCell, applyPartition, applyPartition.go]

variable (α β) in
/--
Data structure used by the general tree-traversal function `explore`.
Internal implementation detail of the ordered set
-/
inductive ExplorationStep [Ord α] (k : α → Ordering) where
  /-- Needle was less than key at this node: return key-value pair and unexplored right subtree,
      recusion will continue in left subtree. -/
  | lt : (a : α) → k a = .lt → β a → List ((a : α) × β a) → ExplorationStep k
  /-- Needle was equal to key at this node: return key-value pair and both unexplored subtrees,
      recursion will terminate. -/
  | eq : List ((a : α) × β a) → Cell α β k → List ((a : α) × β a) → ExplorationStep k
  /-- Needle was larger than key at this node: return key-value pair and unexplored left subtree,
      recusion will containue in right subtree. -/
  | gt : List ((a : α) × β a) → (a : α) → k a = .gt → β a → ExplorationStep k

/-- General tree-traversal function. Internal implementation detail of the ordered set -/
def explore {γ : Type w} [Ord α] (k : α → Ordering) (init : γ)
    (inner : γ → ExplorationStep α β k → γ) (l : Impl α β) : γ :=
  match l with
  | .leaf => inner init (.eq [] .empty [])
  | .inner _ ky y l r =>
    match h : k ky with
    | .lt => explore k (inner init <| .lt ky h y r.toListModel) inner l
    | .eq => inner init <| .eq l.toListModel (Cell.ofEq ky y h) r.toListModel
    | .gt => explore k (inner init <| .gt l.toListModel ky h y) inner r

open ExplorationStep

theorem applyPartition_go_step [Ord α] {k : α → Ordering} {init : δ} (l₁ l₂) (l l' : Impl α β) (h)
  (f : δ → ExplorationStep α β k → δ) :
    applyPartition.go k l' (fun l' c _ r' => f init (.eq l' c r')) l₁ l h l₂ =
    applyPartition.go k l' (fun l' c _ r' => f init (.eq (l₁ ++ l') c (r' ++ l₂))) [] l h [] := by
  suffices ∀ l₃ l₄,
    applyPartition.go k l' (fun l' c _ r' => f init (.eq (l₃ ++ l') c (r' ++ l₄))) l₁ l h l₂ =
    applyPartition.go k l' (fun l' c _ r' => f init (.eq (l₃ ++ l₁ ++ l') c (r' ++ l₂ ++ l₄))) [] l h [] by
    simpa using this [] []
  intro l₃ l₄
  induction l generalizing l₁ l₂ l₃ l₄
  · rename_i sz k' v' l r ih₁ ih₂
    simp only [applyPartition.go]
    split <;> rename_i hcmp
    · simp only [List.cons_append, List.append_assoc, List.append_nil]
      rw [ih₁]
      simp only [← List.append_assoc l₃]
      rw [ih₁]
      simp
    · simp
    · simp only [List.append_assoc, List.nil_append]
      rw [ih₂]
      simp only [← List.append_assoc l₃]
      rw [ih₂]
      simp
  · simp [applyPartition.go]

theorem explore_eq_applyPartition [Ord α] {k : α → Ordering} (init : δ) (l : Impl α β)
    (f : δ → ExplorationStep α β k → δ)
    (hfr : ∀ {k hk v ll c rr r init}, f (f init (.lt k hk v r)) (.eq ll c rr) = f init (.eq ll c (rr ++ ⟨k, v⟩ :: r)))
    (hfl : ∀ {k hk v ll c rr l init}, f (f init (.gt l k hk v)) (.eq ll c rr) = f init (.eq (l ++ ⟨k, v⟩ :: ll) c rr))
    :
    explore k init f l = applyPartition k l fun l c _ r => f init (.eq l c r) := by
  rw [applyPartition]
  suffices ∀ L, (h : L.contains' k → l.contains' k) →
    explore k init f l = applyPartition.go k L (fun l_1 c x r => f init (eq l_1 c r)) [] l h [] from this l id
  intro L hL
  induction l generalizing init
  · rename_i sz k' v' l r ih₁ ih₂
    rw [explore, applyPartition.go]
    split <;> rename_i hcmp
    · simp [hcmp, contains'] at hL
      rw [ih₁ _ hL]
      conv => rhs; rw [applyPartition_go_step]
      simp
      congr
      ext ll c hc rr
      apply hfr
    · simp
    · simp [hcmp, contains'] at hL
      rw [ih₂ _ hL]
      conv => rhs; rw [applyPartition_go_step]
      simp
      congr
      ext ll c hc rr
      apply hfl
  · simp [explore, applyPartition.go]

/-- General "update the mapping for a given key" function. -/
def updateCell [Ord α] (k : α) (f : Cell α β (compare k) → Cell α β (compare k))
    (l : Impl α β) (hl : Balanced l) : TreeB α β (l.size - 1) (l.size + 1) :=
  match l with
  | leaf => match (f .empty).inner with
            | none => ⟨.leaf, by tree_tac, by tree_tac, by tree_tac⟩
            | some ⟨k', v'⟩ => ⟨.inner 1 k' v' .leaf .leaf, by tree_tac, by tree_tac, by tree_tac⟩
  | inner sz ky y l r =>
    match h : compare k ky with
    | .lt =>
        let ⟨newL, h₁, h₂, h₃⟩ := updateCell k f l (by tree_tac)
        ⟨balance ky y newL r (by tree_tac) (by tree_tac) (by tree_tac), by tree_tac, by tree_tac,
          by tree_tac⟩
    | .eq => match (f (.ofEq ky y h)).inner with
             | none =>
               ⟨glue l r (by tree_tac) (by tree_tac) (by tree_tac), by tree_tac, by tree_tac,
                  by tree_tac⟩
             | some ⟨ky', y'⟩ => ⟨.inner sz ky' y' l r, by tree_tac, by tree_tac, by tree_tac⟩
    | .gt =>
        let ⟨newR, h₁, h₂, h₃⟩ := updateCell k f r (by tree_tac)
        ⟨balance ky y l newR (by tree_tac) (by tree_tac) (by tree_tac), by tree_tac, by tree_tac,
          by tree_tac⟩

/-!
## Model functions
-/

/-- Model implementation of the `contains` function. -/
def containsₘ [Ord α] (k : α) (l : Impl α β) : Bool :=
  applyCell k l fun c _ => c.contains

/-- Model implementation of the `get?` function. -/
def get?ₘ [Ord α] [OrientedOrd α] [LawfulEqOrd α] (k : α) (l : Impl α β) : Option (β k) :=
  applyCell k l fun c _ => c.get?

/-- Model implementation of the `get?ₘ` function. -/
def getₘ [Ord α] [OrientedOrd α] [LawfulEqOrd α] (k : α) (l : Impl α β) (h : l.contains k = true) : β k :=
  applyCell k l fun c hc => c.get (by simp_all [contains'_compare])

/-- Model implementation of the `insert` function. -/
def insertₘ [Ord α] (k : α) (v : β k) (l : Impl α β) (h : l.Balanced) : Impl α β :=
  updateCell k (fun _ => .of k v) l h |>.impl

/-- Preliminary model implementation of the `lookupGE` function. -/
def lookupGEₘ' [Ord α] (k : α) (l : Impl α β) : Option ((a : α) × β a) :=
  explore (compare k) none (fun sofar step =>
    match step with
    | .lt ky _ y _ => some ⟨ky, y⟩
    | .eq _ c r => c.inner.or r.head? |>.or sofar
    | .gt _ _ _ _ => sofar) l

/-- Model implementation of the `lookupGE` function. -/
def lookupGEₘ [Ord α] (k : α) (l : Impl α β) : Option ((a : α) × β a) :=
  applyPartition (compare k) l fun _ c _ r => c.inner.or r.head?

/-- Internal implementation detail of the ordered set -/
def min?ₘ' [Ord α] (l : Impl α β) : Option ((a : α) × β a) :=
  explore (fun (_ : α) => .lt) none (fun sofar step =>
    match step with
    | .lt ky _ y _ => some ⟨ky, y⟩
    | .eq _ _ r => r.head?.or sofar) l

/-- Internal implementation detail of the ordered set -/
def min?ₘ [Ord α] (l : Impl α β) : Option ((a : α) × β a) :=
  applyPartition (fun (_ : α) => .lt) l fun _ _ _ r => r.head?

/-!
## Helper theorems for reasoning with key-value pairs
-/

theorem balanceLSlow_pair_congr {k : α} {v : β k} {k' : α} {v' : β k'}
    (h : (⟨k, v⟩ : (a : α) × β a) = ⟨k', v'⟩) {l l' r r' : Impl α β}
    (hl : l = l') (hr : r = r') :
    balanceLSlow k v l r = balanceLSlow k' v' l' r' := by
  cases h; cases hl; cases hr; rfl

theorem balanceRSlow_pair_congr {k : α} {v : β k} {k' : α} {v' : β k'}
    (h : (⟨k, v⟩ : (a : α) × β a) = ⟨k', v'⟩) {l l' r r' : Impl α β}
    (hl : l = l') (hr : r = r') :
    balanceRSlow k v l r = balanceRSlow k' v' l' r' := by
  cases h; cases hl; cases hr; rfl

/-!
## Equivalence of function to model functions
-/

theorem contains_eq_containsₘ [Ord α] (k : α) (l : Impl α β) :
    l.contains k = l.containsₘ k := by
  simp only [containsₘ]
  induction l
  · simp only [contains, applyCell]
    split <;> rename_i hcmp₁ <;> split <;> rename_i hcmp₂ <;> try (simp [hcmp₁] at hcmp₂; done)
    all_goals simp_all
  · simp [contains, applyCell]

theorem get?_eq_get?ₘ [Ord α] [OrientedOrd α] [LawfulEqOrd α] (k : α) (l : Impl α β) :
    l.get? k = l.get?ₘ k := by
  simp only [get?ₘ]
  induction l
  · simp only [applyCell, get?]
    split <;> rename_i hcmp₁ <;> split <;> rename_i hcmp₂ <;> try (simp [hcmp₁] at hcmp₂; done)
    all_goals simp_all [Cell.get?, Cell.ofEq]
  · simp [get?, applyCell]

theorem lookupGE_eq_lookupGEₘ' [Ord α] {k : α} {l : Impl α β} :
    l.lookupGE k = l.lookupGEₘ' k := by
  rw [lookupGE, lookupGEₘ']
  suffices ∀ o, lookupGE.go k o l = explore (compare k) o _ l from this none
  intro o
  induction l generalizing o
  · rename_i sz k' v' l r ih₁ ih₂
    rw [lookupGE.go, explore]
    split <;> rename_i hcmp <;> split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    all_goals simp_all
  · simp [lookupGE.go, explore]

theorem lookupGEₘ'_eq_lookupGEₘ [Ord α] {k : α} {l : Impl α β} :
    l.lookupGEₘ' k = l.lookupGEₘ k := by
  rw [lookupGEₘ', explore_eq_applyPartition, lookupGEₘ]
  · simp only [Option.or_none]
  · intros k hcmp v ll c rr r init
    simp
    cases c.inner <;> simp
  · intros k hcmp v ll c rr l init
    simp

theorem min?_eq_min?ₘ' [Ord α] {l : Impl α β} : l.min? = l.min?ₘ' := by
  rw [min?ₘ']
  induction l using min?.induct <;> simp_all [min?, explore]

theorem min?ₘ'_eq_min?ₘ [Ord α] {l : Impl α β} : l.min?ₘ' = l.min?ₘ := by
  rw [min?ₘ', explore_eq_applyPartition, min?ₘ] <;> simp

theorem min?_eq_min?ₘ [Ord α] {l : Impl α β} : l.min? = l.min?ₘ := by
  rw [min?_eq_min?ₘ', min?ₘ'_eq_min?ₘ]

theorem lookupGE_eq_lookupGEₘ [Ord α] {k : α} {l : Impl α β} :
    l.lookupGE k = l.lookupGEₘ k := by
  rw [lookupGE_eq_lookupGEₘ', lookupGEₘ'_eq_lookupGEₘ]

theorem balanceL_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inl hlr.erase) := by
  rw [balanceL_eq_balanceLErase, balanceLErase_eq_balanceLSlow,
    balanceLSlow_eq_balanceSlow hlb hrb hlr.erase, balance_eq_balanceSlow]

theorem balanceR_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inr hlr.erase) := by
  rw [balanceR_eq_balanceRErase, balanceRErase_eq_balanceRSlow,
    balanceRSlow_eq_balanceSlow hlb hrb hlr.erase, balance_eq_balanceSlow]

theorem balanceLErase_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceLErase k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inl hlr) := by
  rw [balanceLErase_eq_balanceLSlow,
    balanceLSlow_eq_balanceSlow hlb hrb hlr, balance_eq_balanceSlow]

theorem balanceRErase_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceRErase k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inr hlr) := by
  rw [balanceRErase_eq_balanceRSlow,
    balanceRSlow_eq_balanceSlow hlb hrb hlr, balance_eq_balanceSlow]

theorem balanceL_eq_balanceLSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balanceLSlow k v l r := by
  rw [balanceL_eq_balanceLErase, balanceLErase_eq_balanceLSlow]

theorem balanceR_eq_balanceRSlow {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balanceRSlow k v l r := by
  rw [balanceR_eq_balanceRErase, balanceRErase_eq_balanceRSlow]

theorem minView_k_eq_minViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (minView k v l r hl hr hlr).k = (minViewSlow k v l r).k := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;> simp_all [minView, minViewSlow]

theorem minView_kv_eq_minViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (⟨(minView k v l r hl hr hlr).k, (minView k v l r hl hr hlr).v⟩ : (a : α) × β a) =
      ⟨(minViewSlow k v l r).k, (minViewSlow k v l r).v⟩ := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;>
    simp_all [minView, minViewSlow]

theorem minView_tree_impl_eq_minViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (minView k v l r hl hr hlr).tree.impl = (minViewSlow k v l r).tree := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;>
    simp_all [minView, minViewSlow, balanceRErase_eq_balanceRSlow]

theorem maxView_k_eq_maxViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).k = (maxViewSlow k v l r).k := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;> simp_all [maxView, maxViewSlow]

theorem maxView_kv_eq_maxViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (⟨(maxView k v l r hl hr hlr).k, (maxView k v l r hl hr hlr).v⟩ : (a : α) × β a) =
      ⟨(maxViewSlow k v l r).k, (maxViewSlow k v l r).v⟩ := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;>
    simp_all [maxView, maxViewSlow]

theorem maxView_tree_impl_eq_maxViewSlow {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).tree.impl = (maxViewSlow k v l r).tree := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;>
    simp_all [maxView, maxViewSlow, balanceLErase_eq_balanceLSlow]

theorem glue_eq_glueSlow {l r : Impl α β} {hl hr hlr} :
    glue l r hl hr hlr = glueSlow l r := by
  rw [glue.eq_def, glueSlow.eq_def]
  split; simp
  split; simp
  dsimp only
  split
  · simpa [*, balanceLErase_eq_balanceLSlow] using balanceLSlow_pair_congr
      minView_kv_eq_minViewSlow rfl minView_tree_impl_eq_minViewSlow
  · simpa [*, balanceRErase_eq_balanceRSlow] using balanceRSlow_pair_congr
      maxView_kv_eq_maxViewSlow maxView_tree_impl_eq_maxViewSlow rfl

theorem insert_eq_insertSlow [Ord α] {k : α} {v : β k} {l : Impl α β} {h} :
    (insert k v l h).impl = insertSlow k v l := by
  induction l, h using insert.induct k v <;>
    simp_all [insert, insertSlow, balanceL_eq_balanceLSlow, balanceR_eq_balanceRSlow]

theorem insert_eq_insertₘ [Ord α] {k : α} {v : β k} {l : Impl α β} {h} :
    (insert k v l h).impl = insertₘ k v l h := by
  simp only [insertₘ]
  induction l
  · simp only [insert, updateCell]
    split <;> rename_i hcmp <;> split <;> rename_i hcmp' <;> try (simp [hcmp] at hcmp'; done)
    all_goals simp_all [balanceL_eq_balance, balanceR_eq_balance]
  · simp [insert, insertₘ, updateCell]

theorem insertSlow_eq_insertₘ [Ord α] {k : α} {v : β k} {l : Impl α β} (h : l.Balanced) :
    insertSlow k v l = insertₘ k v l h := by
  rw [← insert_eq_insertSlow (h := h), insert_eq_insertₘ]

end Impl

end Std.DTreeMap.Internal
