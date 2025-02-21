/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.WF.Defs
import Std.Data.DTreeMap.Internal.Cell

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

/-- Internal implementation detail of the tree map -/
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
  induction l <;> simp_all only [contains', contains] <;> rfl

/-- General tree-traversal function. Internal implementation detail of the tree map -/
def applyPartition [Ord α] (k : α → Ordering) (l : Impl α β)
    (f : List ((a : α) × β a) → (c : Cell α β k) → (l.contains' k → c.contains) → List ((a : α) × β a) → δ) : δ :=
  go [] l id []
where
  go (ll : List ((a : α) × β a)) (m : Impl α β) (hm : l.contains' k → m.contains' k) (rr : List ((a : α) × β a)) : δ :=
  match m with
  | .leaf => f ll .empty (by simp_all [contains']) rr
  | .inner _ k' v' l r =>
    match h : k k' with
    | .lt =>
      go ll l (fun hc => have := hm hc; by rw [← this, contains']; simp_all)
        (⟨k', v'⟩ :: r.toListModel ++ rr)
    | .eq => f (ll ++ l.toListModel) (.ofEq k' v' h) (by simp) (r.toListModel ++ rr)
    | .gt =>
      go (ll ++ l.toListModel ++ [⟨k', v'⟩]) r
        (fun hc => have := hm hc; by rw [← this, contains']; simp_all) rr

/-- Internal implementation detail of the tree map -/
def applyCell [Ord α] (k : α) (l : Impl α β)
    (f : (c : Cell α β (compare k)) → (l.contains' (compare k) → c.contains) → δ) : δ :=
  match l with
  | .leaf => f .empty (by simp [contains'])
  | .inner _ k' v' l r =>
    match hcmp : compare k k' with
    | .lt => applyCell k l (fun c h => f c fun h' => h (by simpa [contains', hcmp] using h'))
    | .eq => f (.ofEq k' v' hcmp) (by simp)
    | .gt => applyCell k r (fun c h => f c fun h' => h (by simpa [contains', hcmp] using h'))

/-- Internal implementation detail of the tree map -/
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
Internal implementation detail of the tree map
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

/-- General tree-traversal function. Internal implementation detail of the tree map -/
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
    split
    · simp only [List.cons_append, List.append_assoc, List.append_nil]
      simp only [ih₁, ← List.append_assoc l₃]
      simp
    · simp
    · simp only [List.append_assoc, List.nil_append]
      simp only [ih₂, ← List.append_assoc l₃]
      simp
  · simp [applyPartition.go]

theorem explore_eq_applyPartition [Ord α] {k : α → Ordering} (init : δ) (l : Impl α β)
    (f : δ → ExplorationStep α β k → δ)
    (hfr : ∀ {k hk v ll c rr r init}, f (f init (.lt k hk v r)) (.eq ll c rr) = f init (.eq ll c (rr ++ ⟨k, v⟩ :: r)))
    (hfl : ∀ {k hk v ll c rr l init}, f (f init (.gt l k hk v)) (.eq ll c rr) = f init (.eq (l ++ ⟨k, v⟩ :: ll) c rr)) :
    explore k init f l = applyPartition k l fun l c _ r => f init (.eq l c r) := by
  rw [applyPartition]
  suffices ∀ L, (h : L.contains' k → l.contains' k) →
    explore k init f l = applyPartition.go k L (fun l_1 c x r => f init (eq l_1 c r)) [] l h [] from this l id
  intro L hL
  induction l generalizing init
  · rename_i sz k' v' l r ih₁ ih₂
    rw [explore, applyPartition.go]
    split <;> rename_i hcmp
    · simp only [hcmp, contains'] at hL
      rw [ih₁ _ hL]
      conv => rhs; rw [applyPartition_go_step]
      simp only [List.nil_append, List.append_nil]
      congr
      ext ll c hc rr
      apply hfr
    · simp
    · simp only [hcmp, contains'] at hL
      rw [ih₂ _ hL]
      conv => rhs; rw [applyPartition_go_step]
      simp only [List.nil_append, List.append_assoc, List.singleton_append, List.append_nil]
      congr
      ext ll c hc rr
      apply hfl
  · simp [explore, applyPartition.go]

/--
General "update the mapping for a given key" function.
Internal implementation detail of the tree map
-/
def updateCell [Ord α] (k : α) (f : Cell α β (compare k) → Cell α β (compare k))
    (l : Impl α β) (hl : Balanced l) : SizedBalancedTree α β (l.size - 1) (l.size + 1) :=
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

/--
Model implementation of the `contains` function.
Internal implementation detail of the tree map
-/
def containsₘ [Ord α] (k : α) (l : Impl α β) : Bool :=
  applyCell k l fun c _ => c.contains

/--
Model implementation of the `get?` function.
Internal implementation detail of the tree map
-/
def get?ₘ [Ord α] [OrientedOrd α] [LawfulEqOrd α] (k : α) (l : Impl α β) : Option (β k) :=
  applyCell k l fun c _ => c.get?

/--
Model implementation of the `insert` function.
Internal implementation detail of the tree map
-/
def insertₘ [Ord α] (k : α) (v : β k) (l : Impl α β) (h : l.Balanced) : Impl α β :=
  updateCell k (fun _ => .of k v) l h |>.impl

/--
Model implementation of the `erase` function.
Internal implementation detail of the tree map
-/
def eraseₘ [Ord α] (k : α) (t : Impl α β) (h : t.Balanced) : Impl α β :=
  updateCell k (fun _ => .empty) t h |>.impl

/--
Model implementation of the `insertIfNew` function.
Internal implementation detail of the tree map
-/
def insertIfNewₘ [Ord α] (k : α) (v : β k) (l : Impl α β) (h : l.Balanced) : Impl α β :=
  updateCell k (fun
    | ⟨.none, _⟩ => .of k v
    | c => c) l h |>.impl

/--
Model implementation of the `alter` function.
Internal implementation detail of the tree map
-/
def alterₘ [Ord α] [OrientedOrd α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k))
    (t : Impl α β) (h : t.Balanced) : Impl α β :=
  updateCell k (·.alter f) t h |>.impl

namespace Const

variable {β : Type v}

/--
Model implementation of the `get?` function.
Internal implementation detail of the tree map
-/
def get?ₘ [Ord α] (k : α) (l : Impl α (fun _ => β)) : Option β :=
  applyCell k l fun c _ => Cell.Const.get? c

/--
Model implementation of the `alter` function.
Internal implementation detail of the tree map
-/
def alterₘ [Ord α] [OrientedOrd α] (k : α) (f : Option β → Option β)
    (t : Impl α (fun _ => β)) (h : t.Balanced) : Impl α (fun _ => β) :=
  updateCell k (Cell.Const.alter f) t h |>.impl

end Const

/-!
## Helper theorems for reasoning with key-value pairs
-/

theorem balanceL!_pair_congr {k : α} {v : β k} {k' : α} {v' : β k'}
    (h : (⟨k, v⟩ : (a : α) × β a) = ⟨k', v'⟩) {l l' r r' : Impl α β}
    (hl : l = l') (hr : r = r') :
    balanceL! k v l r = balanceL! k' v' l' r' := by
  cases h; cases hl; cases hr; rfl

theorem balanceR!_pair_congr {k : α} {v : β k} {k' : α} {v' : β k'}
    (h : (⟨k, v⟩ : (a : α) × β a) = ⟨k', v'⟩) {l l' r r' : Impl α β}
    (hl : l = l') (hr : r = r') :
    balanceR! k v l r = balanceR! k' v' l' r' := by
  cases h; cases hl; cases hr; rfl

/-!
## Equivalence of function to model functions
-/

theorem contains_eq_containsₘ [Ord α] (k : α) (l : Impl α β) :
    l.contains k = l.containsₘ k := by
  simp only [containsₘ]
  induction l
  · simp only [contains, applyCell]
    split <;> split <;> simp_all
  · simp [contains, applyCell]

theorem get?_eq_get?ₘ [Ord α] [OrientedOrd α] [LawfulEqOrd α] (k : α) (l : Impl α β) :
    l.get? k = l.get?ₘ k := by
  simp only [get?ₘ]
  induction l
  · simp only [applyCell, get?]
    split <;> rename_i hcmp₁ <;> split <;> rename_i hcmp₂ <;> try (simp [hcmp₁] at hcmp₂; done)
    all_goals simp_all [Cell.get?, Cell.ofEq]
  · simp [get?, applyCell]

theorem balanceL_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inl hlr.erase) := by
  rw [balanceL_eq_balanceLErase, balanceLErase_eq_balanceL!,
    balanceL!_eq_balance! hlb hrb hlr.erase, balance_eq_balance!]

theorem balanceR_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inr hlr.erase) := by
  rw [balanceR_eq_balanceRErase, balanceRErase_eq_balanceR!,
    balanceR!_eq_balance! hlb hrb hlr.erase, balance_eq_balance!]

theorem balanceLErase_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceLErase k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inl hlr) := by
  rw [balanceLErase_eq_balanceL!,
    balanceL!_eq_balance! hlb hrb hlr, balance_eq_balance!]

theorem balanceRErase_eq_balance {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceRErase k v l r hlb hrb hlr = balance k v l r hlb hrb (Or.inr hlr) := by
  rw [balanceRErase_eq_balanceR!,
    balanceR!_eq_balance! hlb hrb hlr, balance_eq_balance!]

theorem balanceL_eq_balanceL! {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceL k v l r hlb hrb hlr = balanceL! k v l r := by
  rw [balanceL_eq_balanceLErase, balanceLErase_eq_balanceL!]

theorem balanceR_eq_balanceR! {k : α} {v : β k} {l r : Impl α β} {hlb hrb hlr} :
    balanceR k v l r hlb hrb hlr = balanceR! k v l r := by
  rw [balanceR_eq_balanceRErase, balanceRErase_eq_balanceR!]

theorem minView_k_eq_minView! {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (minView k v l r hl hr hlr).k = (minView! k v l r).k := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;> simp_all [minView, minView!]

theorem minView_kv_eq_minView! {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (⟨(minView k v l r hl hr hlr).k, (minView k v l r hl hr hlr).v⟩ : (a : α) × β a) =
      ⟨(minView! k v l r).k, (minView! k v l r).v⟩ := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;>
    simp_all [minView, minView!]

theorem minView_tree_impl_eq_minView! {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (minView k v l r hl hr hlr).tree.impl = (minView! k v l r).tree := by
  induction k, v, l, r, hl, hr, hlr using minView.induct <;>
    simp_all [minView, minView!, balanceRErase_eq_balanceR!]

theorem maxView_k_eq_maxView! {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).k = (maxView! k v l r).k := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;> simp_all [maxView, maxView!]

theorem maxView_kv_eq_maxView! {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (⟨(maxView k v l r hl hr hlr).k, (maxView k v l r hl hr hlr).v⟩ : (a : α) × β a) =
      ⟨(maxView! k v l r).k, (maxView! k v l r).v⟩ := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;>
    simp_all [maxView, maxView!]

theorem maxView_tree_impl_eq_maxView! {k : α} {v : β k} {l r : Impl α β} {hl hr hlr} :
    (maxView k v l r hl hr hlr).tree.impl = (maxView! k v l r).tree := by
  induction k, v, l, r, hl, hr, hlr using maxView.induct <;>
    simp_all [maxView, maxView!, balanceLErase_eq_balanceL!]

theorem glue_eq_glue! {l r : Impl α β} {hl hr hlr} :
    glue l r hl hr hlr = glue! l r := by
  rw [glue.eq_def, glue!.eq_def]
  split
  · simp
  split
  · simp
  split
  · simpa [*, balanceLErase_eq_balanceL!] using balanceL!_pair_congr
      minView_kv_eq_minView! rfl minView_tree_impl_eq_minView!
  · simpa [*, balanceRErase_eq_balanceR!] using balanceR!_pair_congr
      maxView_kv_eq_maxView! maxView_tree_impl_eq_maxView! rfl

theorem insert_eq_insert! [Ord α] {k : α} {v : β k} {l : Impl α β} {h} :
    (insert k v l h).impl = insert! k v l := by
  induction l, h using insert.induct k v <;>
    simp_all [insert, insert!, balanceL_eq_balanceL!, balanceR_eq_balanceR!]

theorem insert_eq_insertₘ [Ord α] {k : α} {v : β k} {l : Impl α β} {h} :
    (insert k v l h).impl = insertₘ k v l h := by
  simp only [insertₘ]
  induction l
  · simp only [insert, updateCell]
    split <;> split <;> simp_all [balanceL_eq_balance, balanceR_eq_balance]
  · simp [insert, insertₘ, updateCell]

theorem insert!_eq_insertₘ [Ord α] {k : α} {v : β k} {l : Impl α β} (h : l.Balanced) :
    insert! k v l = insertₘ k v l h := by
  rw [← insert_eq_insert! (h := h), insert_eq_insertₘ]

theorem erase_eq_erase! [Ord α] {k : α} {t : Impl α β} {h} :
    (erase k t h).impl = erase! k t := by
  induction t, h using erase.induct k <;>
    simp_all [erase, erase!, balanceLErase_eq_balanceL!, balanceRErase_eq_balanceR!,
      glue_eq_glue!]

theorem erase_eq_eraseₘ [Ord α] {k : α} {t : Impl α β} {h} :
    (erase k t h).impl = eraseₘ k t h := by
  simp only [eraseₘ]
  induction t
  · simp only [erase, updateCell]
    split <;> split <;> simp_all [balanceLErase_eq_balance, balanceRErase_eq_balance]
  · simp [erase, eraseₘ, updateCell]

theorem erase!_eq_eraseₘ [Ord α] {k : α} {t : Impl α β} (h : t.Balanced) :
    erase! k t = eraseₘ k t h := by
  rw [← erase_eq_erase! (h := h), erase_eq_eraseₘ]

theorem containsThenInsert!_fst_eq_containsThenInsert_fst [Ord α] (t : Impl α β) (htb : t.Balanced) (a : α) (b : β a) :
    (t.containsThenInsert! a b).1 = (t.containsThenInsert a b htb).1 := by
  cases t <;> simp [containsThenInsert, containsThenInsert.size,
    containsThenInsert!, containsThenInsert!.size, insert!_eq_insertₘ, insert_eq_insertₘ, htb]

theorem containsThenInsert!_snd_eq_containsThenInsert_snd [Ord α] (t : Impl α β) (htb : t.Balanced) (a : α) (b : β a) :
    (t.containsThenInsert! a b).2 = (t.containsThenInsert a b htb).2.impl := by
  cases t <;> simp [containsThenInsert, containsThenInsert!, insert!_eq_insertₘ htb,
    insert_eq_insertₘ]

theorem containsThenInsert_snd_eq_insertₘ [Ord α] (t : Impl α β) (htb : t.Balanced) (a : α) (b : β a) :
    (t.containsThenInsert a b htb).2.impl = t.insertₘ a b htb := by
  rw [containsThenInsert, insert_eq_insertₘ]

theorem containsThenInsert!_snd_eq_insertₘ [Ord α] (t : Impl α β) (htb : t.Balanced) (a : α) (b : β a) :
    (t.containsThenInsert! a b).2 = t.insertₘ a b htb := by
  rw [containsThenInsert!_snd_eq_containsThenInsert_snd, containsThenInsert_snd_eq_insertₘ]

theorem insertIfNew_eq_insertIfNew! [Ord α] {k : α} {v : β k} {l : Impl α β} {h} :
    (insertIfNew k v l h).impl = insertIfNew! k v l := by
  simp only [insertIfNew, insertIfNew!]
  split
  · rfl
  · simp [insert_eq_insert!]

theorem containsThenInsertIfNew!_fst_eq_containsThenInsertIfNew_fst [Ord α] (t : Impl α β) (htb : t.Balanced) (a : α) (b : β a) :
    (t.containsThenInsertIfNew! a b).1 = (t.containsThenInsertIfNew a b htb).1 := by
  simp only [containsThenInsertIfNew!, containsThenInsertIfNew]
  split <;> rfl

theorem containsThenInsertIfNew!_snd_eq_containsThenInsertIfNew_snd [Ord α] (t : Impl α β) (htb : t.Balanced) (a : α) (b : β a) :
    (t.containsThenInsertIfNew! a b).2 = (t.containsThenInsertIfNew a b htb).2.impl := by
  simp only [containsThenInsertIfNew!, containsThenInsertIfNew]
  split
  · rfl
  · simp [insert!_eq_insertₘ, insert_eq_insertₘ, htb]

theorem containsThenInsertIfNew_fst_eq_containsₘ [Ord α] [TransOrd α] (t : Impl α β) (htb : t.Balanced)
    (a : α) (b : β a) : (t.containsThenInsertIfNew a b htb).1 = t.containsₘ a := by
  simp only [containsThenInsertIfNew, contains_eq_containsₘ]
  split <;> next h => simp only [h]

theorem containsThenInsertIfNew_snd_eq_insertIfNew [Ord α] (t : Impl α β) (htb : t.Balanced) (a : α) (b : β a) :
    (t.containsThenInsertIfNew a b htb).2 = (t.insertIfNew a b htb) := by
  rw [containsThenInsertIfNew, insertIfNew]
  split <;> rfl

theorem containsThenInsertIfNew!_fst_eq_containsₘ [Ord α] [TransOrd α] (t : Impl α β)
    (a : α) (b : β a) : (t.containsThenInsertIfNew! a b).1 = t.containsₘ a := by
  simp only [containsThenInsertIfNew!, contains_eq_containsₘ]
  split <;> next h => simp only [h]

theorem containsThenInsertIfNew!_snd_eq_insertIfNew! [Ord α] (t : Impl α β) (a : α) (b : β a) :
    (t.containsThenInsertIfNew! a b).2 = t.insertIfNew! a b:= by
  rw [containsThenInsertIfNew!, insertIfNew!]
  split <;> rfl

namespace Const

variable {β : Type v}

theorem get?_eq_get?ₘ [Ord α] (k : α) (l : Impl α (fun _ => β)) :
    Const.get? k l = Const.get?ₘ k l := by
  simp only [Const.get?ₘ]
  induction l
  · simp only [applyCell, Const.get?]
    split <;> rename_i hcmp₁ <;> split <;> rename_i hcmp₂ <;> try (simp [hcmp₁] at hcmp₂; done)
    all_goals simp_all [Cell.Const.get?, Cell.ofEq]
  · simp [Const.get?, applyCell]

end Const

end Impl

end Std.DTreeMap.Internal
