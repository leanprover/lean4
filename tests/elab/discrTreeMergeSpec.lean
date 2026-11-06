module
public import Lean.Meta.DiscrTree.Basic
import all Lean.Meta.DiscrTree.Basic
import all Lean.Meta.DiscrTree.Types
import all Lean.Expr
import all Lean.Data.Name
import all Init.Data.Array.QSort.Basic
import all Init.Data.Array.BinSearch
import Init.Data.Vector.Perm
import Init.Data.Array.Perm
import Std.Data.HashMap.Lemmas
meta import Lean.Meta.DiscrTree.Basic

/-!
Verifies that merging per-module discrimination trees (`DiscrTree.ofModuleRoots` applied to the
`DiscrTree.moduleRootsOf` of each module) agrees with inserting the entries of all modules in module
order with `DiscrTree.insertKeyValue`: forcing all `lazy` nodes of the trie under any root key gives
exactly the trie under this key after sequential insertion (`ofModuleRoots_spec`). Both sides are
characterized by the relation `Den` between entries and tries: `insertAux_den` for sequential
insertion and `mergeTries_spec` for the merge.

`==` on values must be symmetric and transitive: the merge deduplicates the values of a module
before folding them into those of earlier modules, which loses values when `==` is not transitive
(see the example at the end). As the operations of `PersistentHashMap` are `partial`,
`ofModuleRoots_spec` assumes their lookup laws (`MapLaws`). Along the way, `Array.qsort` is shown to
return a sorted permutation, as in `constTrieLookupSpec.lean`.
-/

open Lean Meta DiscrTree
/-! ## `Array.qsort` (copied from `constTrieLookupSpec.lean`) -/

namespace DiscrTreeMergeSpec.QS
variable {α : Type _} {n : Nat}

/-- Every element of `a`'s segment `[lo, hi]` occurs in `b`'s segment. -/
def SegSub (a b : Vector α n) (lo hi : Nat) : Prop :=
  ∀ k (hk : k < n), lo ≤ k → k ≤ hi → ∃ k', ∃ hk' : k' < n, lo ≤ k' ∧ k' ≤ hi ∧ a[k] = b[k']

/-- `b` is a permutation of `a` that only permutes the segment `[lo, hi]`. -/
structure Rel (a b : Vector α n) (lo hi : Nat) : Prop where
  perm : b.Perm a
  out : ∀ k (hk : k < n), (k < lo ∨ hi < k) → b[k] = a[k]
  sub : SegSub a b lo hi
  sup : SegSub b a lo hi

theorem Rel.refl (a : Vector α n) (lo hi) : Rel a a lo hi :=
  ⟨.refl _, fun _ _ _ => Eq.refl _, fun k hk h1 h2 => ⟨k, hk, h1, h2, rfl⟩,
    fun k hk h1 h2 => ⟨k, hk, h1, h2, rfl⟩⟩

theorem SegSub.trans {a b c : Vector α n} (h₁ : SegSub a b lo hi) (h₂ : SegSub b c lo hi) :
    SegSub a c lo hi := by
  intro k hk h1 h2
  obtain ⟨k', hk', h1', h2', e⟩ := h₁ k hk h1 h2
  obtain ⟨k'', hk'', h1'', h2'', e'⟩ := h₂ k' hk' h1' h2'
  exact ⟨k'', hk'', h1'', h2'', e.trans e'⟩

theorem Rel.trans {a b c : Vector α n} (h₁ : Rel a b lo hi) (h₂ : Rel b c lo hi) : Rel a c lo hi :=
  ⟨h₂.perm.trans h₁.perm, fun k hk h => (h₂.out k hk h).trans (h₁.out k hk h),
   h₁.sub.trans h₂.sub, h₂.sup.trans h₁.sup⟩

theorem Rel.widen {a b : Vector α n} (h : Rel a b lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    Rel a b lo' hi' := by
  refine ⟨h.perm, fun k hk h' => h.out k hk (by omega), fun k hk h1 h2 => ?_, fun k hk h1 h2 => ?_⟩
  · by_cases hin : lo ≤ k ∧ k ≤ hi
    · obtain ⟨k', hk', _, _, e⟩ := h.sub k hk hin.1 hin.2
      exact ⟨k', hk', by omega, by omega, e⟩
    · exact ⟨k, hk, h1, h2, (h.out k hk (by omega)).symm⟩
  · by_cases hin : lo ≤ k ∧ k ≤ hi
    · obtain ⟨k', hk', _, _, e⟩ := h.sup k hk hin.1 hin.2
      exact ⟨k', hk', by omega, by omega, e⟩
    · exact ⟨k, hk, h1, h2, h.out k hk (by omega)⟩

theorem Rel.swap (a : Vector α n) (i j : Nat) (hi : i < n) (hj : j < n)
    (h1 : lo ≤ i) (h2 : i ≤ hi') (h3 : lo ≤ j) (h4 : j ≤ hi') :
    Rel a (a.swap i j hi hj) lo hi' := by
  refine ⟨Vector.swap_perm hi hj, by grind, fun k hk g1 g2 => ?_, fun k hk g1 g2 => ?_⟩ <;>
    exact ⟨if k = i then j else if k = j then i else k, by grind, by grind, by grind, by grind⟩

variable (lt : α → α → Bool)

theorem loop_spec (lo hi : Nat) (hhi : hi < n) (pivot : α) (as : Vector α n) (i k : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi)
    (hp : as[hi] = pivot)
    (hl : ∀ x (hx : x < n), lo ≤ x → x < i → lt as[x] pivot)
    (hr : ∀ x (hx : x < n), i ≤ x → x < k → ¬lt as[x] pivot = true) :
    ∃ asL : Vector α n, ∃ m, ∃ hm : m < n,
      (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).2 = asL.swap m hi hm hhi ∧
      (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w).1.1 = m ∧
      Rel as asL lo (hi - 1) ∧ asL[hi] = pivot ∧ lo ≤ m ∧ m ≤ hi ∧
      (∀ x (hx : x < n), lo ≤ x → x < m → lt asL[x] pivot) ∧
      (∀ x (hx : x < n), m ≤ x → x < hi → ¬lt asL[x] pivot = true) := by
  induction as, i, k, ilo, ik, w using Array.qpartition.loop.induct lt lo hi hhi pivot with
  | case1 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop]; simp only [h, ↓reduceDIte, hlt, ↓reduceIte]
    -- `grind` is much slower with `ih` in context
    obtain ⟨asL, m, hm, e1, e2, hrel, hp', h1, h2, hl', hr'⟩ :=
      ih (by clear ih; grind) (by clear ih; grind) (by clear ih; grind)
    exact ⟨asL, m, hm, e1, e2,
      (Rel.swap as i k _ _ ilo (by omega) (by omega) (by omega)).trans hrel,
      hp', h1, h2, hl', hr'⟩
  | case2 as i k ilo ik w h hlt ih =>
    rw [Array.qpartition.loop]; simp only [h, ↓reduceDIte, hlt, ↓reduceIte, Bool.false_eq_true]
    exact ih hp hl (by clear ih; grind)
  | case3 as i k ilo ik w h =>
    rw [Array.qpartition.loop]; simp only [h, ↓reduceDIte]
    exact ⟨as, i, by omega, rfl, rfl, Rel.refl _ _ _, hp, ilo, by omega, hl, by grind⟩

variable (asymm : ∀ a b, lt a b = true → lt b a = false)
  (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
include asymm

omit asymm in
theorem Rel.ite_swap (c : Bool) (a : Vector α n) (i j : Nat) (hi : i < n) (hj : j < n)
    (h1 : lo ≤ i) (h2 : i ≤ hi') (h3 : lo ≤ j) (h4 : j ≤ hi') :
    Rel a (if c = true then a.swap i j hi hj else a) lo hi' := by
  split
  · exact Rel.swap _ _ _ _ _ h1 h2 h3 h4
  · exact Rel.refl _ _ _

omit asymm in
theorem after_loop (as as3 : Vector α n) (lo hi mid : Nat) (hhi : hi < n) (hrel : Rel as as3 lo hi)
    (hm1 : lo ≤ mid) (hm2 : mid < hi) (hmed : ¬lt (as3[mid]'(by omega)) as3[hi] = true) :
    let r := Array.qpartition.loop lt lo hi hhi as3[hi] as3 lo lo (by omega) (by omega) (by omega)
    Rel as r.2 lo hi ∧ r.1.1 < hi ∧
      (∀ x (hx : x < n), lo ≤ x → x < r.1.1 → lt r.2[x] (r.2[r.1.1]'(by have := r.1.2; omega))) ∧
      (∀ x (hx : x < n), r.1.1 < x → x ≤ hi →
        ¬lt r.2[x] (r.2[r.1.1]'(by have := r.1.2; omega)) = true) := by
  intro r
  obtain ⟨asL, m, hm, e1, e2, hrel', hp', h1, h2, hl', hr'⟩ :=
    loop_spec lt lo hi hhi as3[hi] as3 lo lo (by omega) (by omega) (by omega) rfl
      (fun x _ g1 g2 => absurd g2 (by omega)) (fun x _ g1 g2 => absurd g2 (by omega))
  unfold r
  simp only [e1, e2]
  have hmh : m < hi := by
    obtain ⟨k', hk', g1, g2, ee⟩ := hrel'.sub mid (by omega) hm1 (by omega)
    grind
  exact ⟨hrel.trans ((hrel'.widen (Nat.le_refl _) (by omega)).trans
    (Rel.swap _ _ _ _ _ h1 (by omega) (by omega) (by omega))), hmh, by grind, by grind⟩

theorem med_ite (a : Vector α n) (i j : Nat) (hi : i < n) (hj : j < n) :
    ¬lt (if lt a[i] a[j] = true then a.swap i j hi hj else a)[i]
      (if lt a[i] a[j] = true then a.swap i j hi hj else a)[j] = true := by
  grind

theorem qpartition_spec (as : Vector α n) (lo hi : Nat) (hlh : lo < hi) (hhi : hi < n) :
    let r := Array.qpartition as lt lo hi (by omega) (by omega) hhi
    Rel as r.2 lo hi ∧ r.1.1 < hi ∧
      (∀ x (hx : x < n), lo ≤ x → x < r.1.1 → lt r.2[x] (r.2[r.1.1]'(by have := r.1.2; omega))) ∧
      (∀ x (hx : x < n), r.1.1 < x → x ≤ hi →
        ¬lt r.2[x] (r.2[r.1.1]'(by have := r.1.2; omega)) = true) := by
  unfold Array.qpartition
  dsimp only
  apply after_loop lt as _ lo hi ((lo + hi) / 2) hhi _ (by omega) (by omega)
    (med_ite lt asymm _ _ _ _ _)
  refine (Rel.ite_swap _ _ _ _ _ _ ?_ ?_ ?_ ?_).trans ((Rel.ite_swap _ _ _ _ _ _ ?_ ?_ ?_ ?_).trans
    (Rel.ite_swap _ _ _ _ _ _ ?_ ?_ ?_ ?_)) <;> omega

def Sorted (v : Vector α n) (lo hi : Nat) : Prop :=
  ∀ i j (hj : j < n) (_ : lo ≤ i) (hij : i < j) (_ : j ≤ hi), ¬lt v[j] (v[i]'(by omega)) = true

include trans in
theorem sort_spec (as : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    Rel as (Array.qsort.sort lt as lo hi w hlo hhi) lo hi ∧
      Sorted lt (Array.qsort.sort lt as lo hi w hlo hhi) lo hi := by
  induction as, lo, hi, w, hlo, hhi using Array.qsort.sort.induct lt with
  | case1 as lo hi w hlo hhi h mid hmid as1 heq hge =>
    exfalso
    have := (qpartition_spec lt asymm as lo hi h hhi).2.1
    simp only [heq] at this; omega
  | case2 as lo hi w hlo hhi h mid hmid as1 heq hge ih1 _ ih2 =>
    have := qpartition_spec lt asymm as lo hi h hhi
    simp only [heq] at this
    obtain ⟨rp, hmh, pl, pr⟩ := this
    rw [Array.qsort.sort]; simp only [h, ↓reduceDIte, heq, hge]
    generalize hs2 : Array.qsort.sort lt as1 lo mid _ hlo _ = as2 at ih1 ih2 ⊢
    generalize hs3 : Array.qsort.sort lt as2 (mid + 1) hi _ _ hhi = as3 at ih2 ⊢
    obtain ⟨r2, s2⟩ := ih1
    obtain ⟨r3, s3⟩ := ih2
    refine ⟨rp.trans ((r2.widen (Nat.le_refl _) (by omega)).trans
      (r3.widen (by omega) (Nat.le_refl _))), ?_⟩
    have hmn : mid < n := by omega
    -- elements of the left part are below or equal to the pivot, those of the right part not below
    have L : ∀ x (hx : x < n), lo ≤ x → x ≤ mid → lt as3[x] as1[mid] ∨ as3[x] = as1[mid] := by
      intro x hx g1 g2
      obtain ⟨k', hk', h1', h2', e⟩ := r2.sup x hx g1 g2
      rw [r3.out x hx (by omega), e]
      by_cases ek : k' = mid
      · subst ek; exact .inr rfl
      · exact .inl (pl k' hk' h1' (by omega))
    have R : ∀ x (hx : x < n), mid + 1 ≤ x → x ≤ hi → ¬lt as3[x] as1[mid] = true := by
      intro x hx g1 g2
      obtain ⟨k', hk', h1', h2', e⟩ := r3.sup x hx g1 g2
      rw [e, r2.out k' hk' (by omega)]
      exact pr k' hk' (by omega) h2'
    intro i j hj g1 g2 g3
    by_cases hi' : mid + 1 ≤ i
    · exact s3 i j hj hi' g2 g3
    · by_cases hj' : j ≤ mid
      · rw [r3.out j hj (by omega), r3.out i (by omega) (by omega)]
        exact s2 i j hj g1 g2 hj'
      · intro hlt
        rcases L i (by omega) g1 (by omega) with h' | h'
        · exact R j hj (by omega) g3 (trans _ _ _ hlt h')
        · exact R j hj (by omega) g3 (h' ▸ hlt)
  | case3 as lo hi w hlo hhi h =>
    rw [Array.qsort.sort]; simp only [h, ↓reduceDIte]
    exact ⟨Rel.refl _ _ _, fun i j hj g1 g2 g3 => absurd g3 (by omega)⟩

include trans in
theorem qsort_spec (as : Array α) :
    (as.qsort lt).Perm as ∧
      ∀ i j (hj : j < (as.qsort lt).size) (hij : i < j),
        ¬lt (as.qsort lt)[j] ((as.qsort lt)[i]'(by omega)) = true := by
  unfold Array.qsort
  split
  · exact ⟨.refl _, by grind⟩
  · simp only [Nat.zero_le, Nat.min_eq_left, Nat.le_refl, Nat.max_eq_right]
    obtain ⟨r, s⟩ :=
      sort_spec lt asymm trans as.toVector 0 (as.size - 1) (by omega) (by omega) (by omega)
    exact ⟨by simpa using Vector.perm_iff_toArray_perm.1 r.perm, by grind [Sorted]⟩

end DiscrTreeMergeSpec.QS

/-! ## Keys are strictly ordered (adapted from Rob Simmons' discrimination tree model) -/

namespace DiscrTreeMergeSpec

deriving instance ReflBEq, LawfulBEq for Lean.Literal
deriving instance ReflBEq, LawfulBEq for Lean.FVarId
deriving instance ReflBEq, LawfulBEq for Key

theorem Name.quickCmpAux_swap : ∀ {n n' : Name}, n.quickCmpAux n' = (n'.quickCmpAux n).swap
  | .anonymous, n => by cases n <;> rfl
  | n, .anonymous => by cases n <;> rfl
  | .num .., .str .. => rfl
  | .str .., .num .. => rfl
  | .num p₁ n₁, .num p₂ n₂ => by
    simp only [Name.quickCmpAux]
    rw [Std.OrientedOrd.eq_swap (a := n₁)]
    cases compare n₂ n₁ <;> simp [Name.quickCmpAux_swap (n := p₁)]
  | .str p₁ s₁, .str p₂ s₂ => by
    simp only [Name.quickCmpAux]
    rw [Std.OrientedOrd.eq_swap (a := s₁)]
    cases compare s₂ s₁ <;> simp [Name.quickCmpAux_swap (n := p₁)]

theorem Name.quickCmpAux_eq_iff : ∀ {n n' : Name}, n.quickCmpAux n' = .eq ↔ n = n'
  | .anonymous, n => by cases n <;> simp [Name.quickCmpAux]
  | n, .anonymous => by cases n <;> simp [Name.quickCmpAux]
  | .num .., .str .. => by simp [Name.quickCmpAux]
  | .str .., .num .. => by simp [Name.quickCmpAux]
  | .num p₁ n₁, .num p₂ n₂ => by
    simp only [Name.quickCmpAux]; split <;> simp_all [Name.quickCmpAux_eq_iff]
  | .str p₁ s₁, .str p₂ s₂ => by
    simp only [Name.quickCmpAux]; split <;> simp_all [Name.quickCmpAux_eq_iff]

private theorem Name.quickCmpAux_num (p p' : Name) (n n' : Nat) :
    (Name.num p n).quickCmpAux (.num p' n') = (compare n n').then (p.quickCmpAux p') := by
  simp only [Name.quickCmpAux]; cases compare n n' <;> rfl

private theorem Name.quickCmpAux_str (p p' : Name) (s s' : String) :
    (Name.str p s).quickCmpAux (.str p' s') = (compare s s').then (p.quickCmpAux p') := by
  simp only [Name.quickCmpAux]; cases compare s s' <;> rfl

theorem Name.quickCmpAux_isLE_trans : ∀ {a b c : Name},
    (a.quickCmpAux b).isLE → (b.quickCmpAux c).isLE → (a.quickCmpAux c).isLE
  | .anonymous, b, c, _, _ => by cases c <;> simp [Name.quickCmpAux]
  | .num .., .anonymous, _, h, _ => by simp [Name.quickCmpAux] at h
  | .str .., .anonymous, _, h, _ => by simp [Name.quickCmpAux] at h
  | .num .., .num .., .anonymous, _, h => by simp [Name.quickCmpAux] at h
  | .num .., .str .., .anonymous, _, h => by simp [Name.quickCmpAux] at h
  | .str .., .str .., .anonymous, _, h => by simp [Name.quickCmpAux] at h
  | .str .., .num .., _, h, _ => by simp [Name.quickCmpAux] at h
  | .num .., .str .., .num .., _, h => by simp [Name.quickCmpAux] at h
  | .num .., .num .., .str .., _, _ => by simp [Name.quickCmpAux]
  | .num .., .str .., .str .., _, _ => by simp [Name.quickCmpAux]
  | .str .., .str .., .num .., _, h => by simp [Name.quickCmpAux] at h
  | .num p₁ n₁, .num p₂ n₂, .num p₃ n₃, hab, hbc => by
    simp only [Name.quickCmpAux_num, Ordering.isLE_then_iff_and] at *
    refine ⟨Std.TransOrd.isLE_trans hab.1 hbc.1, ?_⟩
    rcases hab.2 with h | h
    · exact .inl (Std.TransCmp.lt_of_lt_of_isLE h hbc.1)
    · rcases hbc.2 with h' | h'
      · exact .inl (Std.TransCmp.lt_of_isLE_of_lt hab.1 h')
      · exact .inr (Name.quickCmpAux_isLE_trans h h')
  | .str p₁ n₁, .str p₂ n₂, .str p₃ n₃, hab, hbc => by
    simp only [Name.quickCmpAux_str, Ordering.isLE_then_iff_and] at *
    refine ⟨Std.TransOrd.isLE_trans hab.1 hbc.1, ?_⟩
    rcases hab.2 with h | h
    · exact .inl (Std.TransCmp.lt_of_lt_of_isLE h hbc.1)
    · rcases hbc.2 with h' | h'
      · exact .inl (Std.TransCmp.lt_of_isLE_of_lt hab.1 h')
      · exact .inr (Name.quickCmpAux_isLE_trans h h')

instance : Std.TransCmp Name.quickCmpAux where
  eq_swap := Name.quickCmpAux_swap
  isLE_trans := Name.quickCmpAux_isLE_trans

theorem Name.quickCmp_eq_compareLex :
    Name.quickCmp = compareLex (compareOn Name.hash) Name.quickCmpAux := by
  funext a b
  simp only [Name.quickCmp, compareLex, compareOn]
  cases compare a.hash b.hash <;> rfl

instance : Std.TransCmp Name.quickCmp := by
  rw [Name.quickCmp_eq_compareLex]; infer_instance

theorem Name.quickLt_irrefl (n : Name) : n.quickLt n = false := by
  simp [Name.quickLt, Std.ReflCmp.compare_self]

theorem Name.quickLt_trans {a b c : Name} (h₁ : a.quickLt b) (h₂ : b.quickLt c) : a.quickLt c := by
  simp only [Name.quickLt, beq_iff_eq] at *
  exact Std.TransCmp.lt_trans h₁ h₂

theorem Name.quickCmp_swap {n n' : Name} : n.quickCmp n' = (n'.quickCmp n).swap :=
  Std.OrientedCmp.eq_swap

theorem Name.eq_of_not_quickLt {n n' : Name} (h₁ : n.quickLt n' = false)
    (h₂ : n'.quickLt n = false) : n = n' := by
  simp only [Name.quickLt, Name.quickCmp_swap (n := n'), beq_eq_false_iff_ne] at h₁ h₂
  have : n.quickCmp n' = .eq := by cases h : n.quickCmp n' <;> simp_all
  simp only [Name.quickCmp] at this
  split at this
  · exact Name.quickCmpAux_eq_iff.mp this
  · contradiction

theorem Literal.eq_of_not_lt {l l' : Literal} (h₁ : l.lt l' = false) (h₂ : l'.lt l = false) :
    l = l' := by
  cases l <;> cases l' <;> simp_all [Literal.lt] <;> grind

theorem Literal.lt_irrefl (l : Literal) : l.lt l = false := by
  cases l <;> simp [Literal.lt, Std.lt_irrefl]

theorem Literal.lt_trans {a b c : Literal} (h₁ : a.lt b) (h₂ : b.lt c) : a.lt c := by
  cases a <;> cases b <;> cases c <;> simp_all [Literal.lt] <;> grind

theorem Key.eq_of_not_lt {k k' : Key} (h₁ : k.lt k' = false) (h₂ : k'.lt k = false) : k = k' := by
  cases k <;> cases k' <;> simp_all [Key.lt, Key.ctorIdx]
  · exact Literal.eq_of_not_lt (by simpa [LT.lt] using h₁) (by simpa [LT.lt] using h₂)
  case fvar.fvar x _ y _ =>
    have := Name.eq_of_not_quickLt h₁.1 h₂.1
    cases x; cases y
    grind
  · have := Name.eq_of_not_quickLt h₁.1 h₂.1
    grind
  · have := Name.eq_of_not_quickLt h₁.1.1 h₂.1.1
    subst this
    have := h₁.1.2 rfl; have := h₂.1.2 rfl
    have : _ = _ := Nat.le_antisymm ‹_› ‹_›
    subst this
    have := h₁.2 rfl rfl; have := h₂.2 rfl rfl
    exact ⟨rfl, rfl, by omega⟩

theorem Key.lt_iff {a b : Key} : a < b ↔ Key.lt a b = true := Iff.rfl

private theorem Literal.lt_iff {a b : Literal} : a < b ↔ a.lt b = true := Iff.rfl

theorem Key.lt_irrefl (k : Key) : ¬ k < k := by
  rw [Key.lt_iff]
  cases k <;> simp [Key.lt, Name.quickLt_irrefl, Literal.lt_iff, Literal.lt_irrefl]

theorem Key.lt_trans {a b c : Key} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [Key.lt_iff] at *
  cases a <;> cases b <;> cases c <;>
    simp_all [Key.lt, Key.ctorIdx, Literal.lt_iff] <;>
    grind [Name.quickLt_trans, Literal.lt_trans]

theorem Key.lt_asymm {a b : Key} (h : a < b) : ¬ b < a :=
  fun h' => Key.lt_irrefl a (Key.lt_trans h h')

theorem Key.lt_total {a b : Key} (h : a ≠ b) : a < b ∨ b < a := by
  rw [Key.lt_iff, Key.lt_iff]
  cases h₁ : a.lt b <;> cases h₂ : b.lt a <;> simp_all
  exact h (Key.eq_of_not_lt h₁ h₂)

end DiscrTreeMergeSpec

/-! ## `insertVal` -/

namespace DiscrTreeMergeSpec
variable {α : Type}

section
variable [BEq α]

/-- `insertVal` on lists. -/
def insV : List α → α → List α
  | [], v => [v]
  | x :: xs, v => if v == x then v :: xs else x :: insV xs v

theorem insertVal_loop_toList (vs : Array α) (v : α) (i : Nat) (hi : i ≤ vs.size) :
    (insertVal.loop vs v i).toList = vs.toList.take i ++ insV (vs.toList.drop i) v := by
  fun_induction insertVal.loop vs v i with
  | case1 i h heq =>
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp [insV, heq, List.set_eq_take_append_cons_drop, h]
  | case2 i h heq ih =>
    rw [ih (by omega), List.drop_eq_getElem_cons (i := i) (by simpa using h)]
    simp [insV, heq, List.take_add_one, h]
  | case3 i h =>
    have : i = vs.size := by omega
    subst this
    rw [← Array.length_toList, List.take_length, List.drop_length]
    simp [insV]

theorem insertVal_toList (vs : Array α) (v : α) : (insertVal vs v).toList = insV vs.toList v := by
  simp [insertVal, insertVal_loop_toList]

theorem insertVal_eq (vs : Array α) (v : α) : insertVal vs v = (insV vs.toList v).toArray := by
  rw [← insertVal_toList]

theorem foldl_insertVal (L : List α) (vs : Array α) :
    L.foldl insertVal vs = (L.foldl insV vs.toList).toArray := by
  induction L generalizing vs with
  | nil => simp
  | cons v L ih => simp [ih, insertVal_toList]

theorem insV_ne_nil (A : List α) (v : α) : insV A v ≠ [] := by
  cases A <;> simp [insV] <;> split <;> simp

theorem foldl_insV_eq_nil {L A : List α} : L.foldl insV A = [] ↔ L = [] ∧ A = [] := by
  induction L generalizing A with
  | nil => simp
  | cons v L ih => simp [ih, insV_ne_nil]

theorem mem_insV {A : List α} {v x : α} : x ∈ insV A v → x ∈ A ∨ x = v := by
  induction A with
  | nil => simp [insV]
  | cons a A ih =>
    simp only [insV]; split
    · simp only [List.mem_cons]; rintro (rfl | h) <;> simp_all
    · simp only [List.mem_cons]
      rintro (rfl | h)
      · simp
      · rcases ih h with h | h <;> simp_all

theorem mem_insV_self (A : List α) (v : α) : v ∈ insV A v := by
  induction A with
  | nil => simp [insV]
  | cons a A ih => simp only [insV]; split <;> simp [ih]

end

section
variable [BEq α] [PartialEquivBEq α]

theorem insV_insV_of_beq {a b : α} (h : (a == b) = true) (A : List α) :
    insV (insV A a) b = insV A b := by
  induction A with
  | nil => simp [insV, BEq.symm h]
  | cons x A ih =>
    by_cases hax : (a == x) = true
    · simp [insV, hax, BEq.symm h, BEq.trans (BEq.symm h) hax]
    · have hbx : ¬(b == x) = true := fun hbx => hax (BEq.trans h hbx)
      simp [insV, hax, hbx, ih]

theorem exists_beq_insV {A : List α} {v : α} (hv : ∃ x ∈ A, (v == x) = true) (s : α) :
    ∃ x ∈ insV A s, (v == x) = true := by
  induction A with
  | nil => simp at hv
  | cons a A ih =>
    simp only [insV]
    obtain ⟨x, hx, hvx⟩ := hv
    rcases List.mem_cons.1 hx with rfl | hx
    · split
      · rename_i hsx
        exact ⟨s, by simp, BEq.trans hvx (BEq.symm hsx)⟩
      · exact ⟨x, by simp, hvx⟩
    · split
      · exact ⟨x, by simp [hx], hvx⟩
      · obtain ⟨y, hy, hvy⟩ := ih ⟨x, hx, hvx⟩
        exact ⟨y, by simp [hy], hvy⟩

theorem insV_comm {A : List α} {v s : α} (hv : ∃ x ∈ A, (v == x) = true)
    (hs : ¬(s == v) = true) : insV (insV A s) v = insV (insV A v) s := by
  induction A with
  | nil => simp at hv
  | cons a A ih =>
    by_cases hva : (v == a) = true
    · have hsa : ¬(s == a) = true := fun hsa => hs (BEq.trans hsa (BEq.symm hva))
      simp [insV, hva, hsa, hs]
    · obtain ⟨x, hx, hvx⟩ := hv
      have hx : x ∈ A := by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hvx hva
        · exact hx
      by_cases hsa : (s == a) = true
      · have hvs : ¬(v == s) = true := fun h => hs (BEq.symm h)
        simp [insV, hva, hsa, hvs]
      · simp [insV, hva, hsa, ih ⟨x, hx, hvx⟩]

/-- The elements of `l` are pairwise not `==`. -/
def Distinct (l : List α) : Prop := l.Pairwise fun x y => ¬(x == y) = true

theorem Distinct.insV {A : List α} (h : Distinct A) (v : α) :
    Distinct (DiscrTreeMergeSpec.insV A v) := by
  induction A with
  | nil => simp [DiscrTreeMergeSpec.insV, Distinct]
  | cons a A ih =>
    simp only [Distinct, List.pairwise_cons] at h
    simp only [DiscrTreeMergeSpec.insV]
    split
    · rename_i hva
      simp only [Distinct, List.pairwise_cons]
      refine ⟨fun y hy hvy => h.1 y hy (BEq.trans (BEq.symm hva) hvy), h.2⟩
    · rename_i hva
      simp only [Distinct, List.pairwise_cons]
      refine ⟨fun y hy hay => ?_, ih h.2⟩
      rcases mem_insV hy with hy | rfl
      · exact h.1 y hy hay
      · exact hva (BEq.symm hay)

theorem Distinct.foldl {A : List α} (h : Distinct A) (L : List α) :
    Distinct (L.foldl DiscrTreeMergeSpec.insV A) := by
  induction L generalizing A with
  | nil => simpa
  | cons v L ih => exact ih (h.insV v)

theorem insV_foldl_comm {C A : List α} {v : α} (hC : ∀ y ∈ C, ¬(y == v) = true)
    (hv : ∃ x ∈ A, (v == x) = true) : insV (C.foldl insV A) v = C.foldl insV (insV A v) := by
  induction C generalizing A with
  | nil => rfl
  | cons y C ih =>
    simp only [List.foldl_cons]
    rw [ih (fun z hz => hC z (by simp [hz])) (exists_beq_insV hv y),
      insV_comm hv (hC y (by simp))]

theorem foldl_insV_insV {B : List α} (hB : Distinct B) (A : List α) (v : α) :
    (insV B v).foldl insV A = insV (B.foldl insV A) v := by
  induction B generalizing A with
  | nil => simp [insV]
  | cons x B ih =>
    simp only [Distinct, List.pairwise_cons] at hB
    simp only [insV]
    split
    · rename_i hvx
      simp only [List.foldl_cons]
      rw [insV_foldl_comm (fun y hy hyv => hB.1 y hy (BEq.symm (BEq.trans hyv hvx)))
        ⟨x, mem_insV_self A x, hvx⟩, insV_insV_of_beq (BEq.symm hvx)]
    · simp only [List.foldl_cons]
      exact ih hB.2 _

theorem foldl_foldl_insV_aux (L : List α) {B : List α} (hB : Distinct B) (A : List α) :
    (L.foldl insV B).foldl insV A = L.foldl insV (B.foldl insV A) := by
  induction L generalizing B with
  | nil => rfl
  | cons v L ih => simp only [List.foldl_cons]; rw [ih (hB.insV v), foldl_insV_insV hB]

/-- Folding the deduplicated values of a module into earlier values is folding in all its values. -/
theorem foldl_foldl_insV (L A : List α) : (L.foldl insV []).foldl insV A = L.foldl insV A :=
  foldl_foldl_insV_aux L (by simp [Distinct]) A

end
end DiscrTreeMergeSpec

/-! ## The expected tries -/

namespace DiscrTreeMergeSpec
variable {α : Type}

/-- An entry: the key sequence and the value. -/
abbrev Entry (α : Type) := Array Key × α

/-- The node with the given values and children, as built by `mergeTries`. -/
def mkT (vs : Array α) (cs : Array (Key × Trie α)) : Trie α :=
  if h : vs.isEmpty ∧ cs.size = 1 then .chain cs[0].1 cs[0].2 else .node vs cs

/-- The values of the entries whose keys end at depth `i`, as inserted in order by `insertVal`. -/
def vals [BEq α] (L : List (Entry α)) (i : Nat) : Array α :=
  ((L.filter fun e => e.1.size ≤ i).map (·.2)).foldl insertVal #[]

/-- The entries with key `k` at depth `i`. -/
def sub (L : List (Entry α)) (i : Nat) (k : Key) : List (Entry α) :=
  L.filter fun e => e.1[i]? == some k

/--
`Den L i t`: `t` is the trie at depth `i` of the entries `L` (which share their first `i` keys
where it matters), inserted in order. A single entry is stored as a `suffix`, several entries as a
node whose values are inserted in order and whose children are sorted by key.
-/
inductive Den [BEq α] : List (Entry α) → Nat → Trie α → Prop
  | suffix (ks : Array Key) (v : α) (i : Nat) : Den [(ks, v)] i (.suffix ks i v)
  | node (L : List (Entry α)) (i : Nat) (cs : Array (Key × Trie α)) :
      2 ≤ L.length →
      (cs.toList.map (·.1)).Pairwise (· < ·) →
      (∀ k, k ∈ cs.toList.map (·.1) ↔ ∃ e ∈ L, e.1[i]? = some k) →
      (∀ p ∈ cs.toList, Den (sub L i p.1) (i + 1) p.2) →
      Den L i (mkT (vals L i) cs)

/-- The children `cs` of the node at depth `i` of the entries `L`. -/
structure Children [BEq α] (L : List (Entry α)) (i : Nat) (cs : Array (Key × Trie α)) : Prop where
  sorted : (cs.toList.map (·.1)).Pairwise (· < ·)
  keys : ∀ k, k ∈ cs.toList.map (·.1) ↔ ∃ e ∈ L, e.1[i]? = some k
  den : ∀ p ∈ cs.toList, Den (sub L i p.1) (i + 1) p.2

theorem Den.node' [BEq α] {L : List (Entry α)} {i : Nat} {cs : Array (Key × Trie α)}
    (hlen : 2 ≤ L.length) (hc : Children L i cs) : Den L i (mkT (vals L i) cs) :=
  .node L i cs hlen hc.sorted hc.keys hc.den

theorem Den.ne_nil [BEq α] {L : List (Entry α)} {i : Nat} {t : Trie α} (h : Den L i t) :
    L ≠ [] := by
  cases h with
  | suffix => simp
  | node _ _ _ hlen => intro h; simp [h] at hlen

/-! ### Uniqueness -/

theorem eq_of_sorted {l l' : List Key} (h : l.Pairwise (· < ·)) (h' : l'.Pairwise (· < ·))
    (hm : ∀ k, k ∈ l ↔ k ∈ l') : l = l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons b l' => exact absurd ((hm b).2 (by simp)) (by simp)
  | cons a l ih =>
    cases l' with
    | nil => exact absurd ((hm a).1 (by simp)) (by simp)
    | cons b l' =>
      simp only [List.pairwise_cons] at h h'
      have hab : a = b := by
        rcases List.mem_cons.1 ((hm a).1 (by simp)) with hab | ha
        · exact hab
        rcases List.mem_cons.1 ((hm b).2 (by simp)) with hba | hb
        · exact hba.symm
        exact absurd (Key.lt_trans (h.1 b hb) (h'.1 a ha)) (Key.lt_irrefl a)
      subst hab
      rw [ih h.2 h'.2 fun k => ?_]
      constructor
      · intro hk
        rcases List.mem_cons.1 ((hm k).1 (by simp [hk])) with rfl | hk'
        · exact absurd (h.1 k hk) (Key.lt_irrefl k)
        · exact hk'
      · intro hk
        rcases List.mem_cons.1 ((hm k).2 (by simp [hk])) with rfl | hk'
        · exact absurd (h'.1 k hk) (Key.lt_irrefl k)
        · exact hk'

theorem eq_of_map_fst_eq {l l' : List (Key × β)} (h : l.map (·.1) = l'.map (·.1))
    (h₂ : ∀ p ∈ l, ∀ q ∈ l', p.1 = q.1 → p.2 = q.2) : l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons p l ih =>
    cases l' with
    | nil => simp at h
    | cons q l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      have := h₂ p (by simp) q (by simp) h.1
      rw [ih h.2 fun p hp q hq => h₂ p (by simp [hp]) q (by simp [hq])]
      cases p; cases q; simp_all

theorem Den.unique [BEq α] {L : List (Entry α)} {i : Nat} {t : Trie α} (h : Den L i t) :
    ∀ {t'}, Den L i t' → t = t' := by
  induction h with
  | suffix ks v i =>
    intro t' h'
    cases h' with
    | suffix => rfl
    | node _ _ _ hlen => simp at hlen
  | node L i cs hlen hs hk hd ih =>
    intro t' h'
    cases h' with
    | suffix => simp at hlen
    | node _ _ cs' _ hs' hk' hd' =>
      have hkeys := eq_of_sorted hs hs' fun k => (hk k).trans (hk' k).symm
      have : cs = cs' := Array.toList_inj.1 <| eq_of_map_fst_eq hkeys fun p hp q hq hpq =>
        ih p hp (hpq ▸ hd' q hq)
      rw [this]

/-! ### Unfolding -/

theorem vals_eq_empty_iff [BEq α] {L : List (Entry α)} {i : Nat} :
    vals L i = #[] ↔ ∀ e ∈ L, i < e.1.size := by
  simp only [vals, foldl_insertVal]
  rw [← Array.toList_inj]
  simp only [foldl_insV_eq_nil, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, decide_eq_true_eq, Nat.not_le, and_true]

theorem unfold_mkT (vs : Array α) (cs : Array (Key × Trie α)) : (mkT vs cs).unfold = (vs, cs) := by
  unfold mkT
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h
    rw [Array.isEmpty_iff] at h1
    simp only [Trie.unfold]
    subst h1
    congr 1
    apply Array.ext <;> simp [h2]
  · simp [Trie.unfold]

theorem force_mkT (vs : Array α) (cs : Array (Key × Trie α)) : (mkT vs cs).force = mkT vs cs := by
  unfold mkT; split <;> rfl

theorem Den.unfold [BEq α] {L : List (Entry α)} {i : Nat} {t : Trie α} (h : Den L i t) :
    ∃ cs, Children L i cs ∧ t.unfold = (vals L i, cs) := by
  cases h with
  | suffix ks v i =>
    by_cases hi : i < ks.size
    · refine ⟨#[(ks[i], .suffix ks (i + 1) v)], ⟨by simp, fun k => ?_, ?_⟩, ?_⟩
      · simp [hi, getElem?_pos, eq_comm]
      · simp only [List.mem_singleton, forall_eq]
        have : sub [(ks, v)] i ks[i] = [(ks, v)] := by simp [sub, hi]
        rw [this]; exact .suffix ks v (i + 1)
      · simp [Trie.unfold, hi, vals, show ¬ks.size ≤ i by omega]
    · refine ⟨#[], ⟨by simp, fun k => ?_, by simp⟩, ?_⟩
      · simp [show ks.size ≤ i by omega]
      · simp [Trie.unfold, hi, vals, show ks.size ≤ i by omega, insertVal_eq,
          insV]
  | node L i cs hlen hs hk hd => exact ⟨cs, ⟨hs, hk, hd⟩, unfold_mkT _ _⟩

theorem Den.force [BEq α] {L : List (Entry α)} {i : Nat} {t : Trie α} (h : Den L i t) :
    ∃ cs, Children L i cs ∧ t.unfold = (vals L i, cs) ∧ t.force = mkT (vals L i) cs := by
  obtain ⟨cs, hc, hu⟩ := h.unfold
  refine ⟨cs, hc, hu, ?_⟩
  cases h with
  | suffix ks v i =>
    simp only [Trie.unfold] at hu
    simp only [Trie.force, Trie.force.unfoldSuffix]
    split at hu <;> simp only [Prod.mk.injEq] at hu <;> obtain ⟨h1, rfl⟩ := hu <;> rw [← h1] <;>
      simp [mkT, *]
  | node L i cs' => rw [force_mkT, unfold_mkT] at *; simp_all

end DiscrTreeMergeSpec

/-! ## Sequential insertion -/

namespace DiscrTreeMergeSpec
variable {α β γ : Type}

def KeysSorted (cs : Array (Key × Trie α)) : Prop :=
  (cs.toList.map Prod.fst).Pairwise (· < ·)

theorem KeysSorted.eq_of_mem {l : List (Key × β)} (hs : (l.map (·.1)).Pairwise (· < ·))
    {p q : Key × β} (hp : p ∈ l) (hq : q ∈ l) (h : p.1 = q.1) : p = q := by
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hp
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hq
  have hlt : ∀ a b (ha : a < l.length) (hb : b < l.length), a < b → l[a].1 < l[b].1 := by
    intro a b ha hb hab
    have := List.pairwise_iff_getElem.1 hs a b (by simpa using ha) (by simpa using hb) hab
    simp only [List.getElem_map] at this
    exact this
  rcases Nat.lt_trichotomy m n with hmn | rfl | hmn
  · have := hlt m n hm hn hmn; rw [h] at this; exact absurd this (Key.lt_irrefl _)
  · rfl
  · have := hlt n m hn hm hmn; rw [h] at this; exact absurd this (Key.lt_irrefl _)

theorem modifyM_id_run {xs : Array α} {i : Nat} {f : α → Id α} (hi : i < xs.size) :
    (xs.modifyM i f).run = xs.set i (f xs[i]).run := by
  simp [Array.modifyM, hi]

theorem binInsertAux_id_cases {lt : α → α → Bool} {merge : α → Id α} {add : Unit → Id α}
    {as : Array α} {k : α} (h_asymm : ∀ a b, lt a b → lt b a → False)
    (lo hi : Fin as.size) (h : lo.1 ≤ hi.1) (w : lt as[lo] k) (whi : lt k as[hi]) :
    (∃ i, ∃ hj : i < as.size, lt as[i] k = false ∧ lt k as[i] = false ∧
        (Array.binInsertAux lt merge add as k lo hi h w).run = as.set i (merge as[i]).run) ∨
    (∃ i, ∃ hj : i ≤ as.size,
        (Array.binInsertAux lt merge add as k lo hi h w).run = as.insertIdx i (add ()).run ∧
        (∀ h : 0 < i, lt as[i - 1] k) ∧ (∀ h : i < as.size, lt k as[i])) := by
  fun_induction Array.binInsertAux lt merge add as k lo hi h w with
  | case1 lo hi _ w mid midVal hlt hmid =>
    simp only [Id.run_bind, Id.run_pure]
    refine .inr ⟨lo + 1, by omega, rfl, fun _ => by simpa using w, fun h' => ?_⟩
    have : hi.1 = lo.1 + 1 ∨ hi.1 = lo.1 := by omega
    rcases this with h_eq | h_eq
    · simpa [← h_eq] using whi
    · exact (h_asymm _ _ w (by simpa [Fin.ext_iff, h_eq] using whi)).elim
  | case2 lo hi _ w mid midVal hlt hmid _ _ ih =>
    exact ih whi
  | case3 lo hi _ w mid midVal hlt hgt _ _ _ ih =>
    exact ih hgt
  | case4 lo hi _ w mid midVal hlt hgt =>
    exact .inl ⟨mid, by omega, by simpa using hlt, by simpa using hgt, modifyM_id_run _⟩

/--
`Array.binInsertM` either merges into an element equivalent to the key, or inserts the new
element at a position whose neighbors are ordered around the key.
-/
theorem binInsertM_id_cases {lt : α → α → Bool} {merge : α → Id α} {add : Unit → Id α}
    {as : Array α} {k : α} (h_asymm : ∀ a b, lt a b → lt b a → False) :
    (∃ i, ∃ hj : i < as.size, lt as[i] k = false ∧ lt k as[i] = false ∧
        (as.binInsertM lt merge add k).run = as.set i (merge as[i]).run) ∨
    (∃ i, ∃ hj : i ≤ as.size, (as.binInsertM lt merge add k).run = as.insertIdx i (add ()).run ∧
        (∀ h : 0 < i, lt as[i - 1] k) ∧ (∀ h : i < as.size, lt k as[i])) := by
  have push_eq : as.push (add ()).run = as.insertIdx as.size (add ()).run := by
    simp
  unfold Array.binInsertM
  split
  · grind
  split
  · grind
  split
  · rename_i h0 hlt hgt
    exact .inl ⟨0, by omega, by simpa using hgt, by simpa using hlt, modifyM_id_run _⟩
  split
  · grind
  split
  · rename_i h0 _ _ hlt hgt
    exact .inl ⟨as.size - 1, by omega, by simpa using hlt, by simpa using hgt, modifyM_id_run _⟩
  · rename_i h0 _ _ _ hgt
    exact binInsertAux_id_cases h_asymm _ _ _ _ (by simpa using hgt)

theorem map_insertIdx' {f : β → γ} {l : List β} {i : Nat} {x : β} :
    (l.insertIdx i x).map f = (l.map f).insertIdx i (f x) := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons y l ih => cases i <;> simp [List.insertIdx_succ_cons, ih]

/-- Inserting between two neighbors that are ordered around the new element keeps a list sorted. -/
theorem pairwise_insertIdx_of_neighbors {R : β → β → Prop}
    (h_trans : ∀ {a b c}, R a b → R b c → R a c)
    {l : List β} {i : Nat} {x : β} (hi : i ≤ l.length) (hl : l.Pairwise R)
    (hprev : ∀ h : 0 < i, R (l[i - 1]'(by omega)) x) (hnext : ∀ h : i < l.length, R x l[i]) :
    (l.insertIdx i x).Pairwise R := by
  induction l generalizing i with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hi; subst hi; simp
  | cons y l ih =>
    have hl' := List.pairwise_cons.1 hl
    cases i with
    | zero =>
      rw [List.insertIdx_zero]
      refine List.Pairwise.cons (fun z hz => ?_) hl
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hnext (by simp)
      · exact h_trans (hnext (by simp)) (hl'.1 z hz)
    | succ i =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hi
      rw [List.insertIdx_succ_cons]
      refine List.Pairwise.cons (fun z hz => ?_) (ih hi hl'.2 (fun h => ?_) (fun h => ?_))
      · rcases (List.mem_insertIdx hi).1 hz with rfl | hz
        · grind
        · exact hl'.1 z hz
      · grind
      · grind

theorem KeysSorted.set {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat}
    (hi : i < cs.size) {y : Key × Trie α} (hy : y.fst = cs[i].fst) : KeysSorted (cs.set i y) := by
  unfold KeysSorted at *
  rw [Array.toList_set, List.map_set, hy]
  have : cs[i].fst = (cs.toList.map Prod.fst)[i]'(by simpa using hi) := by simp
  rwa [this, List.set_getElem_self]

theorem KeysSorted.insertIdx {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat}
    (hi : i ≤ cs.size) {y : Key × Trie α}
    (hprev : ∀ h : 0 < i, cs[i - 1].fst < y.fst) (hnext : ∀ h : i < cs.size, y.fst < cs[i].fst) :
    KeysSorted (cs.insertIdx i y) := by
  unfold KeysSorted at *
  rw [Array.toList_insertIdx, map_insertIdx']
  refine pairwise_insertIdx_of_neighbors (R := (· < ·)) Key.lt_trans
    (by simp only [List.length_map, Array.length_toList]; exact hi) hs (fun h => ?_) (fun h => ?_)
  · simp only [List.getElem_map, Array.getElem_toList]; exact hprev h
  · grind


theorem binInsertM_id_induct {lt : α → α → Bool} {merge : α → Id α} {add : Unit → Id α}
    {as : Array α} {k : α} {P : Array α → Prop} (h_asymm : ∀ a b, lt a b → lt b a → False)
    (hmerge : ∀ i (hi : i < as.size) x, as[i] = x → lt x k = false → lt k x = false →
      P (as.set i (merge x).run))
    (hadd : ∀ i (hi : i ≤ as.size), (∀ h : 0 < i, lt as[i - 1] k) →
      (∀ h : i < as.size, lt k as[i]) → P (as.insertIdx i (add ()).run)) :
    P (as.binInsertM lt merge add k).run := by
  rcases binInsertM_id_cases (lt := lt) (merge := merge) (add := add) (as := as) (k := k) h_asymm
    with ⟨i, hi, h1, h2, heq⟩ | ⟨i, hi, heq, h1, h2⟩
  · rw [heq]; exact hmerge i hi _ rfl h1 h2
  · rw [heq]; exact hadd i hi h1 h2

/-- The new key of an insertion position is different from all keys. -/
theorem KeysSorted.ne_of_insertIdx {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {j : Nat}
    (hj : j ≤ cs.size) {k : Key} (hprev : ∀ h : 0 < j, cs[j - 1].1 < k)
    (hnext : ∀ h : j < cs.size, k < cs[j].1) : ∀ p ∈ cs, p.1 ≠ k := by
  intro p hp hpk
  obtain ⟨m, hm, rfl⟩ := Array.mem_iff_getElem.1 hp
  have hlt : ∀ a b (ha : a < cs.size) (hb : b < cs.size), a < b → cs[a].1 < cs[b].1 := by
    intro a b ha hb hab
    have := List.pairwise_iff_getElem.1 hs a b (by simpa using ha) (by simpa using hb) hab
    simp only [List.getElem_map, Array.getElem_toList] at this
    exact this
  have : cs[m].1 < k ∨ k < cs[m].1 := by
    by_cases hmj : m < j
    · have h1 := hprev (by omega)
      rcases Nat.lt_or_eq_of_le (show m ≤ j - 1 by omega) with h | h
      · exact .inl (Key.lt_trans (hlt m (j - 1) hm (by omega) h) h1)
      · subst h; exact .inl h1
    · have h1 := hnext (by omega)
      rcases Nat.lt_or_eq_of_le (show j ≤ m by omega) with h | h
      · exact .inr (Key.lt_trans h1 (hlt j m (by omega) hm h))
      · subst h; exact .inr h1
  rw [hpk] at this
  exact (Key.lt_irrefl k) (this.elim id id)

theorem length_append_singleton {L : List (Entry α)} (h : L ≠ []) (e : Entry α) :
    2 ≤ (L ++ [e]).length := by
  cases L <;> simp_all

theorem sub_eq_self {L : List (Entry α)} {i : Nat} {k : Key} (h : ∀ e ∈ L, e.1[i]? = some k) :
    sub L i k = L := by
  simp only [sub]
  exact List.filter_eq_self.2 (by simpa using h)

theorem sub_eq_nil {L : List (Entry α)} {i : Nat} {k : Key} (h : ∀ e ∈ L, e.1[i]? ≠ some k) :
    sub L i k = [] := by
  simp only [sub]
  exact List.filter_eq_nil_iff.2 (by simpa using h)

theorem sub_append (L : List (Entry α)) (e : Entry α) (i : Nat) (k : Key) :
    sub (L ++ [e]) i k = sub L i k ++ (if e.1[i]? == some k then [e] else []) := by
  simp only [sub, List.filter_append]
  split <;> simp_all

theorem sub_append_of_ne {L : List (Entry α)} {e : Entry α} {i : Nat} {k : Key}
    (h : e.1[i]? ≠ some k) : sub (L ++ [e]) i k = sub L i k := by
  simp [sub_append, h]

theorem mkT_of_ne_empty {vs : Array α} (cs : Array (Key × Trie α)) (h : vs ≠ #[]) :
    mkT vs cs = .node vs cs := by
  simp [mkT, Array.isEmpty_iff, h]

theorem mkT_of_size_ne (vs : Array α) {cs : Array (Key × Trie α)} (h : cs.size ≠ 1) :
    mkT vs cs = .node vs cs := by
  simp [mkT, h]

theorem mkT_singleton (k : Key) (c : Trie α) : mkT #[] #[(k, c)] = .chain k c := by
  simp [mkT]

section
variable [BEq α]

theorem vals_append_of_lt {L : List (Entry α)} {e : Entry α} {i : Nat} (h : i < e.1.size) :
    vals (L ++ [e]) i = vals L i := by
  simp [vals, List.filter_append, show ¬e.1.size ≤ i by omega]

theorem vals_append_of_le {L : List (Entry α)} {e : Entry α} {i : Nat} (h : e.1.size ≤ i) :
    vals (L ++ [e]) i = insertVal (vals L i) e.2 := by
  simp [vals, List.filter_append, h]

theorem insertVal_ne_empty (vs : Array α) (v : α) : insertVal vs v ≠ #[] := by
  rw [insertVal_eq]; intro h
  exact insV_ne_nil _ _ (by simpa using congrArg Array.toList h)

theorem Children.keys_mem {L : List (Entry α)} {i : Nat} {cs : Array (Key × Trie α)}
    (hc : Children L i cs) {e : Entry α} (he : e ∈ L) {k : Key} (hk : e.1[i]? = some k) :
    ∃ c, (k, c) ∈ cs := by
  have := (hc.keys k).2 ⟨e, he, hk⟩
  simp only [List.mem_map, Array.mem_toList_iff] at this
  obtain ⟨⟨k', c⟩, hm, rfl⟩ := this
  exact ⟨c, hm⟩

theorem Children.size_pos {L : List (Entry α)} {i : Nat} {cs : Array (Key × Trie α)}
    (hc : Children L i cs) (hv : vals L i = #[]) (hne : L ≠ []) : 0 < cs.size := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil L hne
  have hi := vals_eq_empty_iff.1 hv e he
  obtain ⟨c, hm⟩ := hc.keys_mem he (k := e.1[i]) (by simp [hi])
  exact Array.size_pos_of_mem hm

theorem keys_append_iff {L : List (Entry α)} {i : Nat} {cs : Array (Key × Trie α)}
    (hc : Children L i cs) (e : Entry α) (k : Key) :
    (∃ e' ∈ L ++ [e], e'.1[i]? = some k) ↔ k ∈ cs.toList.map (·.1) ∨ e.1[i]? = some k := by
  rw [hc.keys]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨e', he' | rfl, h⟩
    · exact .inl ⟨e', he', h⟩
    · exact .inr h
  · rintro (⟨e', he', h⟩ | h)
    · exact ⟨e', .inl he', h⟩
    · exact ⟨e, .inr rfl, h⟩

omit [BEq α] in
theorem binInsert_singleton {k k' : Key} (h : k' ≠ k) (c c' : Trie α) :
    #[(k, c)].binInsert (fun a b => decide (a.1 < b.1)) (k', c') =
      if k' < k then #[(k', c'), (k, c)] else #[(k, c), (k', c')] := by
  unfold Array.binInsert Array.binInsertM
  by_cases h1 : k' < k
  · simp [h1]
  · have h2 : k < k' := (Key.lt_total h).resolve_left h1
    simp [h1, h2]

/-- Inserting an entry into the trie of `L` at depth `i` gives the trie of `L` and the entry. -/
theorem insertAux_den (keys : Array Key) (v : α) (i : Nat) (L : List (Entry α)) (t : Trie α)
    (h : Den L i t) : Den (L ++ [(keys, v)]) i (insertAux keys v i t) := by
  obtain ⟨cs, hc, -, hf⟩ := h.force
  have hne := h.ne_nil
  have hlen := length_append_singleton hne (keys, v)
  rw [insertAux.eq_def, hf]
  by_cases hch : (vals L i).isEmpty ∧ cs.size = 1
  · obtain ⟨hv, hs⟩ := hch
    rw [Array.isEmpty_iff] at hv
    obtain ⟨k, c, rfl⟩ : ∃ k c, cs = #[(k, c)] :=
      ⟨cs[0].1, cs[0].2, Array.ext (by simp [hs]) fun j h1 _ => by
        have : j = 0 := by omega
        subst this; rfl⟩
    have hall : ∀ e ∈ L, e.1[i]? = some k := by
      intro e he
      have hi := vals_eq_empty_iff.1 hv e he
      obtain ⟨c', hm⟩ := hc.keys_mem he (k := e.1[i]) (by simp [hi])
      simp at hm
      simp [hi, hm.1]
    have hden : Den L (i + 1) c := by
      have := hc.den (k, c) (by simp)
      rwa [sub_eq_self hall] at this
    rw [hv, mkT_singleton]
    dsimp only
    split
    · rename_i hi
      have hlt : i < keys.size := hi
      split
      · rename_i hk
        have hk : keys[i] = k := by simpa using hk
        have := Den.node' hlen (i := i) (cs := #[(k, insertAux keys v (i + 1) c)])
          ⟨by simp, fun k' => ?_, ?_⟩
        · rwa [vals_append_of_lt hi, hv, mkT_singleton] at this
        · rw [keys_append_iff hc]
          simp [hi, hk, eq_comm]
        · simp only [List.mem_singleton, forall_eq]
          rw [sub_append, sub_eq_self hall]
          simp only [hi, getElem?_pos, hk, BEq.rfl, ↓reduceIte]
          exact insertAux_den keys v (i + 1) L c hden
      · rename_i hk
        have hk : keys[i] ≠ k := by simpa using hk
        rw [binInsert_singleton hk]
        have hsk : sub (L ++ [(keys, v)]) i k = L := by
          rw [sub_append_of_ne (by simp [hi, hk]), sub_eq_self hall]
        have hsk' : sub (L ++ [(keys, v)]) i keys[i] = [(keys, v)] := by
          rw [sub_append, sub_eq_nil (fun e he => by simp [hall e he, Ne.symm hk])]
          simp [hi]
        have hden' : Den [(keys, v)] (i + 1) (createNodes keys v (i + 1)) := .suffix keys v (i + 1)
        have hkeys :
            ∀ k', (∃ e' ∈ L ++ [(keys, v)], e'.1[i]? = some k') ↔ k' = k ∨ k' = keys[i] := by
          intro k'; rw [keys_append_iff hc]; simp [hi, eq_comm]
        split
        · rename_i hlt'
          have := Den.node' hlen (i := i) (cs := #[(keys[i], createNodes keys v (i + 1)), (k, c)])
            ⟨by simp [hlt'], fun k' => ?_, ?_⟩
          · rwa [vals_append_of_lt hi, hv, mkT_of_size_ne _ (by simp)] at this
          · rw [hkeys]; simp [or_comm]
          · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
              forall_eq]
            exact ⟨by rw [hsk']; exact hden', by rw [hsk]; exact hden⟩
        · rename_i hlt'
          have hlt' : k < keys[i] := (Key.lt_total (Ne.symm hk)).resolve_right hlt'
          have := Den.node' hlen (i := i) (cs := #[(k, c), (keys[i], createNodes keys v (i + 1))])
            ⟨by simp [hlt'], fun k' => ?_, ?_⟩
          · rwa [vals_append_of_lt hi, hv, mkT_of_size_ne _ (by simp)] at this
          · rw [hkeys]; simp
          · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
              forall_eq]
            exact ⟨by rw [hsk]; exact hden, by rw [hsk']; exact hden'⟩
    · rename_i hi
      have hnone : keys[i]? = none := Array.getElem?_eq_none (by omega)
      have := Den.node' hlen (i := i) (cs := #[(k, c)]) ⟨by simp, fun k' => ?_, ?_⟩
      · rw [vals_append_of_le (by simpa using hi), hv, mkT_of_ne_empty _ (insertVal_ne_empty _ _)]
          at this
        simpa [insertVal_eq, insV] using this
      · rw [keys_append_iff hc]; simp [hnone]
      · simp only [List.mem_singleton, forall_eq]
        rw [sub_append_of_ne (by simp [hnone]), sub_eq_self hall]
        exact hden
  · have hmkT : ∀ cs' : Array (Key × Trie α), cs.size ≤ cs'.size →
        mkT (vals L i) cs' = .node (vals L i) cs' := by
      intro cs' hle
      by_cases hv : vals L i = #[]
      · have := hc.size_pos hv hne
        have : cs.size ≠ 1 := fun h => hch ⟨by simp [hv], h⟩
        exact mkT_of_size_ne _ (by omega)
      · exact mkT_of_ne_empty _ hv
    rw [hmkT cs (Nat.le_refl _)]
    dsimp only
    split
    · rename_i hi
      have hlt : i < keys.size := hi
      rw [← vals_append_of_lt (L := L) (e := (keys, v)) hi]
      have hmkT' : ∀ cs' : Array (Key × Trie α), cs.size ≤ cs'.size →
          Trie.node (vals (L ++ [(keys, v)]) i) cs' = mkT (vals (L ++ [(keys, v)]) i) cs' := by
        intro cs' hle; rw [vals_append_of_lt hi, hmkT cs' hle]
      refine binInsertM_id_induct
        (P := fun cs' => Den (L ++ [(keys, v)]) i (.node (vals (L ++ [(keys, v)]) i) cs'))
        (fun a b h1 h2 => Key.lt_asymm (by simpa using h1) (by simpa using h2)) ?_ ?_
      · rintro j hj ⟨k', c⟩ hjx h1 h2
        dsimp only [Id.run]
        have hk : k' = keys[i] :=
          Key.eq_of_not_lt (by simpa [Key.lt_iff] using h1) (by simpa [Key.lt_iff] using h2)
        subst hk
        have hcm : (keys[i], c) ∈ cs := hjx ▸ Array.getElem_mem hj
        have hden : Den (sub L i keys[i]) (i + 1) c := hc.den _ (by simpa using hcm)
        have hkeys : (cs.set j (keys[i], insertAux keys v (i + 1) c)).toList.map (·.1) =
            cs.toList.map (·.1) := by
          rw [Array.toList_set, List.map_set]
          have : keys[i] = (cs.toList.map (·.1))[j]'(by simpa using hj) := by simp [hjx]
          simp only
          rw [this, List.set_getElem_self]
        have hs' : KeysSorted (cs.set j (keys[i], insertAux keys v (i + 1) c)) :=
          KeysSorted.set hc.sorted hj (by simp [hjx])
        rw [hmkT' _ (by simp)]
        refine Den.node' hlen ⟨hs', fun k' => ?_, fun q hq => ?_⟩
        · rw [keys_append_iff hc, hkeys]
          simp only [hi, getElem?_pos, Option.some.injEq]
          constructor
          · exact .inl
          · rintro (h | rfl)
            · exact h
            · simp only [List.mem_map, Array.mem_toList_iff]; exact ⟨_, hcm, rfl⟩
        · by_cases hq1 : q.1 = keys[i]
          · have := KeysSorted.eq_of_mem hs' hq
              (Array.mem_toList_iff.2 (Array.mem_set hj)) hq1
            subst this
            simp only
            rw [sub_append]
            simp only [hi, getElem?_pos, BEq.rfl, ↓reduceIte]
            exact insertAux_den keys v (i + 1) _ c hden
          · rw [sub_append_of_ne (by simp [hi, Ne.symm hq1])]
            rcases List.mem_or_eq_of_mem_set (by simpa using hq) with hq | hq
            · exact hc.den q hq
            · subst hq; exact absurd rfl hq1
      · intro j hj hprev hnext
        dsimp only [Id.run]
        have hne_k := KeysSorted.ne_of_insertIdx hc.sorted hj (k := keys[i])
          (fun h => by simpa using hprev h) (fun h => by simpa using hnext h)
        have hs' : KeysSorted (cs.insertIdx j (keys[i], createNodes keys v (i + 1))) :=
          KeysSorted.insertIdx hc.sorted hj (fun h => by simpa using hprev h)
            (fun h => by simpa using hnext h)
        rw [hmkT' _ (by simp)]
        refine Den.node' hlen ⟨hs', fun k' => ?_, fun q hq => ?_⟩
        · rw [keys_append_iff hc]
          simp only [Array.toList_insertIdx, map_insertIdx', hi, getElem?_pos, Option.some.injEq]
          rw [List.mem_insertIdx (by simpa using hj)]
          simp only [eq_comm (a := k'), or_comm]
        · rcases Array.mem_insertIdx.1 (Array.mem_toList_iff.1 hq) with rfl | hq
          · have : sub (L ++ [(keys, v)]) i keys[i] = [(keys, v)] := by
              rw [sub_append, sub_eq_nil fun e he hk => ?_]
              · simp [hi]
              · obtain ⟨c, hm⟩ := hc.keys_mem he hk
                exact hne_k _ hm rfl
            rw [this]
            exact .suffix keys v (i + 1)
          · rw [sub_append_of_ne (by simp [hi, Ne.symm (hne_k q hq)])]
            exact hc.den q (by simpa using hq)
    · rename_i hi
      have hnone : keys[i]? = none := Array.getElem?_eq_none (by omega)
      have := Den.node' hlen (i := i) (cs := cs) ⟨hc.sorted, fun k' => ?_, fun q hq => ?_⟩
      · rwa [vals_append_of_le (by simpa using hi), mkT_of_ne_empty _ (insertVal_ne_empty _ _)]
          at this
      · rw [keys_append_iff hc]; simp [hnone]
      · rw [sub_append_of_ne (by simp [hnone])]
        exact hc.den q hq
termination_by keys.size - i

end
end DiscrTreeMergeSpec

/-! ## `groupByKey` -/

namespace DiscrTreeMergeSpec
variable {α β γ : Type}

/-- An invariant of a `for` loop in `Id` whose body always yields, along the processed prefix. -/
theorem forIn'_list_inv (l : List γ) (f : (a : γ) → a ∈ l → β → Id (ForInStep β))
    (I : List γ → β → Prop) (pre : List γ) (init : β) (h0 : I pre init)
    (hs : ∀ a (m : a ∈ l) b pre', I pre' b → ∃ b', f a m b = .yield b' ∧ I (pre' ++ [a]) b') :
    I (pre ++ l) (forIn' l init f).run := by
  induction l generalizing pre init with
  | nil => simpa using h0
  | cons a l ih =>
    obtain ⟨b', hb', hI⟩ := hs a List.mem_cons_self init pre h0
    rw [List.forIn'_cons, hb']
    have := ih (fun a m b => f a (List.mem_cons_of_mem _ m) b) (pre ++ [a]) b' hI
      (fun a m b pre' h => hs a _ b pre' h)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this
    exact this

theorem forIn'_array_inv (xs : Array γ) (f : (a : γ) → a ∈ xs → β → Id (ForInStep β))
    (I : List γ → β → Prop) (pre : List γ) (init : β) (h0 : I pre init)
    (hs : ∀ a (m : a ∈ xs) b pre', I pre' b → ∃ b', f a m b = .yield b' ∧ I (pre' ++ [a]) b') :
    I (pre ++ xs.toList) (forIn' xs init f).run := by
  have e : forIn' xs init f =
      forIn' xs.toList init (fun a m b => f a (Array.mem_toList_iff.1 m) b) :=
    (Array.forIn'_toList (xs := xs) (b := init)
      (f := fun a m b => f a (Array.mem_toList_iff.1 m) b)).symm
  rw [e]
  exact forIn'_list_inv _ _ I pre init h0 fun a m b pre' h => hs a _ b pre' h

/-- The groups of `groupByKey`. -/
abbrev Grp (P : Trie α → Prop) := {g : Array (Trie α) // 0 < g.size ∧ ∀ c ∈ g, P c}

/-- The invariant of the loops of `groupByKey` after grouping the children `F`. -/
structure GInv (P : Trie α → Prop) (F : List (Key × Trie α)) (idx : Std.HashMap Key Nat)
    (groups : Array (Key × Grp P × Nat)) : Prop where
  nodup : (groups.toList.map (·.1)).Nodup
  idx_none : ∀ k, idx[k]? = none ↔ k ∉ groups.toList.map (·.1)
  idx_some : ∀ k j, idx[k]? = some j → ∃ h : j < groups.size, groups[j].1 = k
  mem : ∀ k, k ∈ groups.toList.map (·.1) ↔ k ∈ F.map (·.1)
  grp : ∀ x ∈ groups.toList, x.2.1.1.toList = (F.filter (·.1 == x.1)).map (·.2)

theorem GInv.empty (P : Trie α → Prop) : GInv P [] ∅ #[] where
  nodup := by simp
  idx_none := by simp
  idx_some := by simp
  mem := by simp
  grp := by simp

theorem GInv.modify {P : Trie α → Prop} {F : List (Key × Trie α)} {idx : Std.HashMap Key Nat}
    {groups : Array (Key × Grp P × Nat)} (inv : GInv P F idx groups) (p : Key × Trie α)
    (j : Nat) (hj : idx[p.1]? = some j) (f : Key × Grp P × Nat → Key × Grp P × Nat)
    (hf1 : ∀ x, (f x).1 = x.1) (hf2 : ∀ x, (f x).2.1.1 = x.2.1.1.push p.2) :
    GInv P (F ++ [p]) idx (groups.modify j f) := by
  obtain ⟨hjs, hjk⟩ := inv.idx_some _ _ hj
  have hkeys : (groups.modify j f).toList.map (·.1) = groups.toList.map (·.1) := by
    apply List.ext_getElem <;> simp [List.getElem_modify]
    intro m h1 h2; split <;> simp [hf1]
  have hpk : p.1 ∈ groups.toList.map (·.1) := by
    simp only [List.mem_map, Array.mem_toList_iff]; exact ⟨_, Array.getElem_mem hjs, hjk⟩
  refine ⟨hkeys ▸ inv.nodup, fun k => hkeys ▸ inv.idx_none k, fun k j' h => ?_, fun k => ?_,
    fun x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := inv.idx_some k j' h
    refine ⟨by simpa using h1, ?_⟩
    rw [Array.getElem_modify]; split <;> simp [hf1, h2]
  · rw [hkeys, inv.mem]; simp only [List.map_append, List.mem_append]
    constructor
    · exact .inl
    · rintro (h | h)
      · exact h
      · simp at h; subst h; exact inv.mem _ |>.1 hpk
  · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [Array.length_toList, Array.size_modify] at hm
    simp only [Array.getElem_toList, Array.getElem_modify]
    split
    · rename_i hjm; subst hjm
      rw [hf2, Array.toList_push, inv.grp _ (Array.mem_toList_iff.2 (Array.getElem_mem hjs)), hf1,
        hjk]
      simp
    · rename_i hjm
      have hne : groups[m].1 ≠ p.1 := by
        intro h
        have := (List.Nodup.getElem_inj inv.nodup (i := m) (j := j) (hi := by simpa using hm)
          (hj := by simpa using hjs)).1 (by simp [h, hjk])
        exact hjm this.symm
      rw [inv.grp _ (Array.mem_toList_iff.2 (Array.getElem_mem hm))]
      simp [List.filter_append, Ne.symm hne]

theorem GInv.push {P : Trie α → Prop} {F : List (Key × Trie α)} {idx : Std.HashMap Key Nat}
    {groups : Array (Key × Grp P × Nat)} (inv : GInv P F idx groups) (p : Key × Trie α)
    (hj : idx[p.1]? = none) (g : Grp P) (hg : g.1 = #[p.2]) (pos : Nat) :
    GInv P (F ++ [p]) (idx.insert p.1 groups.size) (groups.push (p.1, g, pos)) := by
  have hpk := (inv.idx_none p.1).1 hj
  refine ⟨?_, fun k => ?_, fun k j' h => ?_, fun k => ?_, fun x hx => ?_⟩
  · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨inv.nodup, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    exact hpk (hb ▸ hab ▸ ha)
  · rw [Std.HashMap.getElem?_insert]
    by_cases hk : p.1 = k
    · subst hk; simp
    · simp [hk, inv.idx_none, Ne.symm hk]
  · rw [Std.HashMap.getElem?_insert] at h
    by_cases hk : p.1 = k
    · subst hk; simp at h; subst h; exact ⟨by simp, by simp⟩
    · simp only [beq_iff_eq, hk, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := inv.idx_some k j' h
      exact ⟨by simp; omega, by rw [Array.getElem_push_lt h1]; exact h2⟩
  · simp only [Array.toList_push, List.map_append, List.mem_append, inv.mem]; simp [or_comm]
  · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have hne : x.1 ≠ p.1 := fun h => hpk (h ▸ List.mem_map_of_mem hx)
      rw [inv.grp x hx]; simp [List.filter_append, Ne.symm hne]
    · rw [hg]
      have : F.filter (·.1 == p.1) = [] :=
        List.filter_eq_nil_iff.2 fun q hq h =>
          hpk ((inv.mem _).2 (by simp at h; exact h ▸ List.mem_map_of_mem hq))
      simp [List.filter_append, this]

/-- The specification of the result of `groupByKey` on the children `F`. -/
structure GBK (P : Trie α → Prop) (F : List (Key × Trie α)) (R : List (Key × Grp P)) : Prop where
  nodup : (R.map (·.1)).Nodup
  mem : ∀ k, k ∈ R.map (·.1) ↔ k ∈ F.map (·.1)
  grp : ∀ x ∈ R, x.2.1.toList = (F.filter (·.1 == x.1)).map (·.2)

theorem GBK.perm {P : Trie α → Prop} {F : List (Key × Trie α)} {R R' : List (Key × Grp P)}
    (h : GBK P F R) (hp : R'.Perm R) : GBK P F R' where
  nodup := (hp.map _).nodup_iff.2 h.nodup
  mem k := ((hp.map _).mem_iff).trans (h.mem k)
  grp x hx := h.grp x (hp.mem_iff.1 hx)

theorem groupByKey_spec (ts : Array (Array (Key × Trie α))) (P : Trie α → Prop) (hP) :
    GBK P (ts.toList.flatMap (·.toList)) (groupByKey ts P hP).toList := by
  have key : ∀ (s : Std.HashMap Key Nat × Array (Key × Grp P × Nat) × Nat),
      GInv P (ts.toList.flatMap (·.toList)) s.1 s.2.1 →
      GBK P (ts.toList.flatMap (·.toList))
        ((s.2.1.qsort fun x1 x2 => decide (x1.2.2 < x2.2.2)).map fun x => (x.1, x.2.1)).toList := by
    intro s inv
    have hperm := (QS.qsort_spec (fun x1 x2 : Key × Grp P × Nat => decide (x1.2.2 < x2.2.2))
      (by intro a b h; simp at *; omega) (by intro a b c h1 h2; simp at *; omega) s.2.1).1
    refine GBK.perm (R := (s.2.1.toList.map fun x => (x.1, x.2.1)))
      ⟨by simpa [Function.comp_def] using inv.nodup,
       fun k => by simpa [Function.comp_def] using inv.mem k,
       fun x hx => ?_⟩ ?_
    · simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact inv.grp y hy
    · simpa using (Array.perm_iff_toList_perm.1 hperm).map _
  simp only [groupByKey, Id.run]
  apply key
  refine forIn'_array_inv ts _
    (fun (pre : List (Array (Key × Trie α)))
      (s : Std.HashMap Key Nat × Array (Key × Grp P × Nat) × Nat) =>
      GInv P (pre.flatMap (·.toList)) s.1 s.2.1) [] _ ?_ ?_
  · exact GInv.empty P
  intro cs hcs s pre inv
  refine ⟨_, rfl, ?_⟩
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine forIn'_array_inv cs _
    (fun (pre' : List (Key × Trie α))
      (s : Std.HashMap Key Nat × Array (Key × Grp P × Nat) × Nat) =>
      GInv P (pre.flatMap (·.toList) ++ pre') s.1 s.2.1) [] _ ?_ ?_
  · simpa using inv
  intro p hp s pre' inv
  split
  · rename_i j hj
    refine ⟨_, rfl, ?_⟩
    simp only [← List.append_assoc]
    exact inv.modify p j hj _ (fun _ => rfl) (fun _ => rfl)
  · rename_i hj
    refine ⟨_, rfl, ?_⟩
    simp only [← List.append_assoc]
    exact inv.push p hj _ rfl s.2.2

end DiscrTreeMergeSpec

/-! ## Forcing `lazy` nodes -/

namespace DiscrTreeMergeSpec
variable {α β γ : Type}

/-- `Forces t r`: forcing all `lazy` nodes of `t` terminates with `r`. -/
inductive Forces : Trie α → Trie α → Prop
  | lazy {t : Thunk (Trie α)} {r : Trie α} : Forces t.get r → Forces (.lazy t) r
  | chain {k : Key} {c r : Trie α} : Forces c r → Forces (.chain k c) (.chain k r)
  | node {vs : Array α} {cs cs' : Array (Key × Trie α)} :
      cs.toList.map (·.1) = cs'.toList.map (·.1) →
      (∀ p ∈ cs.toList.zip cs'.toList, Forces p.1.2 p.2.2) → Forces (.node vs cs) (.node vs cs')
  | suffix {ks : Array Key} {i : Nat} {v : α} : Forces (.suffix ks i v) (.suffix ks i v)

theorem eq_of_forces_zip {l l₁ l₂ : List (Key × Trie α)} (h₁ : l.map (·.1) = l₁.map (·.1))
    (h₂ : l.map (·.1) = l₂.map (·.1))
    (ih : ∀ p ∈ l.zip l₁, ∀ r, Forces p.1.2 r → p.2.2 = r)
    (hf : ∀ p ∈ l.zip l₂, Forces p.1.2 p.2.2) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => cases l₁ <;> cases l₂ <;> simp_all
  | cons p l ihl =>
    cases l₁ with
    | nil => simp at h₁
    | cons q₁ l₁ =>
      cases l₂ with
      | nil => simp at h₂
      | cons q₂ l₂ =>
        simp only [List.map_cons, List.cons.injEq] at h₁ h₂
        have e := ih (p, q₁) (by simp) q₂.2 (hf (p, q₂) (by simp))
        rw [ihl h₁.2 h₂.2 (fun p hp => ih p (by simp [hp])) (fun p hp => hf p (by simp [hp]))]
        obtain ⟨k₁, c₁⟩ := q₁; obtain ⟨k₂, c₂⟩ := q₂
        simp_all

/-- Forcing is deterministic. -/
theorem Forces.unique {t r : Trie α} (h : Forces t r) : ∀ {r'}, Forces t r' → r = r' := by
  induction h with
  | lazy _ ih => intro r' h'; cases h'; exact ih ‹_›
  | chain _ ih => intro r' h'; cases h'; rw [ih ‹_›]
  | node hk _ ih =>
    intro r' h'
    cases h' with
    | node hk' hf' =>
      rw [Array.toList_inj.1 (eq_of_forces_zip hk hk' (fun p hp r h => ih p hp h) hf')]
  | suffix => intro r' h'; cases h'; rfl

theorem mem_zip_self {l : List β} {p : β × β} (h : p ∈ l.zip l) : p.1 = p.2 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact ih h

/-- The children `cs` force to `cs'`. -/
def ForcesCh (cs cs' : Array (Key × Trie α)) : Prop :=
  cs.toList.map (·.1) = cs'.toList.map (·.1) ∧ ∀ p ∈ cs.toList.zip cs'.toList, Forces p.1.2 p.2.2

theorem forces_mkT (vs : Array α) {cs cs' : Array (Key × Trie α)} (h : ForcesCh cs cs') :
    Forces (mkT vs cs) (mkT vs cs') := by
  have hsz : cs.size = cs'.size := by simpa using congrArg List.length h.1
  unfold mkT
  split <;> split
  · rename_i hc _
    have hk : cs[0].1 = cs'[0].1 := by
      have := congrArg (·[0]?) h.1
      simpa [hc.2, ← hsz] using this
    rw [hk]
    refine .chain (h.2 (cs[0], cs'[0]) ?_)
    rw [List.mem_iff_getElem]
    exact ⟨0, by simp [hc.2, ← hsz], by simp⟩
  · rename_i hc hc'; exact absurd ⟨hc.1, hsz ▸ hc.2⟩ hc'
  · rename_i hc hc'; exact absurd ⟨hc'.1, hsz ▸ hc'.2⟩ hc
  · exact .node h.1 h.2

theorem forcesCh_self {cs : Array (Key × Trie α)} (h : ∀ p ∈ cs.toList, Forces p.2 p.2) :
    ForcesCh cs cs :=
  ⟨rfl, fun p hp => by
    have := mem_zip_self hp
    rw [← this]
    exact h p.1 (List.of_mem_zip hp).1⟩

theorem Den.forces_self [BEq α] {L : List (Entry α)} {i : Nat} {t : Trie α} (h : Den L i t) :
    Forces t t := by
  induction h with
  | suffix => exact .suffix
  | node L i cs _ _ _ _ ih => exact forces_mkT _ (forcesCh_self ih)

/-! ## Merging -/

section
variable [BEq α]

/-- Relates two lists elementwise. -/
inductive Rel2 (R : β → γ → Prop) : List β → List γ → Prop
  | nil : Rel2 R [] []
  | cons {a : β} {b : γ} {l : List β} {l' : List γ} :
      R a b → Rel2 R l l' → Rel2 R (a :: l) (b :: l')

theorem exists_forall₂ {l : List β} {Q : β → γ → Prop} (h : ∀ x ∈ l, ∃ y, Q x y) :
    ∃ l', Rel2 Q l l' := by
  induction l with
  | nil => exact ⟨[], .nil⟩
  | cons x l ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨l', hl'⟩ := ih fun x hx => h x (by simp [hx])
    exact ⟨y :: l', .cons hy hl'⟩

theorem filter_nodup {l : List (Key × β)} (hs : (l.map (·.1)).Nodup) (k : Key) :
    (l.filter (·.1 == k) = [] ∧ k ∉ l.map (·.1)) ∨
      ∃ c, (k, c) ∈ l ∧ l.filter (·.1 == k) = [(k, c)] := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hs
    by_cases hp : p.1 = k
    · subst hp
      have : l.filter (·.1 == p.1) = [] := List.filter_eq_nil_iff.2 fun q hq h => by
        simp only [beq_iff_eq] at h
        exact hs.1 ⟨q, hq, h⟩
      exact .inr ⟨p.2, by simp, by simp [this]⟩
    · rcases ih hs.2 with ⟨h1, h2⟩ | ⟨c, hc, h⟩
      · refine .inl ⟨by simp [hp, h1], ?_⟩
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨Ne.symm hp, h2⟩
      · exact .inr ⟨c, List.mem_cons_of_mem _ hc, by simp [hp, h]⟩

/-- The root entries `cs` of the trie of the entries `L` at depth `i`, in any order. -/
structure Roots (L : List (Entry α)) (i : Nat) (cs : Array (Key × Trie α)) : Prop where
  nodup : (cs.toList.map (·.1)).Nodup
  keys : ∀ k, k ∈ cs.toList.map (·.1) ↔ ∃ e ∈ L, e.1[i]? = some k
  den : ∀ p ∈ cs.toList, Den (sub L i p.1) (i + 1) p.2

theorem Children.roots {L : List (Entry α)} {i : Nat} {cs : Array (Key × Trie α)}
    (hc : Children L i cs) : Roots L i cs :=
  ⟨List.Pairwise.imp (R := (· < ·)) (fun {a b} (h : a < b) (e : a = b) => Key.lt_irrefl a (e ▸ h))
    hc.sorted, hc.keys, hc.den⟩

theorem Rel2.imp {R S : β → γ → Prop} {l : List β} {l' : List γ} (h : Rel2 R l l')
    (hRS : ∀ a b, R a b → S a b) : Rel2 S l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hRS _ _ hab) ih

/-- The children of all modules with key `k` at depth `i` are the tries of their entries. -/
theorem group_den {Es : List (List (Entry α))} {CSs : List (Array (Key × Trie α))} {i : Nat}
    (h : Rel2 (fun E cs => Roots E i cs) Es CSs) (k : Key) :
    ∃ Es', Rel2 (fun E t => Den E (i + 1) t) Es'
        (((CSs.flatMap (·.toList)).filter (·.1 == k)).map (·.2)) ∧
      Es'.flatten = sub Es.flatten i k := by
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons E cs Es CSs hc _ ih =>
    obtain ⟨Es', h', hf⟩ := ih
    simp only [List.flatMap_cons, List.filter_append, List.map_append]
    rcases filter_nodup hc.nodup k with ⟨h1, h2⟩ | ⟨c, hm, h1⟩
    · refine ⟨Es', by simpa [h1] using h', ?_⟩
      have : E.filter (fun e => e.1[i]? == some k) = [] := List.filter_eq_nil_iff.2 fun e he h => by
        simp only [beq_iff_eq] at h
        exact h2 ((hc.keys k).2 ⟨e, he, h⟩)
      rw [hf]
      simp only [List.flatten_cons, sub, List.filter_append, this, List.nil_append]
    · refine ⟨sub E i k :: Es', ?_, ?_⟩
      · rw [h1]
        exact .cons (hc.den (k, c) hm) h'
      · rw [List.flatten_cons, hf]
        simp only [sub, List.flatten_cons, List.filter_append]

theorem keys_flat {Es : List (List (Entry α))} {CSs : List (Array (Key × Trie α))} {i : Nat}
    (h : Rel2 (fun E cs => Roots E i cs) Es CSs) (k : Key) :
    k ∈ (CSs.flatMap (·.toList)).map (·.1) ↔ ∃ e ∈ Es.flatten, e.1[i]? = some k := by
  induction h with
  | nil => simp
  | @cons E cs Es CSs hc _ ih =>
    simp only [List.flatMap_cons, List.map_append, List.mem_append, List.flatten_cons]
    rw [ih, hc.keys]
    constructor
    · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
      · exact ⟨e, .inl he, h⟩
      · exact ⟨e, .inr he, h⟩
    · rintro ⟨e, he | he, h⟩
      · exact .inl ⟨e, he, h⟩
      · exact .inr ⟨e, he, h⟩

end

section
variable [BEq α]

theorem Rel2.length_eq {R : β → γ → Prop} {l : List β} {l' : List γ} (h : Rel2 R l l') :
    l.length = l'.length := by
  induction h <;> simp_all

theorem Rel2.of_map_snd {R : β → γ → Prop} {l : List β} {l' : List γ} (h : Rel2 R l l')
    (g : β → δ) : (List.zipWith (fun a b => (g a, b)) l l').map (·.2) = l' := by
  induction h <;> simp_all

theorem unfold_rel {Es : List (List (Entry α))} {ts : List (Trie α)} {i : Nat}
    (h : Rel2 (fun E t => Den E i t) Es ts) :
    ∃ CSs, Rel2 (fun E cs => Children E i cs) Es CSs ∧
      ts.map Trie.unfold = List.zipWith (fun E cs => (vals E i, cs)) Es CSs := by
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | cons hd _ ih =>
    obtain ⟨cs, hc, hu⟩ := hd.unfold
    obtain ⟨CSs, hCSs, he⟩ := ih
    exact ⟨cs :: CSs, .cons hc hCSs, by simp [hu, he]⟩

theorem length_flatten_ge {Es : List (List (Entry α))} {ts : List (Trie α)} {i : Nat}
    (h : Rel2 (fun E t => Den E i t) Es ts) : ts.length ≤ Es.flatten.length := by
  induction h with
  | nil => simp
  | cons hd _ ih =>
    have := hd.ne_nil
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have : 0 < List.length _ := List.length_pos_iff.2 this
    omega

end

section
variable [BEq α] [PartialEquivBEq α]

theorem vals_append (L L' : List (Entry α)) (i : Nat) :
    vals (L ++ L') i = (vals L' i).foldl insertVal (vals L i) := by
  have h : ∀ L : List (Entry α),
      (vals L i).toList = ((L.filter fun e => e.1.size ≤ i).map (·.2)).foldl insV [] := by
    intro L; simp [vals, foldl_insertVal]
  rw [← Array.foldl_toList, foldl_insertVal, h L', h L, foldl_foldl_insV]
  simp [vals, foldl_insertVal, List.filter_append]

theorem foldl_vals {R : List (Entry α) → Array (Key × Trie α) → Prop} {Es CSs} {i : Nat}
    (h : Rel2 R Es CSs) (Pre : List (Entry α))
    (g : Array α → Array α × Array (Key × Trie α) → Array α)
    (hg : ∀ acc x, g acc x = if acc.isEmpty then x.1 else x.1.foldl insertVal acc) :
    (List.zipWith (fun E cs => (vals E i, cs)) Es CSs).foldl g (vals Pre i) =
      vals (Pre ++ Es.flatten) i := by
  induction h generalizing Pre with
  | nil => simp
  | @cons E cs Es CSs _ _ ih =>
    simp only [List.zipWith_cons_cons, List.foldl_cons, List.flatten_cons]
    have : g (vals Pre i) (vals E i, cs) = vals (Pre ++ E) i := by
      rw [hg, vals_append]
      split
      · rename_i he
        rw [Array.isEmpty_iff] at he
        rw [he]
        have := vals_append [] E i
        simp only [List.nil_append, show vals ([] : List (Entry α)) i = #[] from rfl] at this
        exact this
      · rfl
    rw [this, ih, List.append_assoc]

end

/-- Strictly sorted keys from `qsort` on keys without duplicates. -/
theorem sorted_of_qsort (G : Array (Key × β)) (hnd : (G.toList.map (·.1)).Nodup) :
    ((G.qsort fun x1 x2 => decide (x1.1 < x2.1)).toList.map (·.1)).Pairwise (· < ·) ∧
      (G.qsort fun x1 x2 => decide (x1.1 < x2.1)).toList.Perm G.toList := by
  obtain ⟨hperm, hs⟩ := QS.qsort_spec (fun x1 x2 : Key × β => decide (x1.1 < x2.1))
    (fun a b h => by simp at *; exact Key.lt_asymm h)
    (fun a b c h1 h2 => by simp at *; exact Key.lt_trans h1 h2) G
  have hperm := Array.perm_iff_toList_perm.1 hperm
  refine ⟨?_, hperm⟩
  have hnd' := (hperm.map (·.1)).nodup_iff.2 hnd
  rw [List.pairwise_iff_getElem]
  intro a b ha hb hab
  simp only [List.length_map, Array.length_toList] at ha hb
  simp only [List.getElem_map, Array.getElem_toList]
  have h1 := hs a b hb hab
  have h2 : (G.qsort fun x1 x2 => decide (x1.1 < x2.1))[a].1 ≠
      (G.qsort fun x1 x2 => decide (x1.1 < x2.1))[b].1 := by
    intro h
    have := (List.Nodup.getElem_inj hnd' (i := a) (j := b) (hi := by simpa using ha)
      (hj := by simpa using hb)).1 (by simpa using h)
    omega
  simp only [decide_eq_true_eq] at h1
  exact (Key.lt_total h2).resolve_right h1

theorem rel2_zip {Q : β → γ → Prop} {l : List β} {l' : List γ} (h : Rel2 Q l l')
    (f : β → δ) (g : β → γ → ε) :
    ∀ p ∈ (l.map f).zip (List.zipWith g l l'), ∃ a b, Q a b ∧ p = (f a, g a b) := by
  induction h with
  | nil => simp
  | @cons a b l l' hab _ ih =>
    intro p hp
    simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨a, b, hab, rfl⟩
    · exact ih p hp

theorem rel2_mem {Q : β → γ → Prop} {l : List β} {l' : List γ} (h : Rel2 Q l l')
    (g : β → γ → ε) : ∀ p ∈ List.zipWith g l l', ∃ a b, Q a b ∧ p = g a b := by
  induction h with
  | nil => simp
  | @cons a b l l' hab _ ih =>
    intro p hp
    simp only [List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨a, b, hab, rfl⟩
    · exact ih p hp

theorem rel2_map_fst {Q : β × γ → δ → Prop} {l : List (β × γ)} {l' : List δ} (h : Rel2 Q l l') :
    (List.zipWith (fun a b => (a.1, b)) l l').map (·.1) = l.map (·.1) := by
  induction h <;> simp_all

theorem rel2_singleton {Q : β → γ → Prop} {l : List β} {c : γ} (h : Rel2 Q l [c]) :
    ∃ a, l = [a] ∧ Q a c := by
  cases h with
  | cons hab h => cases h; exact ⟨_, rfl, hab⟩

/-- The step of `mergeTries` folding in the values of a trie. -/
def valsStep [BEq α] (acc : Array α) (x : Array α × Array (Key × Trie α)) : Array α :=
  if acc.isEmpty then x.1 else x.1.foldl insertVal acc

theorem mergeTries_unfold [BEq α] (ts : Array (Trie α)) :
    ∃ hP, mergeTries ts = mkT ((ts.map Trie.unfold).foldl valsStep #[])
      (((groupByKey ((ts.map Trie.unfold).map (·.2)) (fun x => x.weight < maxWeight ts) hP).qsort
        fun x1 x2 => decide (x1.1 < x2.1)).map fun kg => (kg.1, mergeGroup kg.2.1)) := by
  refine ⟨?_, ?_⟩
  rotate_left
  rw [mergeTries]
  rfl

section
variable [BEq α] [PartialEquivBEq α]

/--
Merging the tries of several modules at depth `i` and forcing all `lazy` nodes gives the trie of
the entries of all modules in order.
-/
theorem mergeTries_spec (N i : Nat) (ts : Array (Trie α)) (Es : List (List (Entry α)))
    (hden : Rel2 (fun E t => Den E i t) Es ts.toList) (hsize : 2 ≤ ts.size)
    (hb : ∀ e ∈ Es.flatten, e.1.size ≤ i + N) :
    ∃ r, Forces (mergeTries ts) r ∧ Den Es.flatten i r := by
  obtain ⟨CSs, hCh, hu⟩ := unfold_rel hden
  have hR := hCh.imp fun _ _ h => h.roots
  have hlen : 2 ≤ Es.flatten.length := by
    have := length_flatten_ge hden; rw [Array.length_toList] at this; omega
  obtain ⟨hP, heq⟩ := mergeTries_unfold ts
  rw [heq]
  have hnodes : (ts.map Trie.unfold).toList = List.zipWith (fun E cs => (vals E i, cs)) Es CSs := by
    rw [← hu]; simp
  have hvs : (ts.map Trie.unfold).foldl valsStep #[] = vals Es.flatten i := by
    have := foldl_vals (i := i) hCh [] valsStep (fun acc x => rfl)
    rw [List.nil_append, ← hnodes, Array.foldl_toList] at this
    exact this
  have hF : ((ts.map Trie.unfold).map (·.2)).toList.flatMap (·.toList) =
      CSs.flatMap (·.toList) := by
    rw [Array.toList_map, hnodes, hCh.of_map_snd]
  have hG := groupByKey_spec ((ts.map Trie.unfold).map (·.2)) (fun x => x.weight < maxWeight ts) hP
  rw [hF] at hG
  rw [hvs]
  generalize groupByKey ((ts.map Trie.unfold).map (·.2)) (fun x => x.weight < maxWeight ts) hP = G
    at hG ⊢
  obtain ⟨hsorted, hperm⟩ := sorted_of_qsort G hG.nodup
  generalize (G.qsort fun x1 x2 => decide (x1.1 < x2.1)) = G' at hsorted hperm ⊢
  have hG' := hG.perm hperm
  have hgroups : ∀ x ∈ G'.toList, ∃ r, Forces (mergeGroup x.2.1) r ∧
      Den (sub Es.flatten i x.1) (i + 1) r := by
    intro x hx
    obtain ⟨Es', hEs', hfl⟩ := group_den hR x.1
    rw [← hG'.grp x hx] at hEs'
    rw [← hfl]
    have hpos := x.2.2.1
    rw [mergeGroup]
    split
    · rename_i h1
      have : x.2.1.toList = [x.2.1[0]] := by
        apply List.ext_getElem <;> simp [h1]
        intro n h2; subst h2; rfl
      rw [this] at hEs'
      obtain ⟨E', rfl, hd⟩ := rel2_singleton hEs'
      exact ⟨_, hd.forces_self, by simpa using hd⟩
    · rename_i h1
      have hsz : 2 ≤ x.2.1.size := by omega
      obtain ⟨E', Es'', rfl⟩ : ∃ E' Es'', Es' = E' :: Es'' := by
        cases Es' with
        | nil => have := hEs'.length_eq; simp at this; omega
        | cons E' Es'' => exact ⟨_, _, rfl⟩
      have hne : E' ≠ [] := by
        generalize x.2.1.toList = l at hEs'
        cases hEs' with
        | cons hd _ => exact hd.ne_nil
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
      have hsub : ∀ e ∈ (E' :: Es'').flatten, e ∈ Es.flatten ∧ e.1[i]? = some x.1 := by
        intro e he; rw [hfl] at he
        simp only [sub, List.mem_filter, beq_iff_eq] at he; exact he
      obtain ⟨he1, he2⟩ := hsub e (by simp [he])
      have hie : i < e.1.size := by
        rcases Nat.lt_or_ge i e.1.size with h | h
        · exact h
        · simp [Array.getElem?_eq_none h] at he2
      have hN : 0 < N := by have := hb e he1; omega
      obtain ⟨r, hr, hd⟩ := mergeTries_spec (N - 1) (i + 1) x.2.1 (E' :: Es'') hEs' hsz
        (fun e he => by
          obtain ⟨he1, he2⟩ := hsub e he
          have := hb e he1
          have : i < e.1.size := by
            rcases Nat.lt_or_ge i e.1.size with h | h
            · exact h
            · simp [Array.getElem?_eq_none h] at he2
          omega)
      exact ⟨r, .lazy hr, hd⟩
  obtain ⟨rs, hrs⟩ := exists_forall₂
    (Q := fun (x : Key × Grp fun x : Trie α => x.weight < maxWeight ts) r =>
    Forces (mergeGroup x.2.1) r ∧
    Den (sub Es.flatten i x.1) (i + 1) r) hgroups
  refine ⟨mkT (vals Es.flatten i) (List.zipWith (fun kg r => (kg.1, r)) G'.toList rs).toArray,
    ?_, Den.node' hlen ⟨?_, fun k => ?_, fun p hp => ?_⟩⟩
  · refine forces_mkT _ ⟨?_, fun p hp => ?_⟩
    · simp [rel2_map_fst hrs, Function.comp_def]
    · simp only [Array.toList_map] at hp
      obtain ⟨a, b, hab, rfl⟩ := rel2_zip hrs _ _ p hp
      exact hab.1
  · simpa [rel2_map_fst hrs] using hsorted
  · simp only [rel2_map_fst hrs]
    rw [hperm.map _ |>.mem_iff, hG.mem, keys_flat hR]
  · obtain ⟨a, b, hab, rfl⟩ := rel2_mem hrs _ p hp
    exact hab.2
termination_by N
decreasing_by omega

end
end DiscrTreeMergeSpec

/-! ## Roots -/

namespace DiscrTreeMergeSpec
variable {α β γ : Type}

/--
The lookup laws of `PersistentHashMap` for `Key`. Its operations are implemented by `partial`
functions, so these laws cannot be proved here and are assumed instead.
-/
structure MapLaws (β : Type) : Prop where
  find?_empty : ∀ k : Key, ({} : PersistentHashMap Key β).find? k = none
  find?_insert : ∀ (m : PersistentHashMap Key β) (k : Key) (v : β) (k' : Key),
    (m.insert k v).find? k' = if k == k' then some v else m.find? k'
  find?_alter : ∀ (m : PersistentHashMap Key β) (k : Key) (f : Option β → Option β) (k' : Key),
    (m.alter k f).find? k' = if k == k' then f (m.find? k) else m.find? k'

theorem forIn_array_inv (xs : Array γ) (f : γ → β → Id (ForInStep β))
    (I : List γ → β → Prop) (pre : List γ) (init : β) (h0 : I pre init)
    (hs : ∀ a, a ∈ xs → ∀ b pre', I pre' b → ∃ b', f a b = .yield b' ∧ I (pre' ++ [a]) b') :
    I (pre ++ xs.toList) (forIn xs init f).run :=
  forIn'_array_inv xs (fun a _ b => f a b) I pre init h0 fun a m b pre' h => hs a m b pre' h

section
variable [BEq α]

/-- The trie of the entries `L` under the root key `k`. -/
def SeqSpec (L : List (Entry α)) (t? : Option (Trie α)) (k : Key) : Prop :=
  match t? with
  | none => sub L 0 k = []
  | some t => Den (sub L 0 k) 1 t

theorem seqSpec_insertKeyValue (laws : MapLaws (Trie α)) {d : DiscrTree α} {L : List (Entry α)}
    (h : ∀ k, SeqSpec L (d.root.find? k) k) (e : Entry α) (he : 0 < e.1.size) (k : Key) :
    SeqSpec (L ++ [e]) ((d.insertKeyValue e.1 e.2).root.find? k) k := by
  have hne : e.1.isEmpty = false := by
    rw [Bool.eq_false_iff]; intro h; rw [Array.isEmpty_iff] at h; simp [h] at he
  simp only [insertKeyValue, hne, Bool.false_eq_true, ↓reduceIte, laws.find?_alter]
  rw [getElem!_pos e.1 0 he]
  by_cases hk : e.1[0] = k
  · subst hk
    have hs := h e.1[0]
    simp only [BEq.rfl, ↓reduceIte]
    revert hs
    cases d.root.find? e.1[0] with
    | none =>
      intro hs
      simp only [SeqSpec] at hs ⊢
      rw [sub_append, hs]
      simp only [Array.getElem?_eq_getElem he, BEq.rfl, ↓reduceIte, List.nil_append]
      exact .suffix e.1 e.2 1
    | some t =>
      intro hs
      simp only [SeqSpec] at hs ⊢
      rw [sub_append]
      simp only [Array.getElem?_eq_getElem he, BEq.rfl, ↓reduceIte]
      exact insertAux_den e.1 e.2 1 _ t hs
  · simp only [beq_iff_eq, hk, ↓reduceIte]
    have := h k
    revert this
    have hne' : e.1[0]? ≠ some k := by simp [Array.getElem?_eq_getElem he, hk]
    cases d.root.find? k with
    | none => simp only [SeqSpec]; intro hs; rw [sub_append_of_ne hne', hs]
    | some t => simp only [SeqSpec]; intro hs; rwa [sub_append_of_ne hne']

theorem seqSpec_foldl (laws : MapLaws (Trie α)) (es : List (Entry α))
    (hne : ∀ e ∈ es, 0 < e.1.size) (L : List (Entry α)) (d : DiscrTree α)
    (h : ∀ k, SeqSpec L (d.root.find? k) k) (k : Key) :
    SeqSpec (L ++ es) ((es.foldl (fun d e => d.insertKeyValue e.1 e.2) d).root.find? k) k := by
  induction es generalizing L d with
  | nil => simpa using h k
  | cons e es ih =>
    simp only [List.foldl_cons]
    have := ih (fun e he => hne e (by simp [he])) (L ++ [e]) _
      (seqSpec_insertKeyValue laws h e (hne e (by simp)))
    simpa using this

theorem seqSpec_empty (laws : MapLaws (Trie α)) (k : Key) :
    SeqSpec [] (({} : DiscrTree α).root.find? k) k := by
  show SeqSpec [] (({} : PersistentHashMap Key (Trie α)).find? k) k
  rw [laws.find?_empty]; rfl

theorem SeqSpec.eq_none_iff {L : List (Entry α)} {t? : Option (Trie α)} {k : Key}
    (h : SeqSpec L t? k) : t? = none ↔ sub L 0 k = [] := by
  cases t? with
  | none => simpa [SeqSpec] using h
  | some t => simp only [SeqSpec] at h; simpa using h.ne_nil

/-- `moduleRootsOf` returns the root entries of the trie of its entries. -/
theorem moduleRootsOf_spec (laws : MapLaws (Trie α)) (es : Array (Array Key × α))
    (hne : ∀ e ∈ es, 0 < e.1.size) : Roots es.toList 0 (moduleRootsOf es) := by
  have key : ∀ s : DiscrTree α × Std.HashMap Key Nat × Nat,
      ((∀ k, SeqSpec es.toList (s.1.root.find? k) k) ∧
        ∀ k, k ∈ s.2.1 ↔ ∃ e ∈ es.toList, e.1[0]? = some k) →
      Roots es.toList 0 ((s.2.1.toArray.qsort fun x1 x2 => decide (x1.2 < x2.2)).map
        fun x => (x.1, (s.1.root.find? x.1).getD default)) := by
    rintro ⟨d, last, i⟩ ⟨hd, hl⟩
    have hperm := Array.perm_iff_toList_perm.1 (QS.qsort_spec
      (fun x1 x2 : Key × Nat => decide (x1.2 < x2.2)) (by intro a b h; simp at *; omega)
      (by intro a b c h1 h2; simp at *; omega) last.toArray).1
    simp only [Std.HashMap.toList_toArray] at hperm
    have hkeys : ∀ k, k ∈ last.toList.map (·.1) ↔ k ∈ last := by
      intro k
      rw [show (last.toList.map (·.1)) = last.toList.map Prod.fst from rfl,
        Std.HashMap.map_fst_toList_eq_keys, Std.HashMap.mem_keys]
    refine ⟨?_, fun k => ?_, fun p hp => ?_⟩
    · simp only [Array.toList_map, List.map_map, Function.comp_def]
      refine (hperm.map _).nodup_iff.2 ?_
      have := Std.HashMap.distinct_keys_toList (m := last)
      exact List.pairwise_map.2 (this.imp fun {a b} h e => by simp [e] at h)
    · simp only [Array.toList_map, List.map_map, Function.comp_def]
      rw [(hperm.map _).mem_iff, hkeys, hl]
    · simp only [Array.toList_map, List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      have hx := (hkeys x.1).1 (List.mem_map_of_mem (hperm.mem_iff.1 hx))
      obtain ⟨e, he, hek⟩ := (hl x.1).1 hx
      have hsub : sub es.toList 0 x.1 ≠ [] := by
        intro h
        have := List.filter_eq_nil_iff.1 h e he
        simp [hek] at this
      have hs := hd x.1
      revert hs
      cases d.root.find? x.1 with
      | none => intro hs; exact absurd hs hsub
      | some t => intro hs; exact hs
  simp only [moduleRootsOf, Id.run]
  apply key
  refine forIn_array_inv es _
    (fun (pre : List (Entry α)) (s : DiscrTree α × Std.HashMap Key Nat × Nat) =>
      (∀ k, SeqSpec pre (s.1.root.find? k) k) ∧ ∀ k, k ∈ s.2.1 ↔ ∃ e ∈ pre, e.1[0]? = some k)
    [] _ ⟨seqSpec_empty laws, by simp⟩ ?_
  intro x hx s pre ⟨hd, hl⟩
  have hx := hne x hx
  split
  · refine ⟨_, rfl, fun k => seqSpec_insertKeyValue laws hd x hx k, fun k => ?_⟩
    simp only [Std.HashMap.mem_insert, hl, List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | ⟨e, he, h⟩)
      · exact ⟨x, .inr rfl, by simp at h; simp [Array.getElem?_eq_getElem hx, h]⟩
      · exact ⟨e, .inl he, h⟩
    · rintro ⟨e, he | rfl, h⟩
      · exact .inr ⟨e, he, h⟩
      · simp [Array.getElem?_eq_getElem hx] at h; exact .inl (by simp [h])
  · contradiction

end

theorem find?_foldl_insert (laws : MapLaws β) (L : List (Key × γ)) (f : γ → β)
    (m : PersistentHashMap Key β) (hnd : (L.map (·.1)).Nodup) (k : Key) :
    (∀ g, (k, g) ∈ L → (L.foldl (fun root x => root.insert x.1 (f x.2)) m).find? k = some (f g)) ∧
      (k ∉ L.map (·.1) →
        (L.foldl (fun root x => root.insert x.1 (f x.2)) m).find? k = m.find? k) := by
  induction L generalizing m with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ih1, ih2⟩ := ih (m.insert x.1 (f x.2)) hnd.2
    simp only [List.foldl_cons, List.mem_cons, List.map_cons, not_or]
    refine ⟨fun g hg => ?_, fun hk => ?_⟩
    · rcases hg with rfl | hg
      · rw [ih2 hnd.1, laws.find?_insert]; simp
      · exact ih1 g hg
    · rw [ih2 hk.2, laws.find?_insert]
      simp [Ne.symm hk.1]

theorem exists_bound (L : List (Entry α)) (i : Nat) : ∃ N, ∀ e ∈ L, e.1.size ≤ i + N := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons e L ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + e.1.size, fun e' he' => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · omega
    · have := hN e' he'; omega

section
variable [BEq α] [PartialEquivBEq α]

theorem mergeGroup_spec (N i : Nat) (g : Array (Trie α)) (Es : List (List (Entry α)))
    (hden : Rel2 (fun E t => Den E i t) Es g.toList) (hpos : 0 < g.size)
    (hb : ∀ e ∈ Es.flatten, e.1.size ≤ i + N) :
    ∃ r, Forces (mergeGroup g) r ∧ Den Es.flatten i r := by
  rw [mergeGroup]
  split
  · rename_i h1
    have : g.toList = [g[0]] := by
      apply List.ext_getElem <;> simp [h1]
      intro n h2; subst h2; rfl
    rw [this] at hden
    obtain ⟨E', rfl, hd⟩ := rel2_singleton hden
    exact ⟨_, hd.forces_self, by simpa using hd⟩
  · obtain ⟨r, hr, hd⟩ := mergeTries_spec N i g Es hden (by omega) hb
    exact ⟨r, .lazy hr, hd⟩

/-- Inserts the entries of a module in order. -/
def insertModule (d : DiscrTree α) (es : Array (Array Key × α)) : DiscrTree α :=
  es.foldl (fun d e => d.insertKeyValue e.1 e.2) d

omit [PartialEquivBEq α] in
theorem seqSpec_insertModules (laws : MapLaws (Trie α)) (ms : List (Array (Array Key × α)))
    (hne : ∀ es ∈ ms, ∀ e ∈ es, 0 < e.1.size) (L : List (Entry α)) (d : DiscrTree α)
    (h : ∀ k, SeqSpec L (d.root.find? k) k) (k : Key) :
    SeqSpec (L ++ (ms.map Array.toList).flatten) ((ms.foldl insertModule d).root.find? k) k := by
  induction ms generalizing L d with
  | nil => simpa using h k
  | cons es ms ih =>
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons, ← List.append_assoc]
    refine ih (fun es hes => hne es (by simp [hes])) _ _ (fun k => ?_)
    rw [insertModule, ← Array.foldl_toList]
    exact seqSpec_foldl laws es.toList (fun e he => hne es (by simp) e (by simpa using he)) L d h k

omit [PartialEquivBEq α] in
theorem roots_moduleRootsOf (laws : MapLaws (Trie α)) (ms : List (Array (Array Key × α)))
    (hne : ∀ es ∈ ms, ∀ e ∈ es, 0 < e.1.size) :
    Rel2 (fun E R => Roots E 0 R) (ms.map Array.toList) (ms.map moduleRootsOf) := by
  induction ms with
  | nil => exact .nil
  | cons es ms ih =>
    exact .cons (moduleRootsOf_spec laws es (hne es (by simp)))
      (ih fun es hes => hne es (by simp [hes]))

/--
After forcing all `lazy` nodes, the trie under each root key of the merged per-module trees is the
one under this key after inserting the entries of all modules in order.
-/
theorem ofModuleRoots_spec (laws : MapLaws (Trie α)) (mods : Array (Array (Array Key × α)))
    (hne : ∀ es ∈ mods, ∀ e ∈ es, 0 < e.1.size) (k : Key) :
    Option.Rel Forces ((ofModuleRoots (mods.map moduleRootsOf)).root.find? k)
      ((mods.foldl insertModule {}).root.find? k) := by
  let all := (mods.toList.map Array.toList).flatten
  have hne' : ∀ es ∈ mods.toList, ∀ e ∈ es, 0 < e.1.size :=
    fun es hes => hne es (by simpa using hes)
  have hs : SeqSpec all ((mods.foldl insertModule {}).root.find? k) k := by
    rw [← Array.foldl_toList]
    exact seqSpec_insertModules laws mods.toList hne' [] {} (seqSpec_empty laws) k
  generalize (mods.foldl insertModule {}).root.find? k = t? at hs ⊢
  have hR : Rel2 (fun E R => Roots E 0 R) (mods.toList.map Array.toList)
      (mods.map moduleRootsOf).toList := by
    rw [Array.toList_map]
    exact roots_moduleRootsOf laws mods.toList hne'
  have hG := groupByKey_spec (mods.map moduleRootsOf) (fun _ => True) (by simp)
  simp only [ofModuleRoots]
  rw [← Array.foldl_toList]
  generalize groupByKey (mods.map moduleRootsOf) (fun _ => True) _ = G at hG ⊢
  obtain ⟨hfound, hnot⟩ := find?_foldl_insert laws G.toList (fun g => mergeGroup g.1) {}
    hG.nodup k
  by_cases hk : k ∈ G.toList.map (·.1)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
    rw [hfound x.2 hx]
    obtain ⟨Es', hEs', hfl⟩ := group_den hR x.1
    rw [← hG.grp x hx] at hEs'
    obtain ⟨N, hN⟩ := exists_bound Es'.flatten 1
    obtain ⟨r, hr, hd⟩ := mergeGroup_spec N 1 x.2.1 Es' hEs' x.2.2.1 hN
    rw [hfl] at hd
    cases t? with
    | none => simp only [SeqSpec] at hs; rw [hs] at hd; exact absurd rfl hd.ne_nil
    | some t => exact .some (hd.unique hs ▸ hr)
  · rw [hnot hk, laws.find?_empty]
    have hsub : sub all 0 k = [] := by
      apply List.filter_eq_nil_iff.2
      intro e he h
      simp only [beq_iff_eq] at h
      exact hk ((hG.mem k).2 ((keys_flat hR k).2 ⟨e, he, h⟩))
    rw [(hs.eq_none_iff).2 hsub]
    exact .none

end
end DiscrTreeMergeSpec

/-!
## A `==` that is not transitive

With values that are `==` when they differ by at most one, the merge deduplicates the second
module's values `2, 1` to `1` before folding them into the first module's `0`, which drops `2`,
while sequential insertion keeps it.
-/

namespace DiscrTreeMergeSpec.NonTransitive

local instance : BEq Nat := ⟨fun a b => a ≤ b + 1 && b ≤ a + 1⟩

def key : Key := .const `f 0

def mods : Array (Array (Array Key × Nat)) := #[#[(#[key], 0)], #[(#[key], 2), (#[key], 1)]]

#guard ((mods.foldl insertModule {}).getEntriesWithKeys #[key]).toList = [1, 2]
#guard ((ofModuleRoots (mods.map moduleRootsOf)).getEntriesWithKeys #[key]).toList = [1]

end DiscrTreeMergeSpec.NonTransitive
