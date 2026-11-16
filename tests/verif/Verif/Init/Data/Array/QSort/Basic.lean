module

import all Init.Data.Array.QSort.Basic
import Init.Data.Vector.Perm
import Init.Data.Array.Perm

/-!
Verifies `Array.qsort`: for an asymmetric and transitive comparator, it returns a permutation of its
input in which no element is less than an earlier one.
-/

namespace Verif.Array.QSort
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
  | case2 as lo hi w hlo hhi h mid hmid as1 heq hge =>
    rename_i ih1 ih2
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
public theorem qsort_spec (as : Array α) :
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


end Verif.Array.QSort
