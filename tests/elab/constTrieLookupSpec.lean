module
import all Lean.ConstTrie
import all Lean.Data.Name
import all Init.Data.Array.QSort.Basic
import Init.Data.Vector.Perm
import Init.Data.Array.Perm
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
Verifies the lookup logic of the per-module constant prefix tries (`Lean.ConstTrie`): the binary
search over hash-sorted children (`findChildIdx?`), lookup via `ConstTrie.find?` in well-formed
tries, and that `ConstTrie.ofArrays` builds a well-formed trie whose `find?` and `foldlM` agree with
its input. Furthermore, looking up a name in the lazily merged `ImportedConsts` of several module
tries (`ImportedConsts.mergeModuleTreesLazy`) via `ImportedConsts.findEntry?` agrees with the
lookups in the individual tries. Along the way, `Array.qsort` is shown to return a sorted
permutation for comparators that are asymmetric and transitive.
-/

/-! ## `Array.qsort` -/

namespace ConstTrieSpec.QS
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

end ConstTrieSpec.QS

namespace ConstTrieSpec
open Lean Lean.ConstTrie

/-! ## `findChildIdx?` -/

theorem lastPartEq_iff {a b : Name} (ha : a ≠ .anonymous) (hb : b ≠ .anonymous)
    (hp : parentOf a = parentOf b) : lastPartEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp_all [lastPartEq, parentOf]

section
variable {β : Type _} [Inhabited β] (cs : Array β) (keyOf : β → Name) (k : Name)

theorem lowerBound_spec (h : UInt64)
    (sorted : ∀ i j (hij : i ≤ j) (hj : j < cs.size), (keyOf cs[i]).hash ≤ (keyOf cs[j]).hash)
    (lo hi : Nat) (hlh : lo ≤ hi) (hhi : hi ≤ cs.size)
    (hlo : ∀ i (_ : i < lo), (keyOf cs[i]!).hash < h)
    (hhi' : ∀ i (_ : hi ≤ i) (_ : i < cs.size), h ≤ (keyOf cs[i]!).hash) :
    let r := findChildIdx?.lowerBound cs keyOf h lo hi
    r ≤ cs.size ∧ (∀ i (_ : i < r), (keyOf cs[i]!).hash < h) ∧
      (∀ i (_ : r ≤ i) (_ : i < cs.size), h ≤ (keyOf cs[i]!).hash) := by
  induction lo, hi using findChildIdx?.lowerBound.induct cs keyOf h with
  | case1 lo hi hlt mid hmid ih =>
    simp only [mid] at hmid ih
    rw [findChildIdx?.lowerBound]; simp only [hlt, ↓reduceDIte, hmid, ↓reduceIte]
    apply ih (by omega) hhi _ hhi'
    intro i hi'
    by_cases him : i = (lo + hi) / 2
    · subst him; exact hmid
    · by_cases hil : i < lo
      · exact hlo i hil
      · have hm : (lo + hi) / 2 < cs.size := by omega
        have hs := sorted i _ (by omega) hm
        simp only [getElem!_pos cs i (by omega), getElem!_pos cs ((lo + hi) / 2) hm] at hmid ⊢
        simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
        omega
  | case2 lo hi hlt mid hmid ih =>
    simp only [mid] at hmid ih
    rw [findChildIdx?.lowerBound]; simp only [hlt, ↓reduceDIte, hmid, ↓reduceIte]
    apply ih (by omega) (by omega) hlo
    intro i hi1 hi2
    have hm : (lo + hi) / 2 < cs.size := by omega
    have hs := sorted _ i hi1 hi2
    simp only [getElem!_pos cs i hi2, getElem!_pos cs ((lo + hi) / 2) hm] at hmid ⊢
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
    omega
  | case3 lo hi hlt =>
    rw [findChildIdx?.lowerBound]; simp only [hlt, ↓reduceDIte]
    refine ⟨by omega, hlo, fun i hi hi2 => hhi' i (by omega) hi2⟩

theorem scanRun_spec
    (sorted : ∀ i j (hij : i ≤ j) (hj : j < cs.size), (keyOf cs[i]).hash ≤ (keyOf cs[j]).hash)
    (j : Nat)
    (hge : ∀ i (_ : j ≤ i) (_ : i < cs.size), k.hash ≤ (keyOf cs[i]).hash)
    (hne : ∀ i (_ : i < j) (_ : i < cs.size), keyOf cs[i] ≠ k)
    (lpe : ∀ i (_ : i < cs.size), lastPartEq (keyOf cs[i]) k = true ↔ keyOf cs[i] = k) :
    match findChildIdx?.scanRun cs keyOf k k.hash j with
    | some r => ∃ _ : r < cs.size, keyOf cs[r] = k
    | none => ∀ i (_ : i < cs.size), keyOf cs[i] ≠ k := by
  induction j using findChildIdx?.scanRun.induct cs keyOf k k.hash with
  | case1 j hj c hc heq =>
    simp only [c] at hc heq
    rw [findChildIdx?.scanRun]; simp only [hj, ↓reduceDIte]
    simp only [hc, heq, ↓reduceIte]
    simp only [getElem!_pos cs j hj] at heq
    exact ⟨hj, (lpe j hj).1 heq⟩
  | case2 j hj c hc heq ih =>
    simp only [c] at hc heq
    rw [findChildIdx?.scanRun]; simp only [hj, ↓reduceDIte]
    simp only [hc, heq, ↓reduceIte, Bool.false_eq_true]
    simp only [getElem!_pos cs j hj] at heq
    apply ih (fun i hi hi2 => hge i (by omega) hi2)
    intro i hi hi2
    by_cases hij : i = j
    · subst hij; intro h; exact heq ((lpe i hi2).2 h)
    · exact hne i (by omega) hi2
  | case3 j hj c hc =>
    simp only [c] at hc
    rw [findChildIdx?.scanRun]; simp only [hj, ↓reduceDIte]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    simp only [getElem!_pos cs j hj, beq_iff_eq] at hc
    intro i hi
    by_cases hij : i < j
    · exact hne i hij hi
    · have h1 := hge j (by omega) hj
      have h2 := sorted j i (by omega) hi
      intro he
      rw [he] at h2
      simp only [UInt64.le_iff_toNat_le] at h1 h2
      exact hc (UInt64.toNat_inj.1 (by omega))
  | case4 j hj =>
    rw [findChildIdx?.scanRun]
    simp only [hj, ↓reduceDIte]
    intro i hi
    exact hne i (by omega) hi

/-- Specification of `findChildIdx?`, without assuming distinct keys. -/
theorem findChildIdx?_spec
    (sorted : ∀ i j (hij : i ≤ j) (hj : j < cs.size), (keyOf cs[i]).hash ≤ (keyOf cs[j]).hash)
    (hk : k ≠ .anonymous)
    (ext : ∀ c ∈ cs, keyOf c ≠ .anonymous ∧ parentOf (keyOf c) = parentOf k) :
    match findChildIdx? cs keyOf k with
    | some r => ∃ _ : r < cs.size, keyOf cs[r] = k
    | none => ∀ c ∈ cs, keyOf c ≠ k := by
  obtain ⟨-, hlt, hge⟩ := lowerBound_spec cs keyOf k.hash sorted 0 cs.size (by omega) (by omega)
    (fun _ h => absurd h (by omega)) (fun _ h1 h2 => absurd h2 (by omega))
  have := scanRun_spec cs keyOf k sorted (findChildIdx?.lowerBound cs keyOf k.hash 0 cs.size)
    (fun i h1 h2 => by grind) (fun i h1 h2 he => by grind)
    (fun i hi =>
      lastPartEq_iff (ext _ (Array.getElem_mem hi)).1 hk (ext _ (Array.getElem_mem hi)).2)
  unfold findChildIdx?
  split at this <;> grind [Array.mem_iff_getElem]

/-- With pairwise distinct keys, `findChildIdx?` returns exactly the index of the key. -/
theorem findChildIdx?_eq_some_iff
    (sorted : ∀ i j (hij : i ≤ j) (hj : j < cs.size), (keyOf cs[i]).hash ≤ (keyOf cs[j]).hash)
    (distinct : ∀ i j (hi : i < cs.size) (hj : j < cs.size), keyOf cs[i] = keyOf cs[j] → i = j)
    (hk : k ≠ .anonymous)
    (ext : ∀ c ∈ cs, keyOf c ≠ .anonymous ∧ parentOf (keyOf c) = parentOf k) (r : Nat) :
    findChildIdx? cs keyOf k = some r ↔ ∃ _ : r < cs.size, keyOf cs[r] = k := by
  have := findChildIdx?_spec cs keyOf k sorted hk ext
  split at this <;> grind

theorem findChildIdx?_eq_none_iff
    (sorted : ∀ i j (hij : i ≤ j) (hj : j < cs.size), (keyOf cs[i]).hash ≤ (keyOf cs[j]).hash)
    (hk : k ≠ .anonymous)
    (ext : ∀ c ∈ cs, keyOf c ≠ .anonymous ∧ parentOf (keyOf c) = parentOf k) :
    findChildIdx? cs keyOf k = none ↔ ∀ c ∈ cs, keyOf c ≠ k := by
  have := findChildIdx?_spec cs keyOf k sorted hk ext
  split at this <;> grind
end

/-! ## Name prefixes -/

def pre : Name → Nat → Name
  | n, 0 => n
  | n, k + 1 => pre (parentOf n) k

def IsPre (p n : Name) : Prop := ∃ k, pre n k = p

theorem pre_succ (n : Name) (k : Nat) : pre n (k + 1) = parentOf (pre n k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [pre, ih, pre]

theorem pre_add (n : Name) (a b : Nat) : pre (pre n a) b = pre n (a + b) := by
  induction a generalizing n with
  | zero => simp [pre]
  | succ a ih => rw [pre, ih, Nat.add_right_comm, pre]

theorem depth_parentOf (c : Name) : (parentOf c).getNumParts = c.getNumParts - 1 := by
  cases c <;> simp [parentOf, Name.getNumParts]

theorem depth_pre (n : Name) (k : Nat) : (pre n k).getNumParts = n.getNumParts - k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [pre, ih, depth_parentOf]; omega

theorem eq_anonymous_of_depth {n : Name} (h : n.getNumParts = 0) : n = .anonymous := by
  cases n <;> simp_all [Name.getNumParts]

theorem isPre_refl (n : Name) : IsPre n n := ⟨0, rfl⟩

theorem IsPre.trans {a b c : Name} : IsPre a b → IsPre b c → IsPre a c := by
  rintro ⟨k₁, rfl⟩ ⟨k₂, rfl⟩; exact ⟨k₂ + k₁, (pre_add _ _ _).symm⟩

theorem isPre_parentOf (c : Name) : IsPre (parentOf c) c := ⟨1, rfl⟩

theorem isPre_anonymous (n : Name) : IsPre .anonymous n :=
  ⟨n.getNumParts, eq_anonymous_of_depth (by rw [depth_pre]; omega)⟩

theorem IsPre.depth_le {a n : Name} : IsPre a n → a.getNumParts ≤ n.getNumParts := by
  rintro ⟨k, rfl⟩; rw [depth_pre]; omega

theorem IsPre.eq_of_depth {a b n : Name} (ha : IsPre a n) (hb : IsPre b n)
    (h : a.getNumParts = b.getNumParts) : a = b := by
  obtain ⟨k₁, rfl⟩ := ha; obtain ⟨k₂, rfl⟩ := hb
  rw [depth_pre, depth_pre] at h
  by_cases h₁ : k₁ ≤ n.getNumParts ∧ k₂ ≤ n.getNumParts
  · rw [show k₁ = k₂ by omega]
  · rw [eq_anonymous_of_depth (by rw [depth_pre]; omega : (pre n k₁).getNumParts = 0),
      eq_anonymous_of_depth (by rw [depth_pre]; omega : (pre n k₂).getNumParts = 0)]

theorem depth_of_ne {c : Name} (h : c ≠ .anonymous) :
    c.getNumParts = (parentOf c).getNumParts + 1 := by
  cases c <;> simp_all [parentOf, Name.getNumParts]

theorem not_isPre_parentOf {c : Name} (h : c ≠ .anonymous) : ¬IsPre c (parentOf c) := by
  intro h'; have := h'.depth_le; rw [depth_of_ne h] at this; omega

theorem isPre_iff_of_ne {c n : Name} (h : n ≠ .anonymous) :
    IsPre c n ↔ c = n ∨ IsPre c (parentOf n) := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact .inl rfl
    | succ k => exact .inr ⟨k, rfl⟩
  · rintro (rfl | h')
    · exact isPre_refl _
    · exact h'.trans (isPre_parentOf _)

theorem pre_ne_anonymous {n : Name} {k : Nat} (h : k < n.getNumParts) : pre n k ≠ .anonymous := by
  intro e; have := depth_pre n k; rw [e] at this; simp [Name.getNumParts] at this; omega

/-! ## `prefixesOf` -/

theorem prefixesOf_spec (n : Name) (acc : Array Name) :
    (prefixesOf n acc).size = acc.size + n.getNumParts ∧
      ∀ j, j < n.getNumParts → (prefixesOf n acc)[acc.size + j]! = pre n j := by
  induction n generalizing acc with
  | anonymous => simp [prefixesOf, Name.getNumParts]
  | str p s ih =>
    obtain ⟨ih1, ih2⟩ := ih (acc.push (.str p s))
    simp only [Array.size_push] at ih1 ih2
    refine ⟨by rw [prefixesOf, ih1, Name.getNumParts]; omega, fun j hj => ?_⟩
    rw [prefixesOf]
    cases j with
    | zero =>
      have e := prefixesOf_prefix p (acc.push (.str p s)) acc.size (by simp)
      rw [Nat.add_zero, e]; simp [pre]
    | succ j =>
      have := ih2 j (by simp [Name.getNumParts] at hj; omega)
      rw [show acc.size + (j + 1) = acc.size + 1 + j by omega, this]; rfl
  | num p s ih =>
    obtain ⟨ih1, ih2⟩ := ih (acc.push (.num p s))
    simp only [Array.size_push] at ih1 ih2
    refine ⟨by rw [prefixesOf, ih1, Name.getNumParts]; omega, fun j hj => ?_⟩
    rw [prefixesOf]
    cases j with
    | zero =>
      have e := prefixesOf_prefix p (acc.push (.num p s)) acc.size (by simp)
      rw [Nat.add_zero, e]; simp [pre]
    | succ j =>
      have := ih2 j (by simp [Name.getNumParts] at hj; omega)
      rw [show acc.size + (j + 1) = acc.size + 1 + j by omega, this]; rfl
where
  prefixesOf_prefix (n : Name) (acc : Array Name) (i : Nat) (hi : i < acc.size) :
      (prefixesOf n acc)[i]! = acc[i] := by
    induction n generalizing acc with
    | anonymous => simp [prefixesOf, getElem!_pos acc i hi]
    | str p s ih => rw [prefixesOf, ih _ (by simp; omega)]; simp [Array.getElem_push_lt hi]
    | num p s ih => rw [prefixesOf, ih _ (by simp; omega)]; simp [Array.getElem_push_lt hi]


/-! ## Well-formed tries and lookup -/

/--
A well-formed trie: child keys extend the parent's key by exactly one component, are pairwise
distinct, and are sorted by hash.
-/
inductive WF : ConstTrie α → Prop
  | intro (t : ConstTrie α)
    (ext : ∀ c ∈ t.children, c.key ≠ .anonymous ∧ parentOf c.key = t.key)
    (sorted : ∀ i j (hij : i ≤ j) (hj : j < t.children.size),
      (t.children[i]'(by omega)).key.hash ≤ t.children[j].key.hash)
    (distinct : ∀ i j (hi : i < t.children.size) (hj : j < t.children.size),
      t.children[i].key = t.children[j].key → i = j)
    (sub : ∀ c ∈ t.children, WF c) : WF t

/-- `t` stores the value `v` for the name `n`. -/
inductive HasEntry : ConstTrie α → Name → α → Prop
  | here {t : ConstTrie α} {v : α} : t.val? = some v → HasEntry t t.key v
  | child {t c : ConstTrie α} {n : Name} {v : α} : c ∈ t.children → HasEntry c n v → HasEntry t n v

theorem hasEntry_iff {t : ConstTrie α} {n : Name} {v : α} :
    HasEntry t n v ↔ (t.key = n ∧ t.val? = some v) ∨ ∃ c ∈ t.children, HasEntry c n v := by
  constructor
  · intro h; cases h with
    | here h => exact .inl ⟨rfl, h⟩
    | child hc h => exact .inr ⟨_, hc, h⟩
  · rintro (⟨rfl, h⟩ | ⟨c, hc, h⟩)
    · exact .here h
    · exact .child hc h

theorem WF.isPre_of_hasEntry {t : ConstTrie α} (wf : WF t) (h : HasEntry t n v) :
    IsPre t.key n := by
  induction h with
  | here => exact isPre_refl _
  | child hc _ ih =>
    cases wf with
    | intro _ ext _ _ sub =>
      have := ih (sub _ hc)
      rw [← (ext _ hc).2]
      exact (isPre_parentOf _).trans this

theorem findChildIdx?_empty (keyOf : ConstTrie α → Name) (k : Name) :
    findChildIdx? #[] keyOf k = none := by
  simp [findChildIdx?, findChildIdx?.lowerBound, findChildIdx?.scanRun]

theorem size_mkEmpty8 : (Array.mkEmpty 8 : Array Name).size = 0 := rfl

theorem findAux_eq (t : ConstTrie α) (path : Array Name) (i : Nat) :
    findAux t path i =
      if i = 0 then t.val? else
        match findChildIdx? t.children key path[i - 1]! with
        | some j => findAux t.children[j]! path (i - 1)
        | none   => none := by
  rw [findAux.eq_def]
  cases t <;> by_cases h : i = 0 <;> simp [h, val?, children, findChildIdx?_empty] <;> split <;>
    simp_all

theorem findAux_iff (n : Name) (v : α) : ∀ i (t : ConstTrie α), WF t → i ≤ n.getNumParts →
    t.key = pre n i → (findAux t (prefixesOf n) i = some v ↔ HasEntry t n v) := by
  intro i
  induction i with
  | zero =>
    intro t wf _ hk
    rw [findAux_eq, ite_eq_left rfl, hasEntry_iff]
    simp only [pre] at hk
    refine ⟨fun h => .inl ⟨hk, h⟩, ?_⟩
    rintro (⟨_, h⟩ | ⟨c, hc, h⟩)
    · exact h
    · cases wf with
      | intro _ ext _ _ sub =>
        have h1 := (WF.isPre_of_hasEntry (sub _ hc) h).depth_le
        have h2 := depth_of_ne (ext _ hc).1
        grind
  | succ i ih =>
    intro t wf hi hk
    obtain ⟨-, hp⟩ := prefixesOf_spec n (.mkEmpty 8)
    have hpi := hp i (by omega)
    simp only [size_mkEmpty8, Nat.zero_add] at hpi
    rw [findAux_eq, ite_eq_right (by omega), Nat.add_sub_cancel, hpi]
    have hkne := pre_ne_anonymous (show i < n.getNumParts by omega)
    cases wf with
    | intro _ ext sorted distinct sub =>
    have ext' : ∀ c ∈ t.children, c.key ≠ .anonymous ∧ parentOf c.key = parentOf (pre n i) := by
      intro c hc; exact ⟨(ext c hc).1, by rw [(ext c hc).2, hk, pre_succ]⟩
    -- a child holding `n` must be the one keyed `pre n i`
    have key_of : ∀ c ∈ t.children, HasEntry c n v → c.key = pre n i := by
      intro c hc h
      apply IsPre.eq_of_depth (WF.isPre_of_hasEntry (sub _ hc) h) ⟨i, rfl⟩
      rw [depth_of_ne (ext c hc).1, (ext c hc).2, hk, depth_pre, depth_pre]; omega
    have not_here : ¬(t.key = n ∧ t.val? = some v) := by
      rintro ⟨e, -⟩
      have := depth_pre n (i + 1); rw [← hk, e] at this; omega
    have := findChildIdx?_spec t.children key (pre n i) sorted hkne ext'
    split at this
    · rename_i j heq
      obtain ⟨hj, hjk⟩ := this
      simp only [getElem!_pos t.children j hj]
      rw [ih _ (sub _ (Array.getElem_mem hj)) (by omega) hjk, hasEntry_iff (t := t)]
      refine ⟨fun h => .inr ⟨_, Array.getElem_mem hj, h⟩, ?_⟩
      rintro (h | ⟨c, hc, h⟩)
      · exact absurd h not_here
      · obtain ⟨j', hj', rfl⟩ := Array.getElem_of_mem hc
        obtain rfl := distinct j' j hj' hj ((key_of _ hc h).trans hjk.symm)
        exact h
    · rw [hasEntry_iff]
      grind

/-- Lookup in a well-formed trie rooted at the anonymous name finds exactly its entries. -/
theorem find?_eq_some_iff {t : ConstTrie α} (wf : WF t) (hroot : t.key = .anonymous) (n : Name)
    (v : α) :
    t.find? n = some v ↔ HasEntry t n v := by
  unfold find?
  obtain ⟨hs, -⟩ := prefixesOf_spec n (.mkEmpty 8)
  simp only [size_mkEmpty8, Nat.zero_add] at hs
  simp only [hs]
  apply findAux_iff n v _ t wf (Nat.le_refl _)
  rw [hroot, eq_anonymous_of_depth (n := pre n n.getNumParts) (by rw [depth_pre]; omega)]


/-- The non-anonymous prefixes of `n`. -/
def T (n c : Name) : Prop := c ≠ .anonymous ∧ IsPre c n

/-- The builder's prefix-graph invariant, with `S` the set of recorded prefixes. -/
structure Inv {α : Type} (b : Builder α) (S : Name → Prop) : Prop where
  seen : ∀ c : Name, b.seen.contains c = true ↔ S c
  chOk : ∀ k c : Name, c ∈ b.children[k]?.getD #[] → c ≠ .anonymous ∧ parentOf c = k ∧ S c
  chAll : ∀ c : Name, S c → c ∈ b.children[parentOf c]?.getD #[]
  nodup : ∀ k : Name, (b.children[k]?.getD #[]).toList.Nodup

theorem Inv.congr {b : Builder α} {S S' : Name → Prop} (inv : Inv b S) (h : ∀ c, S c ↔ S' c) :
    Inv b S' := by
  have : S = S' := funext fun c => propext (h c)
  exact this ▸ inv

theorem Inv.empty : Inv ({} : Builder α) (fun _ => False) where
  seen c := by simp
  chOk k c h := by simp at h
  chAll c h := h.elim
  nodup k := by simp

theorem addName_values (b : Builder α) (cur : Name) : (b.addName cur).values = b.values := by
  induction b, cur using Builder.addName.induct with
  | case1 b cur h ih => rw [Builder.addName, dite_eq_left h, ih]
  | case2 b cur h => rw [Builder.addName, dite_eq_right h]

theorem addName_spec (b : Builder α) (cur : Name) (S : Name → Prop) (inv : Inv b S)
    (closed : ∀ c, S c → IsPre c cur → ∀ d, T c d → S d) :
    Inv (b.addName cur) (fun c => S c ∨ T cur c) := by
  induction b, cur using Builder.addName.induct generalizing S with
  | case1 b cur h ih =>
    rw [Builder.addName, dite_eq_left h]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
    obtain ⟨hne, hns⟩ := h
    have hnS : ¬S cur := fun hs => by rw [← inv.seen] at hs; simp_all
    -- the builder after recording `cur`
    have inv' : Inv { b with
        seen := b.seen.insert cur
        children := b.children.alter (parentOf cur) fun cs? => some ((cs?.getD #[]).push cur) }
        (fun c => S c ∨ c = cur) := by
      constructor
      · grind [inv.seen]
      · intro k c hc
        simp only [Std.HashMap.getElem?_alter, beq_iff_eq] at hc
        split at hc
        · rename_i e; subst e
          simp only [Option.getD_some, Array.mem_push] at hc
          rcases hc with hc | rfl
          · have := inv.chOk _ _ hc; exact ⟨this.1, this.2.1, .inl this.2.2⟩
          · exact ⟨hne, rfl, .inr rfl⟩
        · have := inv.chOk _ _ hc; exact ⟨this.1, this.2.1, .inl this.2.2⟩
      · intro c hc
        simp only [Std.HashMap.getElem?_alter, beq_iff_eq]
        split
        · simp only [Option.getD_some, Array.mem_push]
          rcases hc with hc | rfl
          · rename_i e; rw [e]; exact .inl (inv.chAll c hc)
          · exact .inr rfl
        · rcases hc with hc | rfl
          · exact inv.chAll c hc
          · contradiction
      · intro k
        simp only [Std.HashMap.getElem?_alter, beq_iff_eq]
        split
        · simp only [Option.getD_some, Array.toList_push, List.nodup_append, List.nodup_cons,
            List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, List.mem_cons, or_false,
            true_and]
          refine ⟨inv.nodup _, fun a ha e he hae => ?_⟩
          subst he; subst hae
          exact hnS (inv.chOk _ _ (by simpa using ha)).2.2
        · exact inv.nodup k
    refine (ih _ inv' ?_).congr fun c => ?_
    · rintro c (hc | rfl) hpre d hd
      · exact .inl (closed c hc (hpre.trans (isPre_parentOf _)) d hd)
      · exact absurd hpre (not_isPre_parentOf hne)
    · simp only [T, isPre_iff_of_ne hne]
      grind
  | case2 b cur h =>
    rw [Builder.addName, dite_eq_right h]
    refine inv.congr fun c => ⟨.inl, fun h' => h'.elim id fun hT => ?_⟩
    by_cases hc : cur = .anonymous
    · have := hT.2.depth_le
      grind [eq_anonymous_of_depth, Name.getNumParts, T]
    · exact closed cur ((inv.seen cur).1 (by grind)) (isPre_refl _) c hT


/-! ## `toTrie` -/

theorem mk_key (k : Name) (v : Option α) (cs : Array (ConstTrie α)) : (mk k v cs).key = k := by
  unfold mk; split <;> rfl

theorem mk_val? (k : Name) (v : Option α) (cs : Array (ConstTrie α)) : (mk k v cs).val? = v := by
  unfold mk; split <;> rfl

theorem mk_children (k : Name) (v : Option α) (cs : Array (ConstTrie α)) :
    (mk k v cs).children = cs := by
  unfold mk; split
  · rename_i h; simp only [Array.isEmpty_iff] at h; subst h; rfl
  · rfl
  · rfl

theorem toTrie_key (b : Builder α) (key : Name) (fuel : Nat) : (b.toTrie key fuel).key = key := by
  cases fuel <;> simp [Builder.toTrie, mk_key]

/-- The children of a `toTrie` node, before sorting. -/
abbrev childArr (b : Builder α) (key : Name) (fuel : Nat) : Array (ConstTrie α) :=
  (b.children[key]?.getD #[]).map (b.toTrie · fuel)

abbrev hashLt (c₁ c₂ : ConstTrie α) : Bool := decide (c₁.key.hash < c₂.key.hash)

theorem toTrie_succ_children (b : Builder α) (key : Name) (fuel : Nat) :
    (b.toTrie key (fuel + 1)).children = (childArr b key fuel).qsort hashLt := by
  simp [Builder.toTrie, mk_children]

theorem hashLt_asymm (a b : ConstTrie α) : hashLt a b = true → hashLt b a = false := by
  grind

theorem hashLt_trans (a b c : ConstTrie α) :
    hashLt a b = true → hashLt b c = true → hashLt a c = true := by
  grind

theorem qsort_hashLt (xs : Array (ConstTrie α)) :
    (xs.qsort hashLt).Perm xs ∧
      ∀ i j (hij : i ≤ j) (hj : j < (xs.qsort hashLt).size),
        ((xs.qsort hashLt)[i]'(by omega)).key.hash ≤ (xs.qsort hashLt)[j].key.hash := by
  obtain ⟨p, s⟩ := QS.qsort_spec hashLt hashLt_asymm hashLt_trans xs
  refine ⟨p, fun i j hij hj => ?_⟩
  by_cases e : i = j
  · grind
  · have := s i j hj (by omega)
    grind

theorem mem_childArr {b : Builder α} {key : Name} {fuel : Nat} {c : ConstTrie α} :
    c ∈ (childArr b key fuel).qsort hashLt ↔
      ∃ a ∈ b.children[key]?.getD #[], b.toTrie a fuel = c := by
  rw [(qsort_hashLt _).1.mem_iff]; simp

theorem toTrie_wf {S : Name → Prop} {b : Builder α} (inv : Inv b S) :
    ∀ fuel key, WF (b.toTrie key fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro key
    refine .intro _ ?_ ?_ ?_ ?_ <;> simp [Builder.toTrie, mk_children]
  | succ f ih =>
    intro key
    refine .intro _ ?_ ?_ ?_ ?_ <;> simp only [toTrie_succ_children]
    · intro c hc
      obtain ⟨a, ha, rfl⟩ := mem_childArr.1 hc
      have := inv.chOk _ _ ha
      rw [toTrie_key, toTrie_key]
      exact ⟨this.1, this.2.1⟩
    · exact (qsort_hashLt _).2
    · intro i j hi hj e
      have hp :=
        (Array.perm_iff_toList_perm.1 (qsort_hashLt (childArr b key f)).1).map ConstTrie.key
      have hnd : ((childArr b key f).qsort hashLt).toList.map ConstTrie.key |>.Nodup := by
        rw [hp.nodup_iff]
        simpa [childArr, Function.comp_def, toTrie_key] using inv.nodup key
      exact (hnd.getElem_inj (hi := by simpa using hi) (hj := by simpa using hj)).1
        (by simpa using e)
    · intro c hc
      obtain ⟨a, -, rfl⟩ := mem_childArr.1 hc
      exact ih a

theorem toTrie_hasEntry {S : Name → Prop} {b : Builder α} (inv : Inv b S) (D : Nat)
    (hval : ∀ (n : Name) (v : α), b.values[n]? = some v → ∀ c, T n c → S c)
    (hD : ∀ (n : Name) (v : α), b.values[n]? = some v → n.getNumParts ≤ D) :
    ∀ fuel key, D ≤ fuel + key.getNumParts → ∀ n v,
      (HasEntry (b.toTrie key fuel) n v ↔ b.values[n]? = some v ∧ IsPre key n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro key hk n v
    rw [hasEntry_iff]
    simp only [Builder.toTrie, mk_key, mk_val?, mk_children, Array.not_mem_empty, false_and,
      exists_false, or_false]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨h, isPre_refl _⟩
    · rintro ⟨h, hp⟩
      have := hD n v h
      have e := hp.eq_of_depth (isPre_refl n) (by have := hp.depth_le; omega)
      subst e; exact ⟨rfl, h⟩
  | succ f ih =>
    intro key hk n v
    rw [hasEntry_iff, toTrie_succ_children]
    simp only [Builder.toTrie, mk_key, mk_val?]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨c, hc, h⟩)
      · exact ⟨h, isPre_refl _⟩
      · obtain ⟨a, ha, rfl⟩ := mem_childArr.1 hc
        obtain ⟨hne, hpar, -⟩ := inv.chOk _ _ ha
        have hda := depth_of_ne hne
        rw [hpar] at hda
        obtain ⟨h1, h2⟩ := (ih a (by omega) n v).1 h
        exact ⟨h1, hpar ▸ (isPre_parentOf a).trans h2⟩
    · rintro ⟨h, hp⟩
      by_cases e : key = n
      · exact .inl ⟨e, e ▸ h⟩
      · right
        have hlt : key.getNumParts < n.getNumParts := by
          have := hp.depth_le
          refine Nat.lt_of_le_of_ne this fun e' => e (hp.eq_of_depth (isPre_refl n) e')
        let a := pre n (n.getNumParts - key.getNumParts - 1)
        have hane : a ≠ .anonymous := pre_ne_anonymous (by omega)
        have hapre : IsPre a n := ⟨_, rfl⟩
        have hda : a.getNumParts = key.getNumParts + 1 := by simp only [a, depth_pre]; omega
        have hpar : parentOf a = key := by
          apply IsPre.eq_of_depth ((isPre_parentOf a).trans hapre) hp
          rw [depth_parentOf]; omega
        have ha : a ∈ b.children[key]?.getD #[] := hpar ▸ inv.chAll a (hval n v h a ⟨hane, hapre⟩)
        refine ⟨b.toTrie a f, mem_childArr.2 ⟨a, ha, rfl⟩, ?_⟩
        exact (ih a (by omega) n v).2 ⟨h, hapre⟩


/-- The values map after inserting the first `i` pairs: the last occurrence of each name wins. -/
def VR (names : Array Name) (vals : Array α) (i : Nat) (m : Std.HashMap Name α) : Prop :=
  ∀ n v, m[n]? = some v ↔ ∃ j, ∃ h₁ : j < names.size, ∃ h₂ : j < vals.size, j < i ∧
    names[j] = n ∧ vals[j] = v ∧ ∀ j' (h₁' : j' < names.size), j < j' → j' < i → names[j'] ≠ n

/-- The prefixes recorded after inserting the first `i` names. -/
def Ins (names : Array Name) (i : Nat) (c : Name) : Prop :=
  ∃ j, ∃ h : j < names.size, j < i ∧ T names[j] c

theorem VR.step {names : Array Name} {vals : Array α} {i : Nat} {m : Std.HashMap Name α}
    (hv : VR names vals i m) (h₁ : i < names.size) (h₂ : i < vals.size) :
    VR names vals (i + 1) (m.insert names[i] vals[i]) := by
  intro n v
  rw [Std.HashMap.getElem?_insert]
  by_cases e : names[i] = n
  · simp only [e, beq_self_eq_true, ↓reduceIte, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨i, h₁, h₂, by omega, e, rfl, fun j' _ g1 g2 => absurd g2 (by omega)⟩
    · rintro ⟨j, hj1, hj2, g, hn, rfl, hlast⟩
      grind
  · simp only [beq_iff_eq, e, ↓reduceIte, hv n v]
    constructor
    · rintro ⟨j, hj1, hj2, g, hn, hv', hlast⟩
      exact ⟨j, hj1, hj2, by omega, hn, hv', by grind⟩
    · rintro ⟨j, hj1, hj2, g, hn, hv', hlast⟩
      exact ⟨j, hj1, hj2, by grind, hn, hv', by grind⟩

theorem Inv.withValues {b : Builder α} {S : Name → Prop} (inv : Inv b S) (m : Std.HashMap Name α) :
    Inv { b with values := m } S :=
  ⟨inv.seen, inv.chOk, inv.chAll, inv.nodup⟩

theorem go_spec (names : Array Name) (vals : Array α) :
    ∀ i (b : Builder α), i ≤ min names.size vals.size → Inv b (Ins names i) →
      VR names vals i b.values →
      Inv (ofArrays.go names vals i b) (Ins names (min names.size vals.size)) ∧
        VR names vals (min names.size vals.size) (ofArrays.go names vals i b).values := by
  intro i b
  induction i, b using ofArrays.go.induct names vals with
  | case1 i b h b' ih =>
    intro hi inv hv
    rw [ofArrays.go, dite_eq_left h]
    apply ih (by omega)
    · have := addName_spec { b with values := b.values.insert names[i] vals[i] } names[i]
        (Ins names i) (inv.withValues _) (by
          rintro c ⟨j, hj, g, hT⟩ _ d hd
          exact ⟨j, hj, g, hd.1, hd.2.trans hT.2⟩)
      refine this.congr fun c => ?_
      constructor
      · rintro (⟨j, hj, g, hT⟩ | hT)
        · exact ⟨j, hj, by omega, hT⟩
        · exact ⟨i, h.1, by omega, hT⟩
      · rintro ⟨j, hj, g, hT⟩
        by_cases e : j = i
        · subst e; exact .inr hT
        · exact .inl ⟨j, hj, by omega, hT⟩
    · rw [addName_values]
      exact hv.step h.1 h.2
  | case2 i b h =>
    intro hi inv hv
    rw [ofArrays.go, dite_eq_right h]
    have : i = min names.size vals.size := by omega
    subst this
    exact ⟨inv, hv⟩

theorem foldl_depth_bound (l : List Name) (init : Nat) :
    init ≤ l.foldl (fun d n => max d n.getNumParts) init ∧
      ∀ x ∈ l, x.getNumParts ≤ l.foldl (fun d n => max d n.getNumParts) init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h1, h2⟩ := ih (max init a.getNumParts)
    exact ⟨by omega, by omega, h2⟩

theorem go_final (names : Array Name) (vals : Array α) :
    Inv (ofArrays.go names vals 0 {}) (Ins names (min names.size vals.size)) ∧
      VR names vals (min names.size vals.size) (ofArrays.go names vals 0 {}).values := by
  apply go_spec names vals 0 {} (by omega)
  · exact Inv.empty.congr fun c => by simp [Ins]
  · intro n v; simp

theorem ofArrays_wf (names : Array Name) (vals : Array α) : WF (ofArrays names vals) :=
  toTrie_wf (go_final names vals).1 _ _

theorem ofArrays_key (names : Array Name) (vals : Array α) :
    (ofArrays names vals).key = .anonymous :=
  toTrie_key _ _ _

theorem ofArrays_hasEntry (names : Array Name) (vals : Array α) (n : Name) (v : α) :
    HasEntry (ofArrays names vals) n v ↔ ∃ j, ∃ h₁ : j < names.size, ∃ h₂ : j < vals.size,
      names[j] = n ∧ vals[j] = v ∧
      ∀ j' (h₁' : j' < names.size), j < j' → j' < vals.size → names[j'] ≠ n := by
  obtain ⟨inv, hv⟩ := go_final names vals
  have := toTrie_hasEntry inv (depthBound names)
    (fun n v h c hc => by
      obtain ⟨j, h1, h2, g, rfl, -, -⟩ := (hv n v).1 h
      exact ⟨j, h1, g, hc⟩)
    (fun n v h => by
      obtain ⟨j, h1, h2, g, rfl, -, -⟩ := (hv n v).1 h
      rw [depthBound, ← Array.foldl_toList]
      exact (foldl_depth_bound names.toList 0).2 _ (Array.getElem_mem_toList h1))
    (depthBound names) .anonymous (Nat.le_refl _) n v
  unfold ofArrays
  rw [this, hv n v]
  simp only [isPre_anonymous, and_true]
  constructor
  · rintro ⟨j, h1, h2, g, hn, hv', hl⟩
    exact ⟨j, h1, h2, hn, hv', fun j' h1' g1 g2 => hl j' h1' g1 (by omega)⟩
  · rintro ⟨j, h1, h2, hn, hv', hl⟩
    exact ⟨j, h1, h2, by omega, hn, hv', fun j' h1' g1 g2 => hl j' h1' g1 (by omega)⟩

/--
`ofArrays names vals` maps `n` to the value paired with its last occurrence among the first
`min names.size vals.size` names.
-/
theorem find?_ofArrays (names : Array Name) (vals : Array α) (n : Name) (v : α) :
    (ofArrays names vals).find? n = some v ↔ ∃ j, ∃ h₁ : j < names.size, ∃ h₂ : j < vals.size,
      names[j] = n ∧ vals[j] = v ∧
      ∀ j' (h₁' : j' < names.size), j < j' → j' < vals.size → names[j'] ≠ n := by
  rw [find?_eq_some_iff (ofArrays_wf names vals) (ofArrays_key names vals), ofArrays_hasEntry]

theorem find?_ofArrays_of_distinct (names : Array Name) (vals : Array α)
    (hsize : names.size = vals.size)
    (distinct : ∀ i j (hi : i < names.size) (hj : j < names.size), names[i] = names[j] → i = j)
    (n : Name) (v : α) :
    (ofArrays names vals).find? n = some v ↔
      ∃ i, ∃ h : i < names.size, names[i] = n ∧ vals[i]'(hsize ▸ h) = v := by
  rw [find?_ofArrays]
  constructor
  · rintro ⟨j, h1, h2, hn, hv, -⟩; exact ⟨j, h1, hn, hv⟩
  · rintro ⟨j, h1, hn, hv⟩
    exact ⟨j, h1, hsize ▸ h1, hn, hv, by grind⟩

theorem find?_ofArrays_getElem (names : Array Name) (vals : Array α)
    (hsize : names.size = vals.size)
    (distinct : ∀ i j (hi : i < names.size) (hj : j < names.size), names[i] = names[j] → i = j)
    (i : Nat) (h : i < names.size) :
    (ofArrays names vals).find? names[i] = some (vals[i]'(hsize ▸ h)) :=
  (find?_ofArrays_of_distinct names vals hsize distinct _ _).2 ⟨i, h, rfl, rfl⟩

theorem find?_ofArrays_eq_none (names : Array Name) (vals : Array α) (n : Name) (h : n ∉ names) :
    (ofArrays names vals).find? n = none := by
  cases e : (ofArrays names vals).find? n with
  | none => rfl
  | some v =>
    obtain ⟨j, h1, -, hn, -⟩ := (find?_ofArrays names vals n v).1 e
    exact absurd (hn ▸ Array.getElem_mem h1) h


/-- The entries of a trie in `foldlM` order. -/
def entries : ConstTrie α → List (Name × α)
  | .leaf k v => [(k, v)]
  | .inner _ cs => cs.toList.flatMap entries
  | .node k v cs => (k, v) :: cs.toList.flatMap entries
decreasing_by
  all_goals
    rename_i c hc
    have := List.sizeOf_lt_of_mem hc
    cases cs; simp_all; omega

theorem entries_eq (t : ConstTrie α) :
    entries t = (t.val?.map fun v => (t.key, v)).toList ++ t.children.toList.flatMap entries := by
  cases t <;> simp [entries, val?, key, children]


theorem sizeOf_lt_of_mem_children {t c : ConstTrie α} (h : c ∈ t.children) :
    sizeOf c < sizeOf t := by
  have := Array.sizeOf_lt_of_mem h
  cases t <;> simp_all [children] <;> omega

theorem foldlM_eq_entries [Monad m] [LawfulMonad m] (t : ConstTrie α) (f : σ → Name → α → m σ)
    (init : σ) : t.foldlM f init = (entries t).foldlM (fun s p => f s p.1 p.2) init := by
  have key : ∀ (l : List (ConstTrie α)), (∀ c ∈ l, ∀ init, c.foldlM f init =
      (entries c).foldlM (fun s p => f s p.1 p.2) init) → ∀ init,
      l.foldlM (fun s c => c.foldlM f s) init =
        (l.flatMap entries).foldlM (fun s p => f s p.1 p.2) init := by
    intro l ih
    induction l with
    | nil => simp
    | cons c l ihl =>
      intro init
      simp only [List.foldlM_cons, List.flatMap_cons, List.foldlM_append]
      rw [ih c (by simp)]
      congr 1; funext s
      exact ihl (fun c hc => ih c (by simp [hc])) s
  have ih : ∀ c ∈ t.children, ∀ init, c.foldlM f init =
      (entries c).foldlM (fun s p => f s p.1 p.2) init :=
    fun c hc init => foldlM_eq_entries c f init
  cases t with
  | leaf k v => simp [foldlM, entries]
  | inner k cs =>
    rw [foldlM, entries, ← Array.foldlM_toList]
    exact key cs.toList (fun c hc => ih c (by simpa [children] using hc)) init
  | node k v cs =>
    rw [foldlM, entries]
    simp only [List.foldlM_cons]
    congr 1; funext s
    rw [← Array.foldlM_toList]
    exact key cs.toList (fun c hc => ih c (by simpa [children] using hc)) s
termination_by t
decreasing_by exact sizeOf_lt_of_mem_children hc

theorem mem_entries (t : ConstTrie α) (n : Name) (v : α) : (n, v) ∈ entries t ↔ HasEntry t n v := by
  rw [entries_eq, hasEntry_iff]
  have ih : ∀ c ∈ t.children, ((n, v) ∈ entries c ↔ HasEntry c n v) :=
    fun c hc => mem_entries c n v
  simp only [List.mem_append, List.mem_flatMap, Array.mem_toList_iff]
  apply or_congr
  · cases t.val? <;> simp [eq_comm]
  · exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, (ih c hc).1 h⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, (ih c hc).2 h⟩⟩
termination_by t
decreasing_by exact sizeOf_lt_of_mem_children hc

theorem WF.entries_keys_nodup {t : ConstTrie α} (wf : WF t) : ((entries t).map Prod.fst).Nodup := by
  induction wf with
  | intro t ext sorted distinct sub ih =>
  rw [entries_eq, List.map_append, List.map_flatMap, List.nodup_append]
  have keys_ext : ∀ c ∈ t.children, ∀ x ∈ (entries c).map Prod.fst, IsPre c.key x := by
    intro c hc x hx
    obtain ⟨⟨x, v⟩, hm, rfl⟩ := List.mem_map.1 hx
    exact WF.isPre_of_hasEntry (sub c hc) ((mem_entries c x v).1 hm)
  refine ⟨?_, ?_, ?_⟩
  · cases t.val? <;> simp
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
    refine ⟨fun c hc => ih c (by simpa using hc), ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij x hx y hy e
    subst e
    simp only [Array.length_toList] at hi hj
    simp only [Array.getElem_toList] at hx hy
    have h1 := keys_ext _ (Array.getElem_mem hi) x hx
    have h2 := keys_ext _ (Array.getElem_mem hj) x hy
    have := distinct i j hi hj (h1.eq_of_depth h2 (by grind [depth_of_ne]))
    omega
  · intro a ha b hb e
    subst e
    have hak : a = t.key := by cases h : t.val? <;> simp_all
    obtain ⟨c, hc, hb⟩ := List.mem_flatMap.1 hb
    have := (keys_ext c (by simpa using hc) a hb).depth_le
    grind [depth_of_ne]

theorem entries_ofArrays_perm (names : Array Name) (vals : Array α)
    (hsize : names.size = vals.size)
    (distinct : ∀ i j (hi : i < names.size) (hj : j < names.size), names[i] = names[j] → i = j) :
    (entries (ofArrays names vals)).Perm (names.zip vals).toList := by
  have hnd := (ofArrays_wf names vals).entries_keys_nodup
  have hzip : ((names.zip vals).toList.map Prod.fst).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij e
    have := distinct i j
    grind
  have ofm : ∀ {l : List (Name × α)}, (l.map Prod.fst).Nodup → l.Nodup := fun h =>
    List.Pairwise.of_map Prod.fst (fun a b h e => h (congrArg _ e)) h
  rw [List.perm_ext_iff_of_nodup (ofm hnd) (ofm hzip)]
  rintro ⟨n, v⟩
  rw [mem_entries, ofArrays_hasEntry, List.mem_iff_getElem]
  simp only [Array.length_toList, Array.size_zip, Array.getElem_toList, Array.getElem_zip,
    Prod.mk.injEq]
  constructor
  · rintro ⟨j, h1, h2, hn, hv, -⟩
    exact ⟨j, by omega, hn, hv⟩
  · rintro ⟨j, hj, hn, hv⟩
    exact ⟨j, by omega, by omega, hn, hv, by grind⟩

end ConstTrieSpec

/-! ## The lazily merged `ImportedConsts` -/

namespace ConstTrieSpec.Merge
open Lean Lean.ImportedConsts Lean.ImportedTree ConstTrieSpec

variable {α σ : Type} {cands : Array (Nat × ConstTrie α)}

abbrev Elem (cands : Array (Nat × ConstTrie α)) :=
  UInt64 × Nat × {c : ConstTrie α // IsCandChild cands c}

def pr (x : Elem cands) : Nat × ConstTrie α := (x.2.1, x.2.2.1)

/-- The children of the candidates with their module indices, in candidate order. -/
def flatPairs (cands : Array (Nat × ConstTrie α)) : List (Nat × ConstTrie α) :=
  cands.toList.flatMap fun p => p.2.children.toList.map fun c => (p.1, c)

def ltE (a b : Elem cands) : Bool :=
  decide (a.1 < b.1) || a.1 == b.1 && decide (a.2.1 < b.2.1)

theorem ltE_iff {a b : Elem cands} :
    ltE a b = true ↔ a.1.toNat < b.1.toNat ∨ (a.1.toNat = b.1.toNat ∧ a.2.1 < b.2.1) := by
  simp only [ltE, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]

theorem ltE_asymm (a b : Elem cands) (h : ltE a b = true) : ltE b a = false := by
  grind [ltE_iff]

theorem ltE_trans (a b c : Elem cands) (h₁ : ltE a b = true) (h₂ : ltE b c = true) :
    ltE a c = true := by
  rw [ltE_iff] at *; omega

theorem foldl_append_toList (l : List β) (g : β → Array γ) (init : Array γ) :
    (l.foldl (fun b x => b ++ g x) init).toList =
      init.toList ++ l.flatMap (fun x => (g x).toList) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih]

theorem flatMap_attachWith_val (l : List β) (P : β → Prop) (H) (f : β → List γ) :
    (l.attachWith P H).flatMap (fun a => f a.val) = l.flatMap f := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.attachWith_cons, List.flatMap_cons]; rw [ih]

/-- The grouping step of `gather`. -/
def ins (groups : Array (Array (Nat × ConstTrie α))) (x : Nat × ConstTrie α) :
    Array (Array (Nat × ConstTrie α)) :=
  match groups.findIdx? fun g => lastPartEq g[0]!.2.key x.2.key with
  | some gi => groups.modify gi (·.push x)
  | none    => groups.push #[x]

theorem groupsOk_ins {groups : Array (Array (Nat × ConstTrie α))} (h : GroupsOk cands groups)
    (x : Nat × ConstTrie α) (hx : IsCandChild cands x.2) : GroupsOk cands (ins groups x) := by
  unfold ConstTrieSpec.Merge.ins; split
  · exact h.modify _ x hx
  · exact h.push x hx

theorem gather_fst (sorted : Array (Elem cands)) (h₀ : UInt64) (idx : Nat)
    (groups : Array (Array (Nat × ConstTrie α))) (hg : GroupsOk cands groups) :
    (foldChildGroups.gather cands sorted h₀ idx groups hg).1 =
      if h : idx < sorted.size then
        if sorted[idx].1 == h₀ then
          (foldChildGroups.gather cands sorted h₀ (idx + 1) (ins groups (pr sorted[idx]))
            (groupsOk_ins hg _ sorted[idx].2.2.2)).1
        else (groups, idx)
      else (groups, idx) := by
  rw [foldChildGroups.gather.eq_def]
  split
  · rename_i h
    split
    · rename_i hh
      generalize hx : sorted[idx] = x
      obtain ⟨a, i, c⟩ := x
      simp only [pr]
      unfold ConstTrieSpec.Merge.ins
      congr 2
      generalize Array.findIdx? (fun g => lastPartEq g[0]!.snd.key c.val.key) groups = r
      cases r <;> rfl
    · rename_i hh; simp
  · rename_i h; simp


/-- The key of a group, that of its first element. -/
def gk (g : Array (Nat × ConstTrie α)) : Name := g[0]!.2.key

/-- `groups` partitions `R` by key, in order of first occurrence of each key. -/
structure Grp (groups : Array (Array (Nat × ConstTrie α))) (R : List (Nat × ConstTrie α)) :
    Prop where
  eq : ∀ g ∈ groups, 0 < g.size ∧ g.toList = R.filter (·.2.key == gk g)
  nodup : (groups.toList.map gk).Nodup
  cover : ∀ x ∈ R, ∃ g ∈ groups, gk g = x.2.key

theorem gk_mem {g : Array (Nat × ConstTrie α)} {R : List (Nat × ConstTrie α)} (h0 : 0 < g.size)
    (h : g.toList = R.filter (·.2.key == gk g)) : ∃ y ∈ R, y.2.key = gk g := by
  have : g[0] ∈ g.toList := by simp
  rw [h] at this
  simp only [List.mem_filter, beq_iff_eq] at this
  exact ⟨_, this.1, this.2⟩

theorem gk_push {g : Array (Nat × ConstTrie α)} (h : 0 < g.size) (x) : gk (g.push x) = gk g := by
  simp [gk, getElem!_pos, Array.getElem_push, h]

theorem Grp.single (x : Nat × ConstTrie α) : Grp #[#[x]] [x] := by
  constructor
  · intro g hg; simp at hg; subst hg; simp [gk]
  · simp
  · intro y hy; simp at hy; subst hy; simp [gk]

theorem Grp.ins {groups : Array (Array (Nat × ConstTrie α))} {R : List (Nat × ConstTrie α)}
    {x : Nat × ConstTrie α} (hg : Grp groups R)
    (hkeys : ∀ a ∈ R ++ [x], ∀ b ∈ R ++ [x],
      lastPartEq a.2.key b.2.key = true ↔ a.2.key = b.2.key) :
    Grp (ins groups x) (R ++ [x]) := by
  have gkR : ∀ g ∈ groups, ∃ y ∈ R, y.2.key = gk g := fun g hgm =>
    gk_mem (hg.eq g hgm).1 (hg.eq g hgm).2
  have lpe : ∀ g ∈ groups, lastPartEq g[0]!.2.key x.2.key = true ↔ gk g = x.2.key := by
    intro g hgm
    obtain ⟨y, hy, hyk⟩ := gkR g hgm
    have := hkeys y (by simp [hy]) x (by simp)
    rw [hyk] at this; exact this
  unfold ConstTrieSpec.Merge.ins
  split
  · rename_i gi hf
    rw [Array.findIdx?_eq_some_iff_getElem] at hf
    obtain ⟨hgi, hp, -⟩ := hf
    have hkey : gk groups[gi] = x.2.key := (lpe _ (Array.getElem_mem hgi)).1 hp
    have hne : ∀ g ∈ groups, 0 < g.size := fun g hgm => (hg.eq g hgm).1
    have hmod : (groups.modify gi (·.push x)).toList.map gk = groups.toList.map gk := by
      apply List.ext_getElem (by simp)
      intro k h1 h2
      simp only [List.getElem_map, Array.getElem_toList, Array.getElem_modify]
      split
      · subst gi; exact gk_push (hne _ (Array.getElem_mem _)) x
      · rfl
    constructor
    · intro g hgm
      rw [Array.mem_iff_getElem] at hgm
      obtain ⟨k, hk, rfl⟩ := hgm
      simp only [Array.size_modify] at hk
      rw [Array.getElem_modify]
      have hold := hg.eq groups[k] (Array.getElem_mem hk)
      split
      · rename_i e; subst e
        rw [gk_push hold.1]
        refine ⟨by simp, ?_⟩
        rw [Array.toList_push, hold.2, List.filter_append]
        simp [hkey]
      · rename_i e
        refine ⟨hold.1, ?_⟩
        rw [hold.2, List.filter_append]
        have : gk groups[k] ≠ x.2.key := fun e' =>
          e ((hg.nodup.getElem_inj (hi := by simpa using hgi) (hj := by simpa using hk)).1
            (by simpa [hkey] using e'.symm))
        simp [Ne.symm this]
    · rw [hmod]; exact hg.nodup
    · intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · obtain ⟨g, hgm, hgk⟩ := hg.cover y hy
        rw [Array.mem_iff_getElem] at hgm
        obtain ⟨k, hk, rfl⟩ := hgm
        refine ⟨_, Array.getElem_mem (i := k) (by simpa using hk), ?_⟩
        rw [Array.getElem_modify]
        split
        · rename_i e; subst e; rw [gk_push (hg.eq _ (Array.getElem_mem hk)).1]; exact hgk
        · exact hgk
      · refine ⟨_, Array.getElem_mem (i := gi) (by simpa using hgi), ?_⟩
        rw [Array.getElem_modify, ite_eq_left rfl, gk_push (hg.eq _ (Array.getElem_mem hgi)).1]
        exact hkey
  · rename_i hf
    rw [Array.findIdx?_eq_none_iff] at hf
    have hnk : ∀ g ∈ groups, gk g ≠ x.2.key := fun g hgm e =>
      by have := hf g hgm; rw [(lpe g hgm).2 e] at this; contradiction
    have hRx : R.filter (·.2.key == x.2.key) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hy e
      obtain ⟨g, hgm, hgk⟩ := hg.cover y hy
      exact hnk g hgm (hgk.trans (by simpa using e))
    constructor
    · intro g hgm
      rw [Array.mem_push] at hgm
      rcases hgm with hgm | rfl
      · have hold := hg.eq g hgm
        refine ⟨hold.1, ?_⟩
        rw [hold.2, List.filter_append]
        simp [Ne.symm (hnk g hgm)]
      · refine ⟨by simp, ?_⟩
        simp only [List.filter_append, gk]
        simp [hRx]
    · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hg.nodup, by simp, ?_⟩
      intro a ha b hb e
      simp only [List.mem_singleton] at hb
      subst hb e
      obtain ⟨g, hgm, hg'⟩ := List.mem_map.1 ha
      exact hnk g (by simpa using hgm) (by rw [hg']; simp [gk])
    · intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · obtain ⟨g, hgm, hgk⟩ := hg.cover y hy
        exact ⟨g, Array.mem_push.2 (.inl hgm), hgk⟩
      · exact ⟨#[y], Array.mem_push.2 (.inr rfl), by simp [gk]⟩


theorem drop_L (sorted : Array (Elem cands)) (idx : Nat) (h : idx < sorted.size) :
    (sorted.toList.map pr).drop idx = pr sorted[idx] :: (sorted.toList.map pr).drop (idx + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]; simp

theorem forall_mem_append_singleton {R : List β} {x : β} {P : β → Prop} (hR : ∀ y ∈ R, P y)
    (hx : P x) : ∀ y ∈ R ++ [x], P y :=
  List.forall_mem_append.2 ⟨hR, List.forall_mem_singleton.2 hx⟩

theorem gather_spec (sorted : Array (Elem cands)) (h₀ : UInt64)
    (hS1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash)
    (hkeys : ∀ a ∈ sorted.toList.map pr, ∀ b ∈ sorted.toList.map pr,
      lastPartEq a.2.key b.2.key = true ↔ a.2.key = b.2.key)
    (idx : Nat) (groups : Array (Array (Nat × ConstTrie α))) (hg : GroupsOk cands groups)
    (R : List (Nat × ConstTrie α)) (hR : Grp groups R) (hRL : ∀ x ∈ R, x ∈ sorted.toList.map pr)
    (hRh : ∀ x ∈ R, x.2.key.hash = h₀) (hidx : idx ≤ sorted.size) :
    ∃ M, (foldChildGroups.gather cands sorted h₀ idx groups hg).1.2 ≤ sorted.size ∧
      idx ≤ (foldChildGroups.gather cands sorted h₀ idx groups hg).1.2 ∧
      (sorted.toList.map pr).drop idx =
        M ++
          (sorted.toList.map pr).drop (foldChildGroups.gather cands sorted h₀ idx groups hg).1.2 ∧
      Grp (foldChildGroups.gather cands sorted h₀ idx groups hg).1.1 (R ++ M) ∧
      (∀ x ∈ M, x.2.key.hash = h₀) ∧
      ∀ h : (foldChildGroups.gather cands sorted h₀ idx groups hg).1.2 < sorted.size,
        sorted[(foldChildGroups.gather cands sorted h₀ idx groups hg).1.2].1 ≠ h₀ := by
  rw [gather_fst]
  split
  · rename_i h
    split
    · rename_i hh
      have hx : pr sorted[idx] ∈ sorted.toList.map pr :=
        List.mem_map_of_mem (Array.getElem_mem_toList h)
      have hxh : (pr sorted[idx]).2.key.hash = h₀ := by
        simp only [pr]; rw [← hS1 idx h]; simpa using hh
      obtain ⟨M, h1, h2, h3, h4, h5, h6⟩ := gather_spec sorted h₀ hS1 hkeys (idx + 1)
        (ins groups (pr sorted[idx])) (groupsOk_ins hg _ sorted[idx].2.2.2) (R ++ [pr sorted[idx]])
        (hR.ins fun a ha b hb => hkeys a (forall_mem_append_singleton hRL hx a ha)
          b (forall_mem_append_singleton hRL hx b hb))
        (forall_mem_append_singleton hRL hx) (forall_mem_append_singleton hRh hxh) h
      refine ⟨pr sorted[idx] :: M, h1, by omega, ?_, by simpa using h4,
        List.forall_mem_cons.2 ⟨hxh, h5⟩, h6⟩
      rw [drop_L sorted idx h, h3]; rfl
    · rename_i hh
      refine ⟨[], hidx, Nat.le_refl _, by simp, by simpa using hR, by simp, fun h' => ?_⟩
      simpa using hh
  · rename_i h
    refine ⟨[], hidx, Nat.le_refl _, by simp, by simpa using hR, by simp, fun h' => absurd h' h⟩
termination_by sorted.size - idx

def step (single : σ → Nat → ConstTrie α → σ) (m : σ → Array (Nat × ConstTrie α) → σ) (s : σ)
    (g : Array (Nat × ConstTrie α)) : σ :=
  if g.size == 1 then single s g[0]!.1 g[0]!.2 else m s g

theorem flush_eq (single : σ → Nat → ConstTrie α → σ) (m : σ → Array (Nat × ConstTrie α) → σ)
    (groups : Array (Array (Nat × ConstTrie α))) (hg : GroupsOk cands groups) (k : Nat) (s : σ) :
    foldChildGroups.flush cands single (fun s g _ _ => m s g) groups hg k s =
      (groups.toList.drop k).foldl (step single m) s := by
  induction k, s using
      foldChildGroups.flush.induct cands single (fun s g _ _ => m s g) groups hg with
  | case1 k s h g hg' ih =>
    rw [foldChildGroups.flush, dite_eq_left h]
    simp only [g, dite_eq_ite] at ih ⊢
    have e : groups.toList.drop k = groups[k] :: groups.toList.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using h)]; simp
    rw [ih, e]
    simp only [List.foldl_cons, step]
  | case2 k s h =>
    rw [foldChildGroups.flush, dite_eq_right h]
    simp [List.drop_eq_nil_of_le (show groups.toList.length ≤ k by simpa using Nat.le_of_not_lt h)]

/-- `G` partitions `R` by key, with keys sorted by hash. -/
structure GP (G : List (Array (Nat × ConstTrie α))) (R : List (Nat × ConstTrie α)) : Prop where
  eq : ∀ g ∈ G, 0 < g.size ∧ g.toList = R.filter (·.2.key == gk g)
  nodup : (G.map gk).Nodup
  cover : ∀ x ∈ R, ∃ g ∈ G, gk g = x.2.key
  sorted : G.Pairwise fun g g' => (gk g).hash.toNat ≤ (gk g').hash.toNat

theorem GP.nil : GP ([] : List (Array (Nat × ConstTrie α))) [] :=
  ⟨by simp, by simp, by simp, by simp⟩

theorem GP.append {groups : Array (Array (Nat × ConstTrie α))}
    {Rrun Rrest : List (Nat × ConstTrie α)}
    {Grest : List (Array (Nat × ConstTrie α))} {h₀ : UInt64}
    (hrun : Grp groups Rrun) (hh : ∀ x ∈ Rrun, x.2.key.hash = h₀)
    (hrest : GP Grest Rrest) (hlt : ∀ y ∈ Rrest, h₀.toNat < y.2.key.hash.toNat) :
    GP (groups.toList ++ Grest) (Rrun ++ Rrest) := by
  have hrunk : ∀ g ∈ groups, (gk g).hash = h₀ := by
    intro g hg
    obtain ⟨y, hy, hyk⟩ := gk_mem (hrun.eq g hg).1 (hrun.eq g hg).2
    rw [← hyk]; exact hh y hy
  have hrestk : ∀ g ∈ Grest, h₀.toNat < (gk g).hash.toNat := by
    intro g hg
    obtain ⟨y, hy, hyk⟩ := gk_mem (hrest.eq g hg).1 (hrest.eq g hg).2
    rw [← hyk]; exact hlt y hy
  constructor
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · have hg' := Array.mem_toList_iff.1 hg
      refine ⟨(hrun.eq g hg').1, ?_⟩
      rw [List.filter_append, (hrun.eq g hg').2]
      suffices Rrest.filter (·.2.key == gk g) = [] by simp [this]
      rw [List.filter_eq_nil_iff]
      intro y hy e
      have := hlt y hy
      grind
    · refine ⟨(hrest.eq g hg).1, ?_⟩
      rw [List.filter_append, (hrest.eq g hg).2]
      suffices Rrun.filter (·.2.key == gk g) = [] by simp [this]
      rw [List.filter_eq_nil_iff]
      intro y hy e
      have := hrestk g hg
      grind
  · rw [List.map_append, List.nodup_append]
    refine ⟨hrun.nodup, hrest.nodup, ?_⟩
    grind
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨g, hg, e⟩ := hrun.cover x hx
      exact ⟨g, List.mem_append.2 (.inl (Array.mem_toList_iff.2 hg)), e⟩
    · obtain ⟨g, hg, e⟩ := hrest.cover x hx
      exact ⟨g, List.mem_append.2 (.inr hg), e⟩
  · rw [List.pairwise_append]
    refine ⟨?_, hrest.sorted, ?_⟩
    · exact List.pairwise_iff_getElem.2 fun i j hi hj _ => by grind
    · grind

theorem mem_drop_L {sorted : Array (Elem cands)} {p : Nat} {y : Nat × ConstTrie α}
    (h : y ∈ (sorted.toList.map pr).drop p) :
    ∃ q, ∃ hq : q < sorted.size, p ≤ q ∧ y = pr sorted[q] := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_drop, List.length_map, Array.length_toList] at hk
  exact ⟨p + k, by omega, by omega, by simp⟩

theorem go_spec (single : σ → Nat → ConstTrie α → σ) (m : σ → Array (Nat × ConstTrie α) → σ)
    (sorted : Array (Elem cands))
    (hS1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash)
    (hS3 : ∀ p q (hpq : p ≤ q) (hq : q < sorted.size),
      (sorted[p]'(by omega)).1.toNat ≤ sorted[q].1.toNat)
    (hkeys : ∀ a ∈ sorted.toList.map pr, ∀ b ∈ sorted.toList.map pr,
      lastPartEq a.2.key b.2.key = true ↔ a.2.key = b.2.key)
    (idx : Nat) :
    ∃ G, (∀ s, foldChildGroups.go cands single (fun s g _ _ => m s g) sorted idx s =
        G.foldl (step single m) s) ∧ GP G ((sorted.toList.map pr).drop idx) := by
  have hpr : ∀ k (h : k < sorted.size), (pr sorted[k]).2.key.hash = sorted[k].1 :=
    fun k h => (hS1 k h).symm
  by_cases h : idx < sorted.size
  · have hL := drop_L sorted idx h
    -- the remaining elements after a run with hash `sorted[idx].1` ending at `e`
    have hlt : ∀ e, idx < e → (∀ he : e < sorted.size, sorted[e].1 ≠ sorted[idx].1) →
        ∀ y ∈ (sorted.toList.map pr).drop e, sorted[idx].1.toNat < y.2.key.hash.toNat := by
      intro e hie hne y hy
      obtain ⟨q, hq, hqe, rfl⟩ := mem_drop_L hy
      rw [hpr q hq]
      have h1 := hS3 idx e (by omega) (by omega)
      have h2 := hS3 e q hqe hq
      have h3 := hne (by omega)
      have : sorted[e].1.toNat ≠ sorted[idx].1.toNat := fun e' => h3 (UInt64.toNat_inj.1 e')
      omega
    by_cases hA : ∃ h' : idx + 1 < sorted.size, sorted[idx + 1].1 == sorted[idx].1
    · obtain ⟨h', hh⟩ := hA
      have hok : GroupsOk cands #[#[pr sorted[idx]]] :=
        GroupsOk.push (groups := #[]) (by simp [GroupsOk]) _ sorted[idx].2.2.2
      obtain ⟨M, h1, h2, h3, h4, h5, h6⟩ := gather_spec sorted sorted[idx].1 hS1 hkeys (idx + 1)
        #[#[pr sorted[idx]]] hok
        [pr sorted[idx]] (Grp.single _) (by
          intro y hy; simp only [List.mem_singleton] at hy; subst hy
          exact List.mem_map_of_mem (Array.getElem_mem_toList h))
        (by simp [hpr idx h]) (by omega)
      obtain ⟨G, hG1, hG2⟩ := go_spec single m sorted hS1 hS3 hkeys
        (foldChildGroups.gather cands sorted sorted[idx].1 (idx + 1) #[#[pr sorted[idx]]] hok).1.2
      refine ⟨(foldChildGroups.gather cands sorted sorted[idx].1 (idx + 1) #[#[pr sorted[idx]]]
        hok).1.1.toList ++ G, fun s => ?_, ?_⟩
      · rw [foldChildGroups.go.eq_def]
        simp only [h, ↓reduceDIte, h', hh, ↓reduceIte]
        refine (hG1 _).trans ?_
        rw [flush_eq, List.drop_zero, List.foldl_append]
        rfl
      · rw [hL, h3, ← List.cons_append]
        exact GP.append h4 (by simpa [hpr idx h] using h5) hG2 (hlt _ (by omega) h6)
    · obtain ⟨G, hG1, hG2⟩ := go_spec single m sorted hS1 hS3 hkeys (idx + 1)
      refine ⟨#[pr sorted[idx]] :: G, fun s => ?_, ?_⟩
      · rw [foldChildGroups.go.eq_def]
        simp only [h, ↓reduceDIte]
        split
        · rename_i h'
          have hh : ¬(sorted[idx + 1].1 == sorted[idx].1) = true := fun hh => hA ⟨h', hh⟩
          simp only [hh, Bool.false_eq_true, ↓reduceIte]
          rw [hG1]; simp [step, pr]
        · rw [hG1]; simp [step, pr]
      · rw [hL, ← List.singleton_append]
        exact GP.append (groups := #[#[pr sorted[idx]]]) (Grp.single _) (by simp [hpr idx h]) hG2
          (hlt _ (by omega) fun he e => hA ⟨he, by simp [e]⟩)
  · refine ⟨[], fun s => ?_, ?_⟩
    · rw [foldChildGroups.go.eq_def]; simp [h]
    · rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt h)]; exact GP.nil
termination_by sorted.size - idx

theorem foldChildGroups_eq (single : σ → Nat → ConstTrie α → σ)
    (multi : σ → (g : Array (Nat × ConstTrie α)) → 0 < g.size → (∀ x ∈ g, IsCandChild cands x.2) →
      σ) :
    ∃ all : Array (Elem cands),
      (∀ init, foldChildGroups cands init single multi =
        foldChildGroups.go cands single multi (all.qsort ltE) 0 init) ∧
      all.toList.map (fun x => (x.1, pr x)) =
        (flatPairs cands).map (fun z => (z.2.key.hash, z)) := by
  refine ⟨_, fun init => rfl, ?_⟩
  simp
  rw [show cands.size = cands.attach.size by simp, ← Array.foldl_toList]
  change List.map _ (Array.toList (List.foldl _ _ _)) = _
  rw [foldl_append_toList]
  simp [flatPairs, List.map_flatMap, pr]
  exact flatMap_attachWith_val cands.toList _ _
    (fun a => List.map (fun x => (x.key.hash, a.fst, x)) a.snd.children.toList)

theorem sorted_facts (all : Array (Elem cands))
    (hall : all.toList.map (fun x => (x.1, pr x)) =
      (flatPairs cands).map (fun z => (z.2.key.hash, z))) :
    (∀ k (h : k < (all.qsort ltE).size), (all.qsort ltE)[k].1 = (all.qsort ltE)[k].2.2.1.key.hash) ∧
    ((all.qsort ltE).toList.map pr).Perm (flatPairs cands) ∧
    (∀ p q (hpq : p < q) (hq : q < (all.qsort ltE).size),
      ¬ltE (all.qsort ltE)[q] ((all.qsort ltE)[p]'(by omega)) = true) := by
  obtain ⟨hperm, hsorted⟩ := QS.qsort_spec ltE ltE_asymm ltE_trans all
  have h1 : all.toList.map pr = flatPairs cands := by
    have := congrArg (List.map Prod.snd) hall
    simpa [Function.comp_def] using this
  refine ⟨?_, ?_, fun p q hpq hq => hsorted p q hq hpq⟩
  · intro k h
    have hm : (all.qsort ltE)[k] ∈ all := hperm.mem_iff.mp (Array.getElem_mem h)
    have : ((all.qsort ltE)[k].1, pr (all.qsort ltE)[k]) ∈
        (flatPairs cands).map (fun z => (z.2.key.hash, z)) := by
      rw [← hall]; exact List.mem_map_of_mem (Array.mem_toList_iff.mpr hm)
    obtain ⟨z, _, hz⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at hz
    rw [← hz.1, hz.2]; rfl
  · rw [← h1]
    exact (Array.perm_iff_toList_perm.1 hperm).map pr

/-- Strictly increasing module indices. -/
def StrictIdx (cands : Array (Nat × ConstTrie α)) : Prop :=
  cands.toList.Pairwise fun p q => p.1 < q.1

theorem flatPairs_mem {x : Nat × ConstTrie α} (h : x ∈ flatPairs cands) :
    ∃ p ∈ cands, x.1 = p.1 ∧ x.2 ∈ p.2.children := by
  simp only [flatPairs, List.mem_flatMap, List.mem_map, Array.mem_toList_iff] at h
  obtain ⟨p, hp, c, hc, rfl⟩ := h
  exact ⟨p, hp, rfl, hc⟩

theorem StrictIdx.eq {cands : Array (Nat × ConstTrie α)} (h : StrictIdx cands)
    {p q : Nat × ConstTrie α}
    (hp : p ∈ cands) (hq : q ∈ cands) (e : p.1 = q.1) : p = q := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hp
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hq
  rw [StrictIdx, List.pairwise_iff_getElem] at h
  have := h i j
  have := h j i
  grind

/-- Children of a well-formed node with equal keys are equal. -/
theorem _root_.ConstTrieSpec.WF.child_eq {t : ConstTrie α} (wf : WF t) {c c' : ConstTrie α}
    (hc : c ∈ t.children)
    (hc' : c' ∈ t.children) (e : c.key = c'.key) : c = c' := by
  cases wf with
  | intro _ _ _ distinct _ =>
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hc
  obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hc'
  obtain rfl := distinct i j hi hj e
  rfl

theorem flatPairs_eq_of_key {K : Name} (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K)
    (hs : StrictIdx cands)
    {x y : Nat × ConstTrie α} (hx : x ∈ flatPairs cands) (hy : y ∈ flatPairs cands) (e1 : x.1 = y.1)
    (e2 : x.2.key = y.2.key) : x = y := by
  obtain ⟨p, hp, hx1, hx2⟩ := flatPairs_mem hx
  obtain ⟨q, hq, hy1, hy2⟩ := flatPairs_mem hy
  obtain rfl := hs.eq hp hq (by omega)
  have := (hc p hp).1.child_eq hx2 hy2 e2
  exact Prod.ext e1 this

theorem flatPairs_nodup {K : Name} (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K) (hs : StrictIdx cands) :
    (flatPairs cands).Nodup := by
  rw [flatPairs, List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij e
    cases (hc p (by simpa using hp)).1 with
    | intro _ _ _ distinct _ =>
    have := distinct i j (by simpa using hi) (by simpa using hj)
    grind
  · exact hs.imp fun hpq x hx y hy e => by grind

theorem flatPairs_filter_sorted {K : Name} (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K)
    (hs : StrictIdx cands) (k : Name) :
    ((flatPairs cands).filter (·.2.key == k)).Pairwise fun a b => a.1 < b.1 := by
  rw [List.pairwise_filter, flatPairs, List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij e1 e2
    cases (hc p (by simpa using hp)).1 with
    | intro _ _ _ distinct _ =>
    have := distinct i j (by simpa using hi) (by simpa using hj)
    grind
  · exact hs.imp fun hpq x hx y hy _ _ => by grind


theorem flatPairs_key {K : Name} (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K) {x : Nat × ConstTrie α}
    (hx : x ∈ flatPairs cands) : x.2.key ≠ .anonymous ∧ ConstTrie.parentOf x.2.key = K := by
  obtain ⟨p, hp, -, hx2⟩ := flatPairs_mem hx
  have ⟨wf, hk⟩ := hc p hp
  cases wf with
  | intro _ ext _ _ _ => exact ⟨(ext _ hx2).1, (ext _ hx2).2.trans hk⟩

theorem foldChildGroups_spec_aux {K : Name} (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K)
    (hs : StrictIdx cands)
    (single : σ → Nat → ConstTrie α → σ) (m : σ → Array (Nat × ConstTrie α) → σ)
    (sorted : Array (Elem cands))
    (heq : ∀ init, foldChildGroups cands init single (fun s g _ _ => m s g) =
      foldChildGroups.go cands single (fun s g _ _ => m s g) sorted 0 init)
    (S1 : ∀ k (h : k < sorted.size), sorted[k].1 = sorted[k].2.2.1.key.hash)
    (hperm : (sorted.toList.map pr).Perm (flatPairs cands))
    (hinv : ∀ p q (hpq : p < q) (hq : q < sorted.size),
      ¬ltE sorted[q] (sorted[p]'(by omega)) = true) :
    ∃ G : List (Array (Nat × ConstTrie α)),
      (∀ init, foldChildGroups cands init single (fun s g _ _ => m s g) =
        G.foldl (step single m) init) ∧
      (∀ g ∈ G, 0 < g.size ∧ g.toList = (flatPairs cands).filter (·.2.key == gk g)) ∧
      (G.map gk).Nodup ∧
      (∀ x ∈ flatPairs cands, ∃ g ∈ G, gk g = x.2.key) ∧
      G.Pairwise (fun g g' => (gk g).hash.toNat ≤ (gk g').hash.toNat) := by
  have S3 : ∀ p q (hpq : p ≤ q) (hq : q < sorted.size),
      (sorted[p]'(by omega)).1.toNat ≤ sorted[q].1.toNat := by
    intro p q hpq hq
    by_cases e : p = q
    · grind
    · have := hinv p q (by omega) hq
      grind [ltE_iff]
  have hmemL : ∀ x ∈ sorted.toList.map pr, x ∈ flatPairs cands := fun x hx => hperm.mem_iff.1 hx
  have hkeys : ∀ a ∈ sorted.toList.map pr, ∀ b ∈ sorted.toList.map pr,
      lastPartEq a.2.key b.2.key = true ↔ a.2.key = b.2.key := by
    intro a ha b hb
    have h1 := flatPairs_key hc (hmemL a ha)
    have h2 := flatPairs_key hc (hmemL b hb)
    exact lastPartEq_iff h1.1 h2.1 (h1.2.trans h2.2.symm)
  obtain ⟨G, hG1, hG2⟩ := go_spec single m sorted S1 S3 hkeys 0
  simp only [List.drop_zero] at hG2
  have hLnd : (sorted.toList.map pr).Nodup := hperm.nodup_iff.2 (flatPairs_nodup hc hs)
  refine ⟨G, fun init => (heq init).trans (hG1 init), fun g hg => ⟨(hG2.eq g hg).1, ?_⟩,
    hG2.nodup, fun x hx => hG2.cover x (hperm.mem_iff.2 hx), hG2.sorted⟩
  rw [(hG2.eq g hg).2]
  apply List.Perm.eq_of_pairwise (le := fun a b => a.1 < b.1)
  · intro a b _ _ h1 h2; omega
  · rw [List.pairwise_filter, List.pairwise_iff_getElem]
    intro i j hi hj hij e1 e2
    simp only [List.length_map, Array.length_toList] at hi hj
    simp only [List.getElem_map, Array.getElem_toList, beq_iff_eq] at e1 e2 ⊢
    have hh : sorted[i].1 = sorted[j].1 := by
      rw [S1 i hi, S1 j hj]; simp only [pr] at e1 e2; rw [e1, e2]
    have hle := hinv i j hij hj
    rw [ltE_iff, hh] at hle
    have hne : pr sorted[i] ≠ pr sorted[j] := fun e =>
      absurd ((hLnd.getElem_inj (hi := by simpa using hi) (hj := by simpa using hj)).1
        (by simpa using e)) (by omega)
    simp only [pr] at hne ⊢
    refine Nat.lt_of_le_of_ne (by omega) fun e => hne ?_
    exact flatPairs_eq_of_key hc hs (hmemL _ (List.mem_map_of_mem (Array.getElem_mem_toList hi)))
      (hmemL _ (List.mem_map_of_mem (Array.getElem_mem_toList hj))) e (e1.trans e2.symm)
  · exact flatPairs_filter_sorted hc hs _
  · exact hperm.filter _

/--
`foldChildGroups` folds `single`/`multi` over the groups of children with equal keys, each group
listing its children in module order, with the groups sorted by key hash.
-/
theorem foldChildGroups_spec {K : Name} (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K)
    (hs : StrictIdx cands)
    (single : σ → Nat → ConstTrie α → σ) (m : σ → Array (Nat × ConstTrie α) → σ) :
    ∃ G : List (Array (Nat × ConstTrie α)),
      (∀ init, foldChildGroups cands init single (fun s g _ _ => m s g) =
        G.foldl (step single m) init) ∧
      (∀ g ∈ G, 0 < g.size ∧ g.toList = (flatPairs cands).filter (·.2.key == gk g)) ∧
      (G.map gk).Nodup ∧
      (∀ x ∈ flatPairs cands, ∃ g ∈ G, gk g = x.2.key) ∧
      G.Pairwise (fun g g' => (gk g).hash.toNat ≤ (gk g').hash.toNat) := by
  obtain ⟨all, heq, hall⟩ := foldChildGroups_eq (cands := cands) single (fun s g _ _ => m s g)
  obtain ⟨S1, hperm, hinv⟩ := sorted_facts all hall
  exact foldChildGroups_spec_aux hc hs single m _ heq S1 hperm hinv

theorem thunk_get_mk (f : Unit → β) : (Thunk.mk f).get = f () := rfl

theorem mergeLazy_one (resolve : Array (α × Nat) → Option (α × Nat)) (k : Name)
    (g : Array (Nat × ConstTrie α)) (h : g.size = 1) :
    mergeLazy resolve k g = .mod g[0]!.1 g[0]!.2 := by
  rw [mergeLazy]; simp [h]

/-- The entry `mergeLazy` stores for the candidate entries `es`. -/
def res (resolve : Array (α × Nat) → Option (α × Nat)) (es : Array (α × Nat)) : Option (α × Nat) :=
  if es.size < 2 then es[0]? else resolve es

theorem res_empty (resolve : Array (α × Nat) → Option (α × Nat)) : res resolve #[] = none := rfl

theorem res_single (resolve : Array (α × Nat) → Option (α × Nat)) (e : α × Nat) :
    res resolve #[e] = some e := rfl

theorem mergeLazy_ne (resolve : Array (α × Nat) → Option (α × Nat)) (k : Name)
    (g : Array (Nat × ConstTrie α)) (h : g.size ≠ 1) :
    mergeLazy resolve k g = .lazy k
      (res resolve <| g.filterMap fun (i, t) => t.val?.map ((·, i)))
      (Thunk.mk fun _ => mergeLazy.expandLazy resolve g) := by
  rw [mergeLazy]; simp only [h, beq_iff_eq, ↓reduceIte]; rfl

theorem key_mergeLazy (resolve : Array (α × Nat) → Option (α × Nat))
    (g : Array (Nat × ConstTrie α)) :
    (mergeLazy resolve (gk g) g).key = gk g := by
  by_cases h : g.size = 1
  · rw [mergeLazy_one _ _ _ h]; rfl
  · rw [mergeLazy_ne _ _ _ h]; rfl

theorem foldl_step_push (resolve : Array (α × Nat) → Option (α × Nat))
    (G : List (Array (Nat × ConstTrie α))) (acc : Array (ImportedTree α)) :
    G.foldl (step (fun cs i c => cs.push (.mod i c))
        (fun cs g => cs.push (mergeLazy resolve g[0]!.2.key g)))
      acc = acc ++ (G.map fun g => mergeLazy resolve (gk g) g).toArray := by
  induction G generalizing acc with
  | nil => simp
  | cons g G ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    have : step (fun cs i c => cs.push (.mod i c))
        (fun cs g => cs.push (mergeLazy resolve g[0]!.2.key g))
        acc g = acc.push (mergeLazy resolve (gk g) g) := by
      unfold step
      split
      · rename_i h; rw [mergeLazy_one _ _ _ (by simpa using h)]
      · rfl
    rw [this]
    apply Array.ext' ; simp

theorem expandLazy_spec {K : Name} (resolve : Array (α × Nat) → Option (α × Nat))
    (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = K) (hs : StrictIdx cands) :
    ∃ G : List (Array (Nat × ConstTrie α)),
      mergeLazy.expandLazy resolve cands = (G.map fun g => mergeLazy resolve (gk g) g).toArray ∧
      (∀ g ∈ G, 0 < g.size ∧ g.toList = (flatPairs cands).filter (·.2.key == gk g)) ∧
      (G.map gk).Nodup ∧
      (∀ x ∈ flatPairs cands, ∃ g ∈ G, gk g = x.2.key) ∧
      G.Pairwise (fun g g' => (gk g).hash.toNat ≤ (gk g').hash.toNat) := by
  obtain ⟨G, h1, h2⟩ := foldChildGroups_spec hc hs
    (fun (cs : Array (ImportedTree α)) i c => cs.push (.mod i c))
    (fun (cs : Array (ImportedTree α)) g => cs.push (mergeLazy resolve g[0]!.2.key g))
  refine ⟨G, ?_, h2⟩
  rw [mergeLazy.expandLazy, h1, foldl_step_push]
  simp

theorem findEntryAux_mod (j : Nat) (t : ConstTrie α) (path : Array Name) (i : Nat) :
    findEntryAux (.mod j t) path i = (t.findAux path i).map (·, j) := by
  rw [findEntryAux]

theorem findEntryAux_lazy (k : Name) (e : Option (α × Nat))
    (cs : Thunk (Array (ImportedTree α)))
    (path : Array Name) (i : Nat) :
    findEntryAux (.lazy k e cs) path i =
      if i = 0 then e else
        match findChildIdx? cs.get ImportedTree.key path[i - 1]! with
        | some j => findEntryAux cs.get[j]! path (i - 1)
        | none => none := by
  rw [findEntryAux]; by_cases h : i = 0 <;> simp [h]; split <;> simp_all

theorem filter_eq_singleton {l : List β} {p : β → Bool} {c : β} (hnd : l.Nodup) (hc : c ∈ l)
    (hp : p c)
    (huniq : ∀ x ∈ l, ∀ y ∈ l, p x → p y → x = y) : l.filter p = [c] := by
  induction l with
  | nil => simp at hc
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [List.filter_cons_of_pos hp, List.filter_eq_nil_iff.2]
      intro x hx hpx
      exact hnd.1 (huniq x (by simp [hx]) c (by simp) hpx hp ▸ hx)
    · have hpa : p a = false := by
        cases h : p a
        · rfl
        · exact absurd (huniq a (by simp) c (by simp [hc]) h hp ▸ hc) hnd.1
      rw [List.filter_cons_of_neg (by simp [hpa])]
      exact ih hnd.2 hc fun x hx y hy => huniq x (by simp [hx]) y (by simp [hy])

theorem children_nodup {t : ConstTrie α} (wf : WF t) : t.children.toList.Nodup := by
  cases wf with
  | intro _ _ _ distinct _ =>
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij e
  have := distinct i j (by simpa using hi) (by simpa using hj)
  grind

theorem filter_children {t : ConstTrie α} (wf : WF t) {k : Name} (hk : k ≠ .anonymous)
    (hpar : ConstTrie.parentOf k = t.key) :
    t.children.toList.filter (·.key == k) =
      match findChildIdx? t.children ConstTrie.key k with
      | some j => [t.children[j]!]
      | none => [] := by
  have wf' := wf
  cases wf' with
  | intro _ ext sorted distinct _ =>
  have ext' : ∀ c ∈ t.children,
      c.key ≠ .anonymous ∧ ConstTrie.parentOf c.key = ConstTrie.parentOf k :=
    fun c hc => ⟨(ext c hc).1, (ext c hc).2.trans hpar.symm⟩
  have := findChildIdx?_spec t.children ConstTrie.key k sorted hk ext'
  split at this
  · rename_i j heq
    obtain ⟨hj, hjk⟩ := this
    try rw [heq]
    simp only [getElem!_pos t.children j hj]
    apply filter_eq_singleton (children_nodup wf) (by simp) (by simp [hjk])
    intro x hx y hy px py
    exact wf.child_eq (by simpa using hx) (by simpa using hy) (by simp at px py; rw [px, py])
  · rename_i heq
    try rw [heq]
    exact List.filter_eq_nil_iff.2 fun c hc e => this c (by simpa using hc) (by simpa using e)

theorem filterMap_eq_flatMap (f : β → Option γ) (l : List β) :
    l.filterMap f = l.flatMap fun a => (f a).toList := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [h, ih]

theorem flatMap_congr_mem {l : List β} {f g : β → List γ} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- The entries of `n` in the candidate tries, in candidate order, for the subtrees at `path[i]`. -/
def es (path : Array Name) (i : Nat) (cands : Array (Nat × ConstTrie α)) : Array (α × Nat) :=
  cands.filterMap fun p => (p.2.findAux path i).map (·, p.1)

theorem es_step (n : Name) (i : Nat) (hi : i < n.getNumParts)
    (hc : ∀ p ∈ cands, WF p.2 ∧ p.2.key = pre n (i + 1)) (g : Array (Nat × ConstTrie α))
    (hg : g.toList = (flatPairs cands).filter (·.2.key == pre n i)) :
    es (prefixesOf n) (i + 1) cands = es (prefixesOf n) i g := by
  obtain ⟨-, hp⟩ := prefixesOf_spec n (.mkEmpty 8)
  have hpi := hp i hi
  simp only [size_mkEmpty8, Nat.zero_add] at hpi
  apply Array.ext'
  simp only [es, Array.toList_filterMap, hg, flatPairs, List.filter_flatMap, List.filterMap_flatMap]
  rw [filterMap_eq_flatMap]
  apply flatMap_congr_mem
  intro p hpm
  have ⟨wf, hkey⟩ := hc p (by simpa using hpm)
  rw [List.filter_map, List.filterMap_map]
  have hfc := filter_children wf (pre_ne_anonymous hi) (by rw [hkey, pre_succ])
  have : (fun c : ConstTrie α => c.key == pre n i) =
      ((fun x : Nat × ConstTrie α => x.2.key == pre n i) ∘ fun c => (p.1, c)) := rfl
  rw [← this, hfc, findAux_eq, ite_eq_right (by omega), Nat.add_sub_cancel, hpi]
  split <;> rename_i heq <;> simp only [List.filterMap_cons, List.filterMap_nil,
    Function.comp_apply]
  · split <;> simp_all
  · rfl

theorem resolve_es_single {resolve : Array (α × Nat) → Option (α × Nat)} (path : Array Name)
    (i : Nat) (h : cands.size = 1) :
    res resolve (es path i cands) = (cands[0]!.2.findAux path i).map (·, cands[0]!.1) := by
  obtain ⟨c, rfl⟩ := Array.size_eq_one_iff.1 h
  simp only [es]
  simp only [List.filterMap_toArray, List.filterMap_cons, List.filterMap_nil]
  simp only [List.getElem!_toArray, List.getElem!_cons_zero]
  cases c.2.findAux path i <;> simp [res_empty, res_single]

theorem findEntryAux_mergeLazy {resolve : Array (α × Nat) → Option (α × Nat)} (n : Name) :
    ∀ i (cands : Array (Nat × ConstTrie α)), (∀ p ∈ cands, WF p.2 ∧ p.2.key = pre n i) →
      StrictIdx cands → i ≤ n.getNumParts →
      findEntryAux (mergeLazy resolve (pre n i) cands) (prefixesOf n) i =
        res resolve (es (prefixesOf n) i cands) := by
  intro i
  induction i with
  | zero =>
    intro cands hc hs hi
    by_cases h1 : cands.size = 1
    · rw [mergeLazy_one _ _ _ h1, findEntryAux_mod, resolve_es_single _ _ h1]
    · rw [mergeLazy_ne _ _ _ h1, findEntryAux_lazy, ite_eq_left rfl]
      congr 1
      unfold es
      congr 1
      funext p
      obtain ⟨j, t⟩ := p
      show _ = Option.map _ (t.findAux _ 0)
      rw [findAux_eq, ite_eq_left rfl]
  | succ i ih =>
    intro cands hc hs hi
    by_cases h1 : cands.size = 1
    · rw [mergeLazy_one _ _ _ h1, findEntryAux_mod, resolve_es_single _ _ h1]
    obtain ⟨-, hp⟩ := prefixesOf_spec n (.mkEmpty 8)
    have hpi := hp i (by omega)
    simp only [size_mkEmpty8, Nat.zero_add] at hpi
    rw [mergeLazy_ne _ _ _ h1, findEntryAux_lazy, ite_eq_right (by omega), thunk_get_mk,
      Nat.add_sub_cancel, hpi]
    obtain ⟨G, hcs, hGeq, hGnd, hGcov, hGsorted⟩ := expandLazy_spec resolve hc hs
    rw [hcs]
    have hgk : ∀ g ∈ G, ConstTrie.parentOf (gk g) = pre n (i + 1) ∧ gk g ≠ .anonymous := by
      intro g hg
      obtain ⟨y, hy, hyk⟩ := gk_mem (hGeq g hg).1 (hGeq g hg).2
      have := flatPairs_key hc hy
      rw [← hyk]; exact ⟨this.2, this.1⟩
    have hcsk : ∀ (k : Nat) (hk : k < (G.map fun g => mergeLazy resolve (gk g) g).toArray.size),
        (G.map fun g => mergeLazy resolve (gk g) g).toArray[k].key =
          gk (G[k]'(by simpa using hk)) := by
      intro k hk; simp [key_mergeLazy]
    have sorted : ∀ a b (hab : a ≤ b)
        (hb : b < (G.map fun g => mergeLazy resolve (gk g) g).toArray.size),
        ((G.map fun g => mergeLazy resolve (gk g) g).toArray[a]'(by omega)).key.hash ≤
          (G.map fun g => mergeLazy resolve (gk g) g).toArray[b].key.hash := by
      intro a b hab hb
      rw [hcsk, hcsk]
      by_cases e : a = b
      · grind
      · have := List.pairwise_iff_getElem.1 hGsorted a b (by simp at hb; omega) (by simpa using hb)
          (by omega)
        grind
    have ext : ∀ c ∈ (G.map fun g => mergeLazy resolve (gk g) g).toArray,
        c.key ≠ .anonymous ∧ ConstTrie.parentOf c.key = ConstTrie.parentOf (pre n i) := by
      intro c hc'
      simp only [List.mem_toArray, List.mem_map] at hc'
      obtain ⟨g, hg, rfl⟩ := hc'
      rw [key_mergeLazy, ← pre_succ]
      exact ⟨(hgk g hg).2, (hgk g hg).1⟩
    have hspec := findChildIdx?_spec _ ImportedTree.key (pre n i) sorted
      (pre_ne_anonymous (by omega)) ext
    split at hspec
    · rename_i j heq
      obtain ⟨hj, hjk⟩ := hspec
      simp only [getElem!_pos (G.map fun g => mergeLazy resolve (gk g) g).toArray j hj]
      have hj' : j < G.length := by simpa using hj
      rw [hcsk] at hjk
      have hG := hGeq G[j] (List.getElem_mem hj')
      simp only [List.getElem_toArray, List.getElem_map]
      rw [hjk, es_step n i (by omega) hc G[j] (by rw [hG.2, hjk])]
      apply ih G[j]
      · intro p hp
        have hp' : p ∈ G[j].toList := by simpa using hp
        rw [hG.2] at hp'
        simp only [List.mem_filter, beq_iff_eq] at hp'
        obtain ⟨q, hq, -, hpq⟩ := flatPairs_mem hp'.1
        have wfq := (hc q hq).1
        cases wfq with
        | intro _ _ _ _ sub => exact ⟨sub _ hpq, hp'.2.trans hjk⟩
      · unfold StrictIdx; rw [hG.2]; exact flatPairs_filter_sorted hc hs _
      · omega
    · rename_i heq
      try simp only [heq]
      have hnil : (flatPairs cands).filter (·.2.key == pre n i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx e
        obtain ⟨g, hg, hgx⟩ := hGcov x hx
        apply hspec (mergeLazy resolve (gk g) g) (by simp; exact ⟨g, hg, rfl⟩)
        rw [key_mergeLazy, hgx]; simpa using e
      rw [es_step n i (by omega) hc #[] (by simp [hnil])]
      simp [es, res_empty]

/--
Looking up `n` in the lazily merged `ImportedConsts` yields the entries of `n` in the module tries,
in module order: none or the single one if there are fewer than two, and `resolve` applied to them
otherwise.
-/
theorem findEntry?_mergeModuleTreesLazy (trees : Array (Nat × ConstTrie α))
    (resolve : Array (α × Nat) → Option (α × Nat))
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous) (hs : StrictIdx trees) (n : Name) :
    findEntry? (mergeModuleTreesLazy trees resolve) n =
      let es := trees.filterMap fun p => (p.2.find? n).map (·, p.1)
      if es.size < 2 then es[0]? else resolve es := by
  obtain ⟨hsz, -⟩ := prefixesOf_spec n (.mkEmpty 8)
  simp only [size_mkEmpty8, Nat.zero_add] at hsz
  have hroot : pre n n.getNumParts = .anonymous :=
    eq_anonymous_of_depth (by rw [depth_pre]; omega)
  unfold findEntry? mergeModuleTreesLazy
  simp only [hsz]
  rw [← hroot, findEntryAux_mergeLazy n _ trees (by rw [hroot]; exact hwf) hs (Nat.le_refl _)]
  simp only [es, ConstTrie.find?, hsz, res]
  rfl

/--
With the default `resolve`, the merged `ImportedConsts` finds the entry of the first module
declaring `n`.
-/
theorem findEntry?_mergeModuleTreesLazy_default (trees : Array (Nat × ConstTrie α))
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous) (hs : StrictIdx trees) (n : Name) :
    findEntry? (mergeModuleTreesLazy trees) n =
      (trees.filterMap fun p => (p.2.find? n).map (·, p.1))[0]? := by
  rw [findEntry?_mergeModuleTreesLazy trees _ hwf hs n]
  dsimp only; split <;> rfl

/--
The merged `ImportedConsts` finds nothing for a name no module declares, the single entry for a name
one module declares, and the result of `resolve` on the entries in module order for a name several
modules declare.
-/
theorem findEntry?_mergeModuleTreesLazy_cases (trees : Array (Nat × ConstTrie α))
    (resolve : Array (α × Nat) → Option (α × Nat))
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous) (hs : StrictIdx trees) (n : Name) :
    let es := trees.filterMap fun p => (p.2.find? n).map (·, p.1)
    (es = #[] → findEntry? (mergeModuleTreesLazy trees resolve) n = none) ∧
    (∀ e, es = #[e] → findEntry? (mergeModuleTreesLazy trees resolve) n = some e) ∧
    (2 ≤ es.size → findEntry? (mergeModuleTreesLazy trees resolve) n = resolve es) := by
  intro es
  have : findEntry? (mergeModuleTreesLazy trees resolve) n =
      if es.size < 2 then es[0]? else resolve es :=
    findEntry?_mergeModuleTreesLazy trees resolve hwf hs n
  refine ⟨fun h => by rw [this, h]; rfl, fun e h => by rw [this, h]; rfl, fun h => ?_⟩
  rw [this, ite_eq_right (by omega)]

theorem findValAux_eq : ∀ (t : ImportedTree α) (path : Array Name) (i : Nat),
    findValAux t path i = (findEntryAux t path i).map Prod.fst
  | .mod j tr, path, i => by
    rw [findValAux.eq_def, findEntryAux.eq_def]; dsimp only; cases tr.findAux path i <;> rfl
  | .lazy k e cs, path, i => by
    rw [findValAux, findEntryAux]
    by_cases h : i = 0
    · simp [h]
    · simp only [h, dite_false]
      split
      · exact findValAux_eq _ path (i - 1)
      · rfl
  | .merged k e? cs, path, i => by
    rw [findValAux.eq_def, findEntryAux.eq_def]; dsimp only
    by_cases h : i = 0
    · simp only [h, dite_true]
    · simp only [h, dite_false]
      split
      · exact findValAux_eq _ path (i - 1)
      · rfl
termination_by _ _ i => i
decreasing_by all_goals omega

/-- `ImportedConsts.find?` returns the value found by `findEntry?`. -/
theorem find?_eq_findEntry? (t : ImportedConsts α) (n : Name) :
    t.find? n = (t.findEntry? n).map Prod.fst :=
  findValAux_eq t.tree _ _

theorem find?_mergeModuleTreesLazy (trees : Array (Nat × ConstTrie α))
    {resolve : Array (α × Nat) → Option (α × Nat)}
    (hwf : ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous) (hs : StrictIdx trees) (n : Name) :
    (mergeModuleTreesLazy trees resolve).find? n =
      (let es := trees.filterMap fun p => (p.2.find? n).map (·, p.1)
       if es.size < 2 then es[0]? else resolve es).map Prod.fst := by
  rw [find?_eq_findEntry?, findEntry?_mergeModuleTreesLazy trees resolve hwf hs]

/-- Tries built by `ConstTrie.ofArrays` satisfy the assumptions of the `ImportedConsts` theorems. -/
theorem wf_of_ofArrays {trees : Array (Nat × ConstTrie α)}
    (h : ∀ p ∈ trees, ∃ (names : Array Name) (vals : Array α),
      p.2 = ConstTrie.ofArrays names vals) :
    ∀ p ∈ trees, WF p.2 ∧ p.2.key = .anonymous := by
  intro p hp
  obtain ⟨names, vals, e⟩ := h p hp
  rw [e]
  exact ⟨ofArrays_wf names vals, ofArrays_key names vals⟩

end ConstTrieSpec.Merge
