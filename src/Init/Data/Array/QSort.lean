/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Init.Data.Nat.Mod

@[simp] theorem size_ite (P: Prop) [Decidable P] (a b: Array α):
    (if P then a else b).size = (if P then a.size else b.size) := by
  split
  all_goals rfl

@[simp] theorem size_dite (P: Prop) [Decidable P] (a: P → Array α) (b: ¬P → Array α):
    (if h: P then a h else b h).size = (if h: P then (a h).size else (b h).size) := by
  split
  all_goals rfl

namespace Nat
@[simp] theorem left_lt_add_div_two: n < (n + m) / 2 ↔ n + 1 < m := by
  rw [← succ_le,
    Nat.le_div_iff_mul_le Nat.zero_lt_two,
    Nat.mul_two, succ_add, succ_le,
    Nat.add_lt_add_iff_left]

@[simp] theorem left_le_add_div_two: n ≤ (n + m) / 2 ↔ n ≤ m := by
  rw [
    Nat.le_div_iff_mul_le Nat.zero_lt_two,
    Nat.mul_two,
    Nat.add_le_add_iff_left]

@[simp] theorem add_div_two_lt_right: (n + m) / 2 < m ↔ n < m:= by
  rw [
    Nat.div_lt_iff_lt_mul Nat.zero_lt_two,
    Nat.mul_two,
    Nat.add_lt_add_iff_right]

@[simp] theorem add_div_two_le_right: (n + m) / 2 ≤ m ↔ n ≤ m + 1:= by
  rw [← lt_succ,
    Nat.div_lt_iff_lt_mul Nat.zero_lt_two,
    Nat.mul_two, add_succ, lt_succ,
    Nat.add_le_add_iff_right]

theorem lt_of_left_lt_add_div_two (h: n < (n + m) / 2): n < m :=
  lt_of_succ_lt (left_lt_add_div_two.mp h)

theorem add_div_two_le_right_of_le (h: n ≤ m): (n + m) / 2 ≤ m :=
  add_div_two_le_right.mpr (le_add_right_of_le h)
end Nat

namespace Array

@[inline] def qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega) : Array α :=

  let rec @[specialize] sort (as : Array α) (low high : Nat)
      (hlh: low ≤ high) (hhs: low < high → high < as.size): {as': Array α // as'.size = as.size} :=
    let s := as.size
    have hs: as.size = s := rfl
    if hlh': low >= high then
      ⟨as, hs⟩
    else
      have hlh': low < high := Nat.gt_of_not_le hlh'
      have hhs := hhs hlh'

      let s := as.size
      have hs: as.size = s := rfl

      have hls: low < s := Nat.lt_of_le_of_lt hlh hhs

      let mid := (low + high) / 2

      have hmh: mid ≤ high := Nat.add_div_two_le_right_of_le hlh
      have hms: mid < s := Nat.lt_of_le_of_lt hmh hhs

      let as := if lt (as[mid]'(hs ▸ hms)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨mid, hs ▸ hms⟩ else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if lt (as[high]'(hs ▸ hhs)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨high, hs ▸ hhs⟩  else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if lt (as[mid]'(hs ▸ hms)) (as[high]'(hs ▸ hhs)) then as.swap ⟨mid, hs ▸ hms⟩ ⟨high, hs ▸ hhs⟩ else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let pivot := as[high]'(hs ▸ hhs)

      -- invariant: lo ≤ k < i → lt as[i] pivot, i ≤ k < j -> ¬lt as[i] pivot
      let rec @[specialize] loop (as : Array α) (i j : Nat) (hli: low ≤ i) (hij: i ≤ j) (hjh: j ≤ high) (hhs: high < as.size): {as': Array α // as'.size = as.size}:=
        let s := as.size
        have hs: as.size = s := rfl
        have his: i < s := Nat.lt_of_le_of_lt hij (Nat.lt_of_le_of_lt hjh hhs)

        if hjh : j < high then
          have hjs: j < s := Nat.lt_trans hjh hhs

          if lt (as[j]'(hs ▸ hjs)) pivot then
            let as := as.swap ⟨i, hs ▸ his⟩ ⟨j, hs ▸ hjs⟩
            have hs: as.size = s := by simp_all only [as, Array.size_swap]

            have hij: i + 1 ≤ j + 1 := Nat.add_le_add_right hij 1
            have hli: low ≤ i + 1 := Nat.le_add_right_of_le hli

            let ⟨as, hs'⟩ := loop as (i+1) (j+1) hli hij hjh (hs ▸ hhs)
            have hs: as.size = s := by rw [← hs, hs']

            ⟨as, hs⟩
          else
            have hij: i ≤ j + 1 := Nat.le_add_right_of_le hij

            let ⟨as, hs'⟩ := loop as i (j+1) hli hij hjh (hs ▸ hhs)
            have hs: as.size = s := by rw [← hs, hs']

            ⟨as, hs⟩
        else if hih: i >= high then
          -- this can only happen if low == high assuming lt is antisymmetric
          -- that's because i == j == high implies that all k in [low, high) are less than the pivot as[high]
          -- in particular, this means that if mid != high, as[mid] is less than as[high], which is impossible,
          -- because we swap them in that case, so that a[mid] >= a[high]
          -- hence, mid = high, which implies (low + high) / 2 = high, which implies that low = high or
          -- low = high + 1, the latter of which is impossible because low <= high; hence, low == high

          ⟨as, hs⟩
        else
          have hih: i < high := Nat.gt_of_not_le hih

          let as := as.swap ⟨i, hs ▸ his⟩ ⟨high, hs ▸ hhs⟩
          have hs: as.size = s := by simp_all only [as, Array.size_swap]

          let ⟨as, hs'⟩ := sort as low i hli (λ _ ↦ hs ▸ his)
          have hs: as.size = s := by rw [← hs, hs']

          let ⟨as, hs'⟩ := sort as (i+1) high hih (λ _ ↦ hs ▸ hhs)
          have hs: as.size = s := by rw [← hs, hs']

          ⟨as, hs⟩
          termination_by (high - low, 0, high - j)

      have hll: low ≤ low := Nat.le_refl low

      let ⟨as, hs'⟩ := loop as low low hll hll hlh (hs ▸ hhs)
      have hs: as.size = s := by rw [← hs, hs']

      ⟨as, hs⟩
      termination_by (high - low, 1, 0)

  (sort as low high hlh hhs).1

@[simp] theorem size_qsort.sort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega):
    (qsort.sort lt as low high hlh hhs).1.size = as.size := by
  exact (qsort.sort lt as low high hlh hhs).2

@[simp] theorem size_qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega):
    (qsort as lt low high hlh hhs).size = as.size := by
  unfold qsort
  exact (qsort.sort lt as low high hlh hhs).2

inductive IPerm {α} (low high: Nat): Array α → Array α → Prop where
| refl: IPerm low high as as
| swap (as: Array α) (i: Nat) (his: i < as.size) (hli: low ≤ i) (hih: i ≤ high) (j: Nat) (hjs: j < as.size) (hlj: low ≤ j) (hjh: j ≤ high): IPerm low high as (as.swap ⟨i, his⟩ ⟨j, hjs⟩)
| trans {as as' as'': Array α}: IPerm low high as as' → IPerm low high as' as'' → IPerm low high as as''

namespace IPerm
theorem ite (p: Prop) [Decidable p] (low high: Nat) (as0 ast asf: Array α)
    (hpt: IPerm low high as0 ast) (hpf: IPerm low high as0 asf):
    IPerm low high as0 (if p then ast else asf) := by
  split
  case isTrue => exact hpt
  case isFalse => exact hpf

theorem dite (p: Prop) [Decidable p] (low high: Nat) (as0: Array α) (ast: p → Array α) (asf: ¬p → Array α)
    (hpt: (h: p) → IPerm low high as0 (ast h)) (hpf: (h: ¬p) → IPerm low high as0 (asf h)):
    IPerm low high as0 (if h: p then ast h else asf h) := by
  split
  case isTrue h => exact hpt h
  case isFalse h => exact hpf h

theorem trans_swap {as0 as: Array α} (hp: IPerm low high as0 as) (i: Nat) (his: i < as.size) (hli: low ≤ i) (hih: i ≤ high) (j: Nat) (hjs: j < as.size) (hlj: low ≤ j) (hjh: j ≤ high):
  IPerm low high as0 (as.swap ⟨i, his⟩ ⟨j, hjs⟩) := by
  apply IPerm.trans hp
  apply IPerm.swap as i his hli hih j hjs hlj hjh

theorem expand {α} {low high: Nat}
    {low' high': Nat} (hll: low' ≤ low) (hhh: high ≤ high') {as: Array α} {as': Array α}
    (p: IPerm low high as as'): IPerm low' high' as as' := by
  induction p with
  | refl => exact refl
  | trans _ _ ih ih' => exact trans ih ih'
  | swap as i his hli hih j hjs hlj hjh =>
    exact swap as
      i his (Nat.le_trans hll hli) (Nat.le_trans hih hhh)
      j hjs (Nat.le_trans hll hlj) (Nat.le_trans hjh hhh)

theorem size_eq {α} {as: Array α} {as': Array α} {low high: Nat}
  (p: IPerm low high as as' ): as.size = as'.size := by
  induction p with
  | refl => rfl
  | trans _ _ ih ih' => rwa [ih'] at ih
  | swap => simp only [size_swap]

def getElem?_lower {α: Type u} {as: Array α} {as': Array α} {low high: Nat} (hkl: k < low)
  (p: IPerm low high as as'): as[k]? = as'[k]? := by
  induction p with
  | refl => rfl
  | trans _ _ ih ih' => rwa [ih'] at ih
  | swap _ _ _ hli _ _ _ hlj _ =>
    simp [swap_def]
    rw [getElem?_set_ne]
    rw [getElem?_set_ne]
    · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hkl hli))
    · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hkl hlj))

def getElem?_higher {α: Type u} {as: Array α} {as': Array α} {low high: Nat} (hhk: high < k)
  (p: IPerm low high as as'): as[k]? = as'[k]? := by
  induction p with
  | refl => rfl
  | trans _ _ ih ih' => rwa [ih'] at ih
  | swap _ _ _ _ hih _ _ _ hjh =>
    simp [swap_def]
    rw [getElem?_set_ne]
    rw [getElem?_set_ne]
    · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hih hhk)
    · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hjh hhk)
end IPerm

def IForAll (as: Array α) (P: α → Prop) (low high: Nat) :=
  ∀ k, (hks: k < as.size) → low ≤ k → (hkh: k < high) → P (as[k]'hks)

abbrev IForAllSwap (as: Array α) (i j) (his: i < as.size) (hjs: j < as.size) (P: α → Prop) (low high: Nat) :=
  IForAll (as.swap ⟨i, his⟩ ⟨j, hjs⟩) P low high

namespace IForAll
theorem map {P: α → Prop} {Q: α → Prop} (ha: IForAll as P low high) (f: (a: α) → P a → Q a):
  IForAll as Q low high := by
  intro k hks hlk hkh
  specialize ha k hks hlk hkh
  exact f as[k] ha

theorem swap_left {as: Array α} {P: α → Prop} {low: Nat} {i j: Nat}
    (hij: i ≤ j) {hjs: j < as.size} (hjp: P (as[j]'hjs))
    (ha: IForAll as P low i):
    IForAllSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs P low (i + 1) := by
  intro k hks hlk hki1
  rw [size_swap] at hks
  simp only [swap_def]
  by_cases hki: k < i
  · rw [getElem_set_ne]
    rw [getElem_set_ne]
    exact ha k hks hlk hki
    · exact Ne.symm (Nat.ne_of_lt hki)
    · have hkj: k < j := Nat.lt_of_lt_of_le hki hij
      exact Ne.symm (Nat.ne_of_lt hkj)
  · have hki: k = i := Nat.eq_of_lt_succ_of_not_lt hki1 hki
    subst k
    by_cases hij: i = j
    · subst i
      simp only [get_eq_getElem, getElem_set_eq]
      exact hjp
    rw [getElem_set_ne]
    rw [getElem_set_eq]
    simp only [get_eq_getElem]
    exact hjp
    · rfl
    · intro h
      exact hij (Eq.symm h)

theorem swap_right {as: Array α} {P: α → Prop} {i j: Nat} (hij: i ≤ j) (hjs: j < as.size)
    (hb: IForAll as P i j):
    IForAllSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs P (i + 1) (j + 1) := by
  intro k hks hi1x hkj1
  rw [size_swap] at hks
  simp only [swap_def]
  by_cases hkj: k < j
  · rw [getElem_set_ne]
    rw [getElem_set_ne]
    have hik: i ≤ k := Nat.le_of_succ_le hi1x
    exact hb k hks hik hkj
    · exact Nat.ne_of_lt hi1x
    · exact Ne.symm (Nat.ne_of_lt hkj)
  · have hkj: k = j := Nat.eq_of_lt_succ_of_not_lt hkj1 hkj
    subst k
    simp only [get_eq_getElem, getElem_set_eq]
    exact hb i (Nat.lt_trans hi1x hjs) (Nat.le_refl i) hi1x

theorem of_swap {as: Array α} {P: α → Prop} {low high i j: Nat} (hli: low ≤ i) (hij: i ≤ j) (hjh: j < high) {hjs: j < as.size}
    (h: IForAllSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs
      P low high): IForAll as P low high := by
  have his := Nat.lt_of_le_of_lt hij hjs
  intro k hks hlk hkh
  simp [IForAllSwap, IForAll, size_swap, swap_def] at h
  by_cases hki: k = i
  · subst k
    have hlj: low ≤ j := Nat.le_trans hli hij
    specialize h j hjs hlj hjh
    rwa [getElem_set_eq] at h
    · rfl
  by_cases hkj: k = j
  · subst k
    have hih: i < high := Nat.lt_of_le_of_lt hij hjh
    specialize h i his hli hih
    rw [getElem_set_ne] at h
    rwa [getElem_set_eq] at h
    · rfl
    · exact hki
  specialize h k hks hlk hkh
  rw [getElem_set_ne] at h
  rwa [getElem_set_ne] at h
  · exact Ne.symm hki
  · exact Ne.symm hkj

/-- can use IPerm.expand if the sizes don't match --/
theorem transport_in {low high : Nat} {as as' : Array α}
    (hp : IPerm low high as as')
    (h : as.IForAll P low (high + 1)):
    as'.IForAll P low (high + 1) := by
  induction hp with
  | refl => exact h
  | trans _ _ ih ih' => exact ih' (ih h)
  | swap as i his hli hih j hjs hlj hjh  =>
    intro k hks hlk hkh
    simp [swap_def]
    rw [getElem_set]
    rw [getElem_set]
    split
    · exact h i his hli (Nat.lt_add_one_of_le hih)
    · split
      · exact h j hjs hlj (Nat.lt_add_one_of_le hjh)
      · simp [size_swap] at hks
        exact h k hks hlk hkh

/-- can use IPerm.expand if the endpoints don't match --/
theorem transport_lower {low high : Nat} {as as' : Array α}
    (hp : IPerm low high as as')
    (h : as.IForAll P begin low):
    as'.IForAll P begin low := by
induction hp with
| refl => exact h
| trans _ _ ih ih' => exact ih' (ih h)
| swap as i his hli _ j hjs hlj _  =>
  intro k hks hbk hkl
  simp [swap_def]
  rw [getElem_set_ne]
  rw [getElem_set_ne]
  · simp [size_swap] at hks
    exact h k hks hbk hkl
  · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hkl hli))
  · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hkl hlj))

/-- can use IPerm.expand if the endpoints don't match --/
theorem transport_higher {low high : Nat} {as as' : Array α}
    (hp : IPerm low high as as')
    (h : as.IForAll P (high + 1) ends):
    as'.IForAll P (high + 1) ends := by
induction hp with
| refl => exact h
| trans _ _ ih ih' => exact ih' (ih h)
| swap as i his _ hih j hjs _ hjh  =>
  intro k hks hhk hke
  simp [swap_def]
  rw [getElem_set_ne]
  rw [getElem_set_ne]
  · simp [size_swap] at hks
    exact h k hks hhk hke
  · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hih hhk)
  · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hjh hhk)

end IForAll

def IsAsymm {α} (r: α → α → Prop) :=
  {x: α} → {y: α} → r x y → r y x → False

def IsTrans {α} (r: α → α → Prop) :=
  {x: α} → {y: α} → {z: α} → r x y → r y z → r x z

def IOrdered (lt: α → α → Bool) (low: Nat) (high: Nat) (as: Array α) :=
  ∀ i j, (hli: low ≤ i) → (hij: i < j) → (hjh: j ≤ high) → (hjs: j < as.size) →
  lt (as[j]'hjs) (as[i]'(Nat.lt_trans hij hjs)) = false

namespace IOrdered
theorem mkSingle (lt : α → α → Bool) (k: Nat) (as: Array α):
    IOrdered lt k k as := by
  unfold IOrdered
  intro i j hli hij hjl hjs
  exfalso
  have hkk: k < k := Nat.lt_of_le_of_lt hli (Nat.lt_of_lt_of_le hij hjl)
  exact (Nat.ne_of_lt hkk) rfl

theorem restrict {low high: Nat}
    {low' high': Nat} (hll: low ≤ low') (hhh: high' ≤ high) {as: Array α}
    (p: IOrdered lt low high as): IOrdered lt low' high' as := by
  unfold IOrdered
  intro i j hli hij hjl hjs
  exact p i j (Nat.le_trans hll hli) hij (Nat.le_trans hjl hhh) hjs

/-- can use IPerm.expand if the endpoints don't match --/
theorem transport_lower {low high : Nat} {as as' : Array α}
    (hp : IPerm (low + 1) high as as')
    (h : as.IOrdered lt begin low):
    as'.IOrdered lt begin low := by
induction hp with
| refl => exact h
| trans _ _ ih ih' => exact ih' (ih h)
| swap as i his hli _ j hjs hlj _ =>
  intro a b hla hab hbl hbs
  have hal := Nat.lt_of_lt_of_le hab hbl
  simp [swap_def]
  rw [getElem_set_ne]
  rw [getElem_set_ne]
  rw [getElem_set_ne]
  rw [getElem_set_ne]
  · simp [size_swap] at hbs
    exact h a b hla hab hbl hbs
  · exact Ne.symm (Nat.ne_of_lt (Nat.lt_trans hal hli))
  · exact Ne.symm (Nat.ne_of_lt (Nat.lt_trans hal hlj))
  · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_le_of_lt hbl hli))
  · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_le_of_lt hbl hlj))

theorem glue
    {lt : α → α → Bool} {low high : Nat} {pivot : α} {i : Nat} {as : Array α}
    (ha : as.IForAll (fun x => lt pivot x = false) low (i + 1))
    (hb : as.IForAll (fun x => lt x pivot = false) (i + 1) (high + 1))
    (hlttr : IsTrans fun x x_1 => lt x x_1 = false)
    (h1 : IOrdered lt low i as)
    (h2 : IOrdered lt (i + 1) high as):
    IOrdered lt low high as := by
  unfold IOrdered
  intro a b hla hab hbh hbs
  have has := Nat.lt_trans hab hbs

  by_cases hbi: b ≤ i
  · exact h1 a b hla hab hbi hbs

  have hib: i < b := Nat.succ_le_of_lt (Nat.gt_of_not_le hbi)
  by_cases hia: i + 1 ≤ a
  · exact h2 a b hia hab hbh hbs

  have hai: a < i + 1 := by exact Nat.gt_of_not_le hia
  specialize ha a has hla hai
  specialize hb b hbs hib (Nat.lt_add_one_of_le hbh)
  exact hlttr hb ha

end IOrdered

abbrev swap_getElem (as: Array α) (i j k: Nat) (his: i < as.size) (hjs: j < as.size) (hks: k < as.size): α :=
  (as.swap ⟨i, his⟩ ⟨j, hjs⟩)[k]'(
      le_of_le_of_eq hks (Eq.symm (size_swap as ⟨i, his⟩ ⟨j, hjs⟩))
    )

theorem getElem_after_swap {as: Array α} {i j high: Nat} (hij: i ≤ j) (hjh: j < high) (hhs: high < as.size):
    as.swap_getElem i j high (Nat.lt_of_le_of_lt hij (Nat.lt_trans hjh hhs)) (Nat.lt_trans hjh hhs) hhs
    = (as[high]'hhs) := by
  simp [swap_getElem, swap_def]
  rw [getElem_set_ne]
  rw [getElem_set_ne]
  · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hij hjh)
  · exact Nat.ne_of_lt (hjh)

structure ISortOf (lt: α → α → Bool) (low high: Nat) (orig: Array α) (sorted: Array α): Prop where
  perm: IPerm low high orig sorted
  ord: IOrdered lt low high sorted

namespace ISortOf
theorem mkSingle (lt : α → α → Bool) (k: Nat) (as0: Array α) (as: Array α) (hp: IPerm k k as0 as):
    ISortOf lt k k as0 as := ⟨hp, IOrdered.mkSingle lt k as⟩

theorem trans {lt: α → α → Bool} {low high: Nat} {as as' as'': Array α}
    (hp: IPerm low high as as') (hs: ISortOf lt low high as' as''):
    (ISortOf lt low high as as'') := by
    constructor
    case ord =>
      exact hs.ord
    case perm =>
      apply IPerm.trans hp hs.perm
end ISortOf

mutual
  theorem qsort.sort_sort_sorts (lt : α → α → Bool) (low high : Nat) (pivot : α) (i : Nat) (as0: Array α) (as: Array α) (hp: IPerm low high as0 as)
      (hli : low ≤ i) (hih : i < high) (hhs : high < as.size)
      (ha: IForAll as (lt pivot · = false) low (i + 1))
      (hb: IForAll as (lt · pivot = false) (i + 1) (high + 1))
      (hltas: IsAsymm (lt · ·)) (hlttr: IsTrans (lt · · = false)):
      have ⟨as', hs'⟩ := qsort.sort lt as low i hli (λ _ ↦ Nat.lt_trans hih hhs)
      ISortOf lt low high as0 (qsort.sort lt as' (i + 1) high hih (λ _ ↦ hs' ▸ hhs)) := by

    have h1 := qsort.sort_sorts as lt low i hli (λ _ ↦ Nat.lt_trans hih hhs) hltas hlttr
    let ahs' := qsort.sort lt as low i hli (λ _ ↦ Nat.lt_trans hih hhs)
    let as' := ahs'.1
    let hs' := ahs'.2
    have h2 := qsort.sort_sorts as' lt (i + 1) high hih (λ _ ↦ hs' ▸ hhs) hltas hlttr
    constructor
    case perm =>
      apply IPerm.trans hp
      apply IPerm.trans
      · apply IPerm.expand (Nat.le_refl _) (Nat.le_of_lt hih) h1.perm
      · apply IPerm.expand (Nat.le_add_right_of_le hli) (Nat.le_refl _) h2.perm

    case ord =>
      apply IOrdered.glue
      case hlttr => exact hlttr
      case pivot => exact pivot
      case i => exact i
      case ha => exact (ha.transport_in h1.perm).transport_lower h2.perm
      case hb => exact (hb.transport_higher h1.perm).transport_in h2.perm
      case h1 =>
        apply IOrdered.transport_lower
        case hp => exact h2.perm
        case h => exact h1.ord
      case h2 => exact h2.ord
      termination_by (high - low, 0, 0)

  theorem qsort.sort_loop_sorts (lt : α → α → Bool) (low high : Nat) (as0: Array α) (as: Array α) (hp: IPerm low high as0 as)
      {pivot : α} (i j : Nat)
      (hli : low ≤ i) (hij : i ≤ j) (hjh : j ≤ high) (hhs : high < as.size) (hph: as[high]'hhs = pivot)
      (ha: IForAll as (lt · pivot) low i)
      (hb: IForAll as (lt · pivot = false) i j)
      (hc: IForAll as (lt · pivot) low high → low = high)
      (hltas: IsAsymm (lt · ·)) (hlttr: IsTrans (lt · · = false)):
      ISortOf lt low high as0 (qsort.sort.loop lt low high pivot as i j hli hij hjh hhs) := by
    unfold qsort.sort.loop

    have hjs: j < as.size := Nat.lt_of_le_of_lt hjh hhs
    have his: i < as.size := Nat.lt_of_le_of_lt hij hjs
    have hih: i ≤ high := Nat.le_trans hij hjh
    have hlj: low ≤ j := Nat.le_trans hli hij
    have hlh: low ≤ high := Nat.le_trans hli hih

    by_cases hjh': j < high
    all_goals simp only [hjh', ↓reduceDIte]

    case pos =>
      have hjs: j < as.size := Nat.lt_trans hjh' hhs
      by_cases hjp: lt (as[j]'hjs) pivot = true
      all_goals simp only [hjp, Bool.false_eq_true, ↓reduceIte]

      case pos =>
        apply qsort.sort_loop_sorts
        case hph => simpa only [getElem_after_swap hij hjh' hhs]
        case ha => exact ha.swap_left hij hjp
        case hb => exact hb.swap_right hij hjs
        case hc => intro h; apply hc; exact h.of_swap hli hij hjh'
        case hltas => exact hltas
        case hlttr => exact hlttr
        case hp => exact .trans hp (.swap as i his hli hih j hjs hlj hjh)

      case neg =>
        apply qsort.sort_loop_sorts
        case hph => exact hph
        case ha =>
          exact ha

        case hb =>
          intro k hks hik hkj1
          by_cases hkj: k < j
          · specialize hb k hks hik hkj
            exact hb
          · have hkj: k = j := Nat.eq_of_lt_succ_of_not_lt hkj1 hkj
            subst k
            exact eq_false_of_ne_true hjp

        case hc =>
          exact hc

        case hltas => exact hltas
        case hlttr => exact hlttr
        case hp => exact hp

    case neg =>
      have hjh: j = high := Nat.le_antisymm hjh (Nat.le_of_not_lt hjh')
      subst j
      by_cases hhi: i ≥ high
      all_goals simp only [hhi, ↓reduceDIte]

      case pos =>
        have hih: i ≤ high := Nat.le_trans hij hjh
        have hi: i = high := Nat.le_antisymm hih hhi
        subst i
        suffices h: low = high by
          subst high
          apply ISortOf.mkSingle
          exact hp

        apply hc
        exact ha

      case neg =>
        apply qsort.sort_sort_sorts
        case hhs => simpa [size_swap]
        case hp =>
          exact IPerm.trans_swap hp i his hli hih high hhs hlh (Nat.le_refl _)
        case ha =>
          let ha := ha.map (λ x a ↦ eq_false_of_ne_true (hltas a))

          have hhh: lt as[high] as[high] = false := by
            exact eq_false_of_ne_true fun a => hltas a a

          exact (hph ▸ ha).swap_left hij hhh
        case hb => exact (hph ▸ hb).swap_right hij hhs
        case hltas => exact hltas
        case hlttr => exact hlttr
        termination_by (high - low, 1, high - j)

  theorem qsort.sort_loop_pivot_swap_sorts (lt : α → α → Bool) (low high : Nat) (as0: Array α) (as: Array α) (hp: IPerm low high as0 as)
      (mid: Nat) (hlm: low ≤ mid) (hmh: mid < high) (hhs : high < as.size)
      --(hltas: lt as[mid] as[high] = true → lt as[high] as[mid] = true → False)
      (hltas: IsAsymm (lt · ·)) (hlttr: IsTrans (lt · · = false)):

      let as' := if lt (as[mid]'(Nat.lt_trans hmh hhs)) (as[high]'hhs) then as.swap ⟨mid, Nat.lt_trans hmh hhs⟩ ⟨high, hhs⟩ else as
      have hs': as'.size = as.size := by dsimp only [as']; split; all_goals simp_all only [Array.size_swap]

      ISortOf lt low high as0 (qsort.sort.loop lt low high (as'[high]'(hs' ▸ hhs)) as' low low
        (Nat.le_refl low) (Nat.le_refl low) (Nat.le_trans hlm (Nat.le_of_lt hmh)) (hs' ▸ hhs)).1 := by
    have hms := Nat.lt_trans hmh hhs
    have hlh := Nat.le_trans hlm (Nat.le_of_lt hmh)

    have hmh': mid ≠ high := Nat.ne_of_lt hmh
    apply qsort.sort_loop_sorts
    case hc =>
      intro h
      simp only [IForAll, size_ite, size_swap, ite_self] at h
      specialize h mid hms hlm hmh
      simp [swap_def] at h
      split at h
      case isTrue h' =>
        rw [getElem_set_ne] at h
        rw [getElem_set_eq] at h
        rw [getElem_set_eq] at h
        exfalso
        exact hltas h' h
        · rfl
        · rfl
        · exact Ne.symm hmh'
      case isFalse h' =>
        exfalso
        exact h' h
    case hph => rfl
    case hltas => exact hltas
    case hlttr => exact hlttr
    case hp =>
      split
      case isTrue h =>
        exact .trans hp <| .swap as mid hms hlm (Nat.le_of_lt hmh) high hhs hlh (Nat.le_refl _)
      case isFalse h =>
        exact hp
    all_goals
      intro k hks hlk hkl
      have hll: low < low := Nat.lt_of_le_of_lt hlk hkl
      exfalso
      exact (Nat.ne_of_lt hll) rfl
      termination_by (high - low, 2, 0)

  theorem qsort.sort_sorts (as: Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
      (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega)
      -- TODO: to use this less constrained version, we need proofs that as'es are a permutation of eac hother
      --(hltas: {i: Nat} → (hli: low ≤ i) → (hih: i ≤ high) → {j: Nat} → (hlj: low ≤ j) → (hjh: j ≤ high) → lt as[i] as[j] = true → lt as[j] as[i] = true → False):
      (hltas: IsAsymm (lt · ·)) (hlttr: IsTrans (lt · · = false)):
      ISortOf lt low high as (qsort.sort lt as low high hlh hhs) := by
      unfold qsort.sort
      by_cases hlh': low ≥ high
      case pos =>
        simp [hlh']
        constructor
        case ord =>
          intro i j hli hij hjh hjs
          have hlh := Nat.lt_of_le_of_lt hli (Nat.lt_of_lt_of_le hij hjh)
          exfalso
          have hlh'': ¬(low ≥ high) := by
            exact Nat.not_le_of_lt hlh
          exact hlh'' hlh'
        case perm =>
          exact IPerm.refl
      case neg =>
        simp only [hlh']
        have hlh': low < high := Nat.gt_of_not_le hlh'

        apply qsort.sort_loop_pivot_swap_sorts

        case hlm => exact Nat.left_le_add_div_two.mpr hlh
        case hmh => exact Nat.add_div_two_lt_right.mpr hlh'

        case hltas => exact hltas
        case hlttr => exact hlttr

        case hp =>
          repeat any_goals
            first
            | apply Nat.le_refl
            | apply Nat.add_div_two_le_right_of_le
            | apply Nat.left_le_add_div_two.mpr
            | apply IPerm.refl
            | apply IPerm.ite
            | apply IPerm.trans_swap
            | assumption
    termination_by ((sizeOf high) - (sizeOf low), 3, 0)
end

theorem qsort_sorts (as: Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega)
    (hltas: IsAsymm (lt · ·)) (hlttr: IsTrans (lt · · = false)):
    ISortOf lt low high as (qsort as lt low high hlh hhs)  := by
    unfold qsort
    apply qsort.sort_sorts
    · exact hltas
    · exact hlttr

end Array
