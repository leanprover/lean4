/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Init.Data.Nat.Mod

namespace Array
@[simp] theorem size_ite (P: Prop) [Decidable P] (a b: Array α):
    (if P then a else b).size = (if P then a.size else b.size) := by
  split
  all_goals rfl

@[simp] theorem size_dite (P: Prop) [Decidable P] (a: P → Array α) (b: ¬P → Array α):
    (if h: P then a h else b h).size = (if h: P then (a h).size else (b h).size) := by
  split
  all_goals rfl

@[simp] theorem set_getElem_eq (as: Array α) (his: i < as.size) (his': i < as.size): as.set ⟨i, his⟩ (as[i]'his') = as := by
  apply Array.ext
  · simp only [size_set]
  · intro k _ _
    rw [getElem_set]
    split
    all_goals
      try subst k
      simp only
end Array

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

@[inline] def qsort (as : Array α) (r: α → α → Bool) (low := 0) (high := as.size - 1) : Array α :=
  let rec @[specialize] sort (as : Array α) (low high : Nat)
      (hhs: low < high → high < as.size): {as': Array α // as'.size = as.size} :=
    let s := as.size
    have hs: as.size = s := rfl
    if hlh': low >= high then
      ⟨as, hs⟩
    else
      have hlh: low < high := Nat.gt_of_not_le hlh'
      have hhs := hhs hlh

      let s := as.size
      have hs: as.size = s := rfl

      have hls: low < s := Nat.lt_trans hlh hhs

      let mid := (low + high) / 2

      have hmh: mid ≤ high := Nat.add_div_two_le_right_of_le (Nat.le_of_lt hlh)
      have hms: mid < s := Nat.lt_of_le_of_lt hmh hhs

      let as := if r (as[mid]'(hs ▸ hms)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨mid, hs ▸ hms⟩ else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if r (as[high]'(hs ▸ hhs)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨high, hs ▸ hhs⟩  else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if r (as[mid]'(hs ▸ hms)) (as[high]'(hs ▸ hhs)) then as.swap ⟨mid, hs ▸ hms⟩ ⟨high, hs ▸ hhs⟩ else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let pivot := as[high]'(hs ▸ hhs)

      -- invariant: lo ≤ k < i → r as[i] pivot, i ≤ k < j -> ¬lt as[i] pivot
      let rec @[specialize] loop (as : Array α) (i j : Nat) (hli: low ≤ i) (hij: i ≤ j) (hjh: j ≤ high) (hhs: high < as.size): {as': Array α // as'.size = as.size}:=
        have _hlh := hlh
        let s := as.size
        have hs: as.size = s := rfl
        have his: i < s := Nat.lt_of_le_of_lt hij (Nat.lt_of_le_of_lt hjh hhs)

        if hjh' : j < high then
          have hjs: j < s := Nat.lt_trans hjh' hhs

          if r (as[j]'(hs ▸ hjs)) pivot then
            let as := as.swap ⟨i, hs ▸ his⟩ ⟨j, hs ▸ hjs⟩
            have hs: as.size = s := by simp_all only [as, Array.size_swap]

            have hij: i + 1 ≤ j + 1 := Nat.add_le_add_right hij 1
            have hli: low ≤ i + 1 := Nat.le_add_right_of_le hli

            let ⟨as, hs'⟩ := loop as (i+1) (j+1) hli hij hjh' (hs ▸ hhs)
            have hs: as.size = s := by rw [← hs, hs']

            ⟨as, hs⟩
          else
            have hij: i ≤ j + 1 := Nat.le_add_right_of_le hij

            let ⟨as, hs'⟩ := loop as i (j+1) hli hij hjh' (hs ▸ hhs)
            have hs: as.size = s := by rw [← hs, hs']

            ⟨as, hs⟩
        else
          let as := as.swap ⟨i, hs ▸ his⟩ ⟨high, hs ▸ hhs⟩
          have hs: as.size = s := by simp_all only [as, Array.size_swap]

          have hi1s: i - 1 < s := Nat.lt_of_le_of_lt (Nat.sub_le i 1) his
          let ⟨as, hs'⟩ := sort as low (i - 1) (λ _ ↦ hs ▸ hi1s)
          have hs: as.size = s := by rw [← hs, hs']

          let ⟨as, hs'⟩ := sort as (i+1) high (λ _ ↦ hs ▸ hhs)
          have hs: as.size = s := by rw [← hs, hs']

          ⟨as, hs⟩
          termination_by (high - low, 0, high - j)

      have hll: low ≤ low := Nat.le_refl low

      let ⟨as, hs'⟩ := loop as low low hll hll (Nat.le_of_lt hlh) (hs ▸ hhs)
      have hs: as.size = s := by rw [← hs, hs']

      ⟨as, hs⟩
      termination_by (high - low, 1, 0)

  have hhs := by
    intro hlh
    split
    · assumption
    · apply Nat.sub_one_lt
      intro h0
      simp [h0] at hlh

  (sort as low (if high < as.size then high else as.size - 1) hhs).1

@[simp] theorem qsort.size_sort (as : Array α) (r: α → α → Bool) (low := 0) (high := as.size - 1)
    (hhs: low < high → high < as.size):
    (qsort.sort r as low high hhs).1.size = as.size := by
  exact (qsort.sort r as low high hhs).2

@[simp] theorem size_qsort (as : Array α) (r: α → α → Bool) (low := 0) (high := as.size - 1):
    (qsort as r low high).size = as.size := by
  unfold qsort
  split
  all_goals exact (qsort.sort _ _ _ _ _).2

inductive IPerm (low high: Nat): Array α → Array α → Prop where
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

theorem trans_swap (hp: IPerm low high as0 as) (i: Nat) (his: i < as.size) (hli: low ≤ i) (hih: i ≤ high) (j: Nat) (hjs: j < as.size) (hlj: low ≤ j) (hjh: j ≤ high):
  IPerm low high as0 (as.swap ⟨i, his⟩ ⟨j, hjs⟩) := by
  apply IPerm.trans hp
  exact IPerm.swap as i his hli hih j hjs hlj hjh

theorem expand
    {low' high': Nat} (hll: low' ≤ low) (hhh: high ≤ high') {as: Array α} {as': Array α}
    (hp: IPerm low high as as'): IPerm low' high' as as' := by
  induction hp with
  | refl => exact refl
  | trans _ _ ih ih' => exact trans ih ih'
  | swap as i his hli hih j hjs hlj hjh =>
    exact swap as
      i his (Nat.le_trans hll hli) (Nat.le_trans hih hhh)
      j hjs (Nat.le_trans hll hlj) (Nat.le_trans hjh hhh)

theorem expand_up (hhh: high ≤ high')
    (hp: IPerm low high as as'): IPerm low high' as as' :=
  hp.expand (Nat.le_refl _) hhh

theorem expand_down (hll: low' ≤ low)
    (hp: IPerm low high as as'): IPerm low' high as as' :=
  hp.expand hll (Nat.le_refl _)

theorem size_eq
  (hp: IPerm low high as as' ): as.size = as'.size := by
  induction hp with
  | refl => rfl
  | trans _ _ ih ih' => rwa [ih'] at ih
  | swap => simp only [size_swap]

theorem eq_of_singleton (hp: IPerm k k as as' ): as = as' := by
  induction hp with
  | refl => rfl
  | trans _ _ ih ih' => rw [ih, ih']
  | swap as i his hli hih j hjs hlj hjh =>
    have hik: i = k := Nat.le_antisymm hih hli
    have hjk: j = k := Nat.le_antisymm hjh hlj
    subst i j
    rw [swap_def]
    apply Array.ext
    · simp only [size_set]
    · intro k _ _
      repeat rw [getElem_set]
      split
      all_goals
        try subst k
        simp only [get_eq_getElem]

theorem eq_of_trivial (hp: IPerm low high as as' ) (h: high ≤ low): as = as' := by
  by_cases h': high = low
  · subst high
    apply eq_of_singleton hp
  · induction hp with
    | refl => rfl
    | trans _ _ ih ih' => rw [ih, ih']
    | swap as i his hli hih j hjs _ _ =>
      exfalso
      have h: high < low := Nat.lt_of_le_of_ne h h'
      exact Nat.not_lt.mpr (Nat.le_trans hli hih) h

theorem resize_out_of_bounds (hp: IPerm low high as0 as) (hsh': (as0.size - 1) ≤ high'):
  IPerm low high' as0 as := by
  induction hp with
  | refl => exact refl
  | trans p' _ ih ih' => exact trans (ih hsh') (ih' (p'.size_eq ▸ hsh'))
  | swap as i his hli _ j hjs hlj _ =>
    have hih': i ≤ high' := Nat.le_trans (Nat.le_sub_one_of_lt his) hsh'
    have hjh': j ≤ high' := Nat.le_trans (Nat.le_sub_one_of_lt hjs) hsh'
    exact swap as
      i his hli hih'
      j hjs hlj hjh'

def getElem?_lower (hp: IPerm low high as as') (hkl: k < low): as[k]? = as'[k]? := by
  induction hp with
  | refl => rfl
  | trans _ _ ih ih' => rwa [ih'] at ih
  | swap _ _ _ hli _ _ _ hlj _ =>
    simp [swap_def]
    rw [getElem?_set_ne]
    rw [getElem?_set_ne]
    · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hkl hli))
    · exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hkl hlj))

def getElem?_higher (hp: IPerm low high as as') (hhk: high < k): as[k]? = as'[k]? := by
  induction hp with
  | refl => rfl
  | trans _ _ ih ih' => rwa [ih'] at ih
  | swap _ _ _ _ hih _ _ _ hjh =>
    simp [swap_def]
    rw [getElem?_set_ne]
    rw [getElem?_set_ne]
    · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hih hhk)
    · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hjh hhk)

def getElem_lower (hp: IPerm low high as as') (hkl: k < low)
  {hks: k < as.size} {hks': k < as'.size}: as[k]'hks = as'[k]'hks' := by
  apply Option.some_inj.mp
  simp only [← getElem?_lt]
  apply hp.getElem?_lower hkl

def getElem_higher (hp: IPerm low high as as') (hhk: high < k)
  {hks: k < as.size} {hks': k < as'.size}: as[k]'hks = as'[k]'hks' := by
  apply Option.some_inj.mp
  simp only [← getElem?_lt]
  apply hp.getElem?_higher hhk

end IPerm

def IForAll (as: Array α) (low high: Nat) (P: α → Prop) :=
  ∀ k, (hks: k < as.size) → low ≤ k → (hkh: k < high) → P (as[k]'hks)

abbrev IForAllSwap (as: Array α) (i j) (his: i < as.size) (hjs: j < as.size) (low high: Nat)(P: α → Prop)  :=
  IForAll (as.swap ⟨i, his⟩ ⟨j, hjs⟩) low high P

namespace IForAll
theorem map {P: α → Prop} {Q: α → Prop} (ha: IForAll as low high P) (f: (a: α) → P a → Q a):
  IForAll as low high Q := by
  intro k hks hlk hkh
  specialize ha k hks hlk hkh
  exact f as[k] ha

theorem swap_left
    (hij: i ≤ j) {hjs: j < as.size} (hjp: P (as[j]'hjs))
    (ha: IForAll as low i P):
    IForAllSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs low (i + 1) P := by
  intro k hks hlk hki1
  rw [size_swap] at hks
  simp only [swap_def]
  by_cases hki: k < i
  · rw [getElem_set_ne, getElem_set_ne]
    exact ha k hks hlk hki
    · exact Ne.symm (Nat.ne_of_lt hki)
    · have hkj: k < j := Nat.lt_of_lt_of_le hki hij
      exact Ne.symm (Nat.ne_of_lt hkj)
  · have hki: k = i := Nat.eq_of_lt_succ_of_not_lt hki1 hki
    subst k
    by_cases hij: i = j
    · subst i
      simp only [getElem_set_eq]
      exact hjp
    rw [getElem_set_ne, getElem_set_eq]
    exact hjp
    · rfl
    · intro h
      exact hij (Eq.symm h)

theorem swap_right
    (hij: i ≤ j) (hjs: j < as.size)
    (hb: IForAll as i j P):
    IForAllSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs (i + 1) (j + 1) P := by
  intro k hks hi1x hkj1
  rw [size_swap] at hks
  simp only [swap_def]
  by_cases hkj: k < j
  · rw [getElem_set_ne, getElem_set_ne]
    have hik: i ≤ k := Nat.le_of_succ_le hi1x
    exact hb k hks hik hkj
    · exact Nat.ne_of_lt hi1x
    · exact Ne.symm (Nat.ne_of_lt hkj)
  · have hkj: k = j := Nat.eq_of_lt_succ_of_not_lt hkj1 hkj
    subst k
    simp only [getElem_set_eq]
    exact hb i (Nat.lt_trans hi1x hjs) (Nat.le_refl i) hi1x

theorem of_swap
    (hli: low ≤ i) (hij: i ≤ j) (hjh: j < high) {hjs: j < as.size}
    (h: IForAllSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs
      low high P): IForAll as low high P := by
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
end IForAll

def ITrans (as: Array α) (low high: Nat) (r:  α → α → Prop) :=
  (i: Nat) → (his: i < as.size) → low ≤ i → i ≤ high →
  (j: Nat) → (hjs: j < as.size) → low ≤ j → j ≤ high →
  (k: Nat) → (hks: k < as.size) → low ≤ k → k ≤ high →
  r (as[i]'his) (as[j]'hjs) → r (as[j]'hjs) (as[k]'hks) → r (as[i]'his) (as[k]'hks)

 /--
 Turns a relation into one that behaves like le
 If r is <, then this means a[i] < a[j] or a[j] !< a[i] => a[i] ≤ a[j]
 If r is <=, then this means a[i] ≤ a[j] or a[j] !≤ a[i] => a[i] ≤ a[j]
  -/
abbrev le_of_relation (r:  α → α → Bool) (i j: α) := r i j = true ∨ r j i = false

def ITransLeB (as: Array α) (low high: Nat) (r:  α → α → Bool) :=
  ITrans as low high (le_of_relation r)

def le_of_relation_refl (r:  α → α → Bool) (x: α): (le_of_relation r) x x := by
  by_cases h: r x x
  · left
    exact h
  · right
    exact eq_false_of_ne_true h

set_option hygiene false in
macro "transport_lemmas"
  α:ident
  "(" T:term ")"
  "(" Ts:term* ")"
  "(" ub:term ")"
  "(" ub':term ")"
  trans:ident
  not_trans:ident
  intros:num : command =>
`(
  theorem restrict {as: Array $α} {low high low' high': Nat} (ha: $T as low high $Ts*)
    (hll: low ≤ low') (hhh: high' ≤ high)
    : $T as low' high' $Ts* := by
  iterate $intros intro _
  apply ha
  all_goals
    try first
    | apply Nat.le_trans hll _
    | apply Nat.le_trans _ hhh
    assumption

  theorem transport_enclosing {as as': Array $α} {low high plow phigh: Nat}
    (h : $T as low high $Ts*)
    (hp : IPerm plow phigh as as')
    (hll: low ≤ plow)
    (hhh: $ub phigh high) :
    $T as' low high $Ts* := by
  induction hp with
  | refl => exact h
  | trans _ _ ih ih' => exact ih' (ih h)
  | swap as a has hpla haph b hbs hplb hbph =>
    have hla := Nat.le_trans hll hpla
    have hlb := Nat.le_trans hll hplb
    have hah := $trans haph hhh
    have hbh := $trans hbph hhh
    iterate $intros intro _
    simp [swap_def]
    repeat rw [getElem_set]
    repeat any_goals split
    all_goals
      apply h
      all_goals assumption

  theorem transport_outside {as as': Array $α} {low high plow phigh: Nat}
    (h : $T as low high $Ts*)
    (hp : IPerm plow phigh as as')
    (hd: (k: Nat) → (hlk: low ≤ k) → (hkh: $ub k high) → (hplk: plow ≤ k) → (hkph: k ≤ phigh) → False):
    $T as' low high $Ts* := by
  induction hp with
  | refl => exact h
  | trans _ _ ih ih' => exact ih' (ih h)
  | swap as i his hli hih j hjs hlj hjh  =>
    iterate $intros intro _
    simp [swap_def]
    repeat rw [getElem_set_ne]
    · apply h
      all_goals assumption
    all_goals
      intro he
      subst_eqs
      apply hd
      all_goals assumption

  theorem transport_lower {as as': Array $α} {low high plow phigh: Nat}
    (h : $T as low high $Ts*)
    (hp : IPerm plow phigh as as')
    (hd: $ub' high plow):
    $T as' low high $Ts* := by
  apply transport_outside h hp
  intro k _ hkh hplk _
  exact $not_trans ($trans hplk hkh) hd

  theorem transport_higher {as as': Array $α} {low high plow phigh: Nat}
    (h : $T as low high $Ts*)
    (hp : IPerm plow phigh as as')
    (hd: phigh < low):
    $T as' low high $Ts* := by
  apply transport_outside h hp
  intro k hlk _ _ hkph
  exact Nat.not_lt.mpr (Nat.le_trans hlk hkph) hd
)

namespace IForAll
variable {α} {P: α → Prop}
transport_lemmas α (IForAll) (P) (LT.lt) (LE.le) Nat.lt_of_le_of_lt Nat.not_le.mpr 4
end IForAll

namespace ITrans
variable {α} {r: α → α → Prop}

transport_lemmas α (ITrans) (r) (LE.le) (LT.lt) Nat.le_trans Nat.not_lt.mpr 12
end ITrans

def IPairwise (r:  α → α → Prop) (low high: Nat) (as: Array α) :=
   ∀ i j, (hli: low ≤ i) → (hij: i < j) → (hjh: j ≤ high) → (hjs: j < as.size) →
  r (as[i]'(Nat.lt_trans hij hjs)) (as[j]'hjs)

/--
If r is <, then this means a[i] < a[j] or a[j] !< a[i] => a[i] ≤ a[j]
If r is <=, then this means a[i] ≤ a[j] or a[j] !≤ a[i] => a[i] ≤  a[j]
 -/
abbrev IPairwiseLeB (r:  α → α → Bool) (low: Nat) (high: Nat) (as: Array α) :=
  IPairwise (le_of_relation (r · ·)) low high as

namespace IPairwise
theorem mkSingle (r : α → α → Prop) (k: Nat) (as: Array α):
    IPairwise r k k as := by
  unfold IPairwise
  intro i j hli hij hjl hjs
  exfalso
  have hkk: k < k := Nat.lt_of_le_of_lt hli (Nat.lt_of_lt_of_le hij hjl)
  exact (Nat.ne_of_lt hkk) rfl

theorem restrict (hll: low ≤ low') (hhh: high' ≤ high) {as: Array α}
    (p: IPairwise r low high as): IPairwise r low' high' as := by
  unfold IPairwise
  intro i j hli hij hjl hjs
  exact p i j (Nat.le_trans hll hli) hij (Nat.le_trans hjl hhh) hjs

theorem resize_out_of_bounds (h: IPairwise r low high as) (hsh: (as.size - 1) ≤ high):
  IPairwise r low high' as := by
  unfold IPairwise
  intro i j hli hij _ hjs
  have hjh: j ≤ high := Nat.le_trans (Nat.le_sub_one_of_lt hjs) hsh
  exact h i j hli hij hjh hjs

theorem transport_outside
    (h : as.IPairwise r low high)
    (hp : IPerm plow phigh as as')
    (hd: (k: Nat) → (hlk: low ≤ k) → (hkh: k ≤ high) → (hplk: plow ≤ k) → (hkph: k ≤ phigh) → False):
    as'.IPairwise r low high := by
induction hp with
| refl => exact h
| trans _ _ ih ih' => exact ih' (ih h)
| swap as i his hli hih j hjs hlj hjh =>
  intro a b hla hab hbl hbs
  have hal := Nat.lt_of_lt_of_le hab hbl
  simp [swap_def]
  repeat rw [getElem_set_ne]
  · simp [size_swap] at hbs
    exact h a b hla hab hbl hbs
  all_goals
    intro he
    simp only at he
    subst_eqs
  · exact hd i (Nat.le_trans hla (Nat.le_of_lt hab)) hbl hli hih
  · exact hd j (Nat.le_trans hla (Nat.le_of_lt hab)) hbl hlj hjh
  · exact hd i hla (Nat.le_of_lt hal) hli hih
  · exact hd j hla (Nat.le_of_lt hal) hlj hjh

theorem transport_lower
    (h : as.IPairwise r low high)
    (hp : IPerm plow phigh as as')
    (hd: high < plow):
    as'.IPairwise r low high := by
  apply h.transport_outside hp
  intro k _ hkh hplk _
  exact Nat.not_lt.mpr (Nat.le_trans hplk hkh) hd

theorem transport_higher
    (h : as.IPairwise r low high)
    (hp : IPerm plow phigh as as')
    (hd: phigh < low):
    as'.IPairwise r low high := by
  apply h.transport_outside hp
  intro k hlk _ _ hkph
  exact Nat.not_lt.mpr (Nat.le_trans hlk hkph) hd

/-
theorem glue_with_pivot
    (ha : as.IForAll low (i + 1) (r · pivot))
    (hb : as.IForAll (i + 1) (high + 1) (r pivot ·))
    (hrtle : ITrans as low high r)
    (h1 : IPairwise r low i as)
    (h2 : IPairwise r (i + 1) high as):
    IPairwise r low high as := by
  unfold IPairwise
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
  exact hrtle ha hb
-/

theorem glue_with_middle
    (his: i < as.size)
    (ha : as.IForAll low i (r · (as[i]'his)))
    (hb : as.IForAll (i + 1) (high + 1) (r (as[i]'his) ·))
    (hrtle : ITrans as low high r)
    (h1 : IPairwise r low (i - 1) as)
    (h2 : IPairwise r (i + 1) high as):
    IPairwise r low high as := by
  unfold IPairwise
  intro a b hla hab hbh hbs
  have has := Nat.lt_trans hab hbs

  by_cases hbi: b < i
  · exact h1 a b hla hab (Nat.le_sub_one_of_lt hbi) hbs

  have hib: i ≤ b := Nat.le_of_not_lt hbi
  by_cases hia: i < a
  · exact h2 a b hia hab hbh hbs

  have hai: a ≤ i := by exact Nat.le_of_not_lt hia

  have ha: a < i → r (as[a]'has) (as[i]'his) := λ hai' ↦ ha a has hla hai'
  have hb: i < b → r (as[i]'his) (as[b]'hbs) := λ hib' ↦ hb b hbs hib' (Nat.lt_add_one_of_le hbh)

  have hah := Nat.le_trans (Nat.le_of_lt hab) hbh
  have hli := Nat.le_trans hla hai
  have hih := Nat.le_trans hib hbh
  have hlb := Nat.le_trans hla (Nat.le_of_lt hab)

  by_cases hai': a < i
  · by_cases hib': i < b
    · exact hrtle a has hla hah i his hli hih b hbs hlb hbh (ha hai') (hb hib')
    · have hib: i = b := by exact Nat.le_antisymm hib (Nat.le_of_not_lt hib')
      subst b
      exact (ha hai')
  · have hai: a = i := by exact Nat.le_antisymm hai (Nat.le_of_not_lt hai')
    subst a
    exact (hb hab)

theorem glue_with_middle_eq_pivot
    {r : α → α → Prop} {low high : Nat} {i : Nat} {as : Array α}
    (his: i < as.size)
    (hpi: as[i]'his = pivot)
    (ha : as.IForAll low i (r · pivot))
    (hb : as.IForAll (i + 1) (high + 1) (r pivot ·))
    (hrtle : ITrans as low high r)
    (h1 : IPairwise r low (i - 1) as)
    (h2 : IPairwise r (i + 1) high as):
    IPairwise r low high as := by
    subst pivot
    apply glue_with_middle
    all_goals assumption

end IPairwise

abbrev swap_getElem (as: Array α) (i j k: Nat) (his: i < as.size) (hjs: j < as.size) (hks: k < as.size): α :=
  (as.swap ⟨i, his⟩ ⟨j, hjs⟩)[k]'(
      le_of_le_of_eq hks (Eq.symm (size_swap as ⟨i, his⟩ ⟨j, hjs⟩))
    )

theorem getElem_after_swap (as: Array α) (hij: i ≤ j) (hjh: j < high) (hhs: high < as.size):
    as.swap_getElem i j high (Nat.lt_of_le_of_lt hij (Nat.lt_trans hjh hhs)) (Nat.lt_trans hjh hhs) hhs
    = (as[high]'hhs) := by
  simp [swap_getElem, swap_def]
  rw [getElem_set_ne]
  rw [getElem_set_ne]
  · exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hij hjh)
  · exact Nat.ne_of_lt (hjh)

structure ISortOf (r: α → α → Prop) (low high: Nat) (orig: Array α) (sorted: Array α): Prop where
  perm: IPerm low high orig sorted
  ord: IPairwise r low high sorted

abbrev ISortOfLeB (r: α → α → Bool) (low high: Nat) (orig: Array α) (sorted: Array α): Prop
  := ISortOf (le_of_relation r) low high orig sorted

namespace ISortOf
theorem mkSingle (r: α → α → Prop) (k: Nat) (as0: Array α) (as: Array α) (hp: IPerm k k as0 as):
    ISortOf r k k as0 as := ⟨hp, .mkSingle r k as⟩

theorem trans
    (hp: IPerm low high as as') (hs: ISortOf r low high as' as''):
    (ISortOf r low high as as'') := by
  constructor
  case perm => exact hp.trans hs.perm
  case ord => exact hs.ord

theorem resize_out_of_bounds (h: ISortOf r low high as0 as) (hsh: (as.size - 1) ≤ high) (hsh': (as0.size - 1) ≤ high'):
  ISortOf r low high' as0 as := by
  constructor
  case perm => exact h.perm.resize_out_of_bounds hsh'
  case ord => exact h.ord.resize_out_of_bounds hsh
end ISortOf

mutual
  theorem qsort.sort_sort_sorts (r: α → α → Bool) (low high : Nat) (pivot : α) (i : Nat) (as: Array α)
      (hlh: low < high) (hli : low ≤ i) (hih : i ≤ high) (hhs : high < as.size)
      (hpi: as[i]'(Nat.lt_of_le_of_lt hih hhs) = pivot)
      (ha: IForAll as low (i + 1) ((le_of_relation r) · pivot))
      (hb: IForAll as (i + 1) (high + 1) ((le_of_relation r) pivot ·))
      (hrtle: ITransLeB as low high r):
      have ⟨as', hs'⟩ := qsort.sort r as low (i - 1) (λ _ ↦ Nat.lt_of_le_of_lt (Nat.sub_le i 1) (Nat.lt_of_le_of_lt hih hhs))
      ISortOfLeB r low high as (qsort.sort r as' (i + 1) high (λ _ ↦ hs' ▸ hhs)) := by
    have his := Nat.lt_of_le_of_lt hih hhs
    have h1ih: i - 1 ≤ high := Nat.le_trans (Nat.sub_le i 1) hih
    have h1is: i - 1 < as.size := Nat.lt_of_le_of_lt h1ih hhs

    have h1 := qsort.sort_sorts as r low (i - 1) (λ _ ↦ h1is) (hrtle.restrict (Nat.le_refl _) h1ih)

    let ahs' := qsort.sort r as low (i - 1) (λ _ ↦ h1is)
    let as' := ahs'.1
    let hs' := ahs'.2
    have h2 := by
      apply qsort.sort_sorts as' r (i + 1) high (λ _ ↦ hs' ▸ hhs) ((hrtle.restrict ?_ ?_).transport_higher h1.perm ?_)
      · exact Nat.le_add_right_of_le hli
      · exact Nat.le_refl _
      · exact Nat.sub_lt_succ i 1

    constructor
    case perm =>
      apply IPerm.trans
      · apply IPerm.expand (Nat.le_refl _) h1ih h1.perm
      · apply IPerm.expand (Nat.le_add_right_of_le hli) (Nat.le_refl _) h2.perm

    case ord =>
      apply IPairwise.glue_with_middle_eq_pivot
      case hrtle =>
        apply (hrtle.transport_enclosing h1.perm ?_ ?_).transport_enclosing h2.perm ?_ ?_
        · exact Nat.le_refl _
        · exact h1ih
        · exact Nat.le_add_right_of_le hli
        · exact Nat.le_refl _
      case i => exact i
      case his => simpa [qsort.size_sort]
      case ha =>
        apply ((ha.transport_enclosing h1.perm ?_ ?_).transport_lower h2.perm ?_).restrict ?_ ?_
        · exact Nat.le_refl _
        · exact Nat.sub_lt_succ i 1
        · exact Nat.le_refl (i + 1)
        · exact Nat.le_refl low
        · exact Nat.le_add_right i 1
      case hb =>
        apply (hb.transport_higher h1.perm ?_).transport_enclosing h2.perm ?_ ?_
        · exact Nat.sub_lt_succ i 1
        · exact Nat.le_refl _
        · exact Nat.lt_add_one high
      case hpi =>
        subst pivot
        simp only [as', ahs'] at h2 -- needed?

        by_cases h0i: 0 < i
        · rw [h1.perm.getElem_higher]
          rw [h2.perm.getElem_lower]
          · exact Nat.lt_add_one i
          · exact Nat.lt_of_lt_of_eq his hs'.symm
          · exact Nat.sub_one_lt_of_lt h0i
        · have h0i: i = 0 := by exact Nat.eq_zero_of_not_pos h0i
          subst i
          have: low = 0 := by exact Nat.eq_zero_of_le_zero hli
          subst low
          simp_all
          simp [h1.perm.eq_of_trivial]
          rw [h2.perm.getElem_lower]
          exact Nat.one_pos

      case h1 =>
        apply h1.ord.transport_lower h2.perm (Nat.sub_lt_succ i 1)
      case h2 => exact h2.ord
      termination_by (high - low, 0, 0)

  theorem qsort.sort_loop_sorts (r: α → α → Bool) (low high : Nat) (hlh: low < high) (as: Array α)
      (i j : Nat)
      (hli : low ≤ i) (hij : i ≤ j) (hjh : j ≤ high) (hhs : high < as.size) (hph: as[high]'hhs = pivot)
      (ha: IForAll as low i (r · pivot))
      (hb: IForAll as i j (r · pivot = false))
      (hrtle: ITransLeB as low high r):
      ISortOfLeB r low high as (qsort.sort.loop r low high hlh pivot as i j hli hij hjh hhs) := by
    unfold qsort.sort.loop

    have hjs: j < as.size := Nat.lt_of_le_of_lt hjh hhs
    have his: i < as.size := Nat.lt_of_le_of_lt hij hjs
    have hih: i ≤ high := Nat.le_trans hij hjh
    have hlj: low ≤ j := Nat.le_trans hli hij

    by_cases hjh': j < high
    all_goals simp only [hjh', ↓reduceDIte]

    case pos =>
      have hjs: j < as.size := Nat.lt_trans hjh' hhs
      by_cases hjp: r (as[j]'hjs) pivot = true
      all_goals simp only [hjp, Bool.false_eq_true, ↓reduceIte]

      case pos =>
        apply ISortOf.trans
        case hs =>
          apply qsort.sort_loop_sorts
          case hph => simpa only [getElem_after_swap _ hij hjh' hhs]
          case ha => exact ha.swap_left hij hjp
          case hb => exact hb.swap_right hij hjs
          case hrtle => exact hrtle.transport_enclosing (IPerm.swap _ _ _ hli hih _ _ hlj hjh) (Nat.le_refl _) (Nat.le_refl _)
        case hp => exact .swap as i his hli hih j hjs hlj hjh

      case neg =>
        apply ISortOf.trans
        case hs =>
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

          case hrtle => exact hrtle
        case hp => exact .refl

    case neg =>
      have hjh: j = high := Nat.le_antisymm hjh (Nat.le_of_not_lt hjh')
      subst j
      apply ISortOf.trans
      case hs =>
        apply qsort.sort_sort_sorts
        case hhs => simpa [size_swap]
        case ha =>
          let ha: as.IForAll low i (le_of_relation r · pivot) := ha.map (λ x a ↦ by
            left
            exact a)

          exact (hph ▸ ha).swap_left hij (le_of_relation_refl r _)
        case hb =>
          let hb: as.IForAll i high (le_of_relation r pivot ·) := hb.map (λ x a ↦ by
            right
            exact a)
          exact (hph ▸ hb).swap_right hij hhs
        case hrtle => exact hrtle.transport_enclosing (IPerm.swap _ _ _ hli hih _ _ hlj hjh) (Nat.le_refl _) (Nat.le_refl _)
        case hli => exact hli
        case hih => exact hih
        case hlh => exact hlh
        case hpi =>
          simp only [swap_def, get_eq_getElem, getElem_set, getElem_set_eq, ite_eq_right_iff, ↓reduceIte]
          intro h
          simp only [h]
      case hp =>
        exact IPerm.swap as i his hli hih high hhs (Nat.le_of_lt hlh) (Nat.le_refl _)
    termination_by (high - low, 1, high - j)

  theorem qsort.sort_loop_pivot_swap_sorts (r: α → α → Bool) (low high : Nat) (hlh: low < high) (as: Array α)
      (mid: Nat) (hlm: low ≤ mid) (hmh: mid < high) (hhs : high < as.size)
      (hrtle: ITransLeB as low high r):

      let as' := if r (as[mid]'(Nat.lt_trans hmh hhs)) (as[high]'hhs) then as.swap ⟨mid, Nat.lt_trans hmh hhs⟩ ⟨high, hhs⟩ else as
      have hs': as'.size = as.size := by dsimp only [as']; split; all_goals simp_all only [Array.size_swap]

      ISortOfLeB r low high as (qsort.sort.loop r low high hlh (as'[high]'(hs' ▸ hhs)) as' low low
        (Nat.le_refl low) (Nat.le_refl low) (Nat.le_trans hlm (Nat.le_of_lt hmh)) (hs' ▸ hhs)).1 := by
    have hms := Nat.lt_trans hmh hhs
    have hlh := Nat.le_trans hlm (Nat.le_of_lt hmh)

    apply ISortOf.trans
    case hs =>
      apply qsort.sort_loop_sorts
      case hph => rfl
      case hrtle =>
        apply hrtle.transport_enclosing ?_ (Nat.le_refl _) (Nat.le_refl _)
        apply IPerm.ite
        · apply IPerm.swap
          all_goals
            first
            | apply Nat.le_refl _
            | assumption
            | apply Nat.le_of_lt; assumption
        · apply IPerm.refl
      all_goals
        intro k hks hlk hkl
        have hll: low < low := Nat.lt_of_le_of_lt hlk hkl
        exfalso
        exact (Nat.ne_of_lt hll) rfl
    case hp =>
      split
      case isTrue h =>
        exact .swap as mid hms hlm (Nat.le_of_lt hmh) high hhs hlh (Nat.le_refl _)
      case isFalse h =>
        exact .refl
    termination_by (high - low, 2, 0)

  theorem qsort.sort_sorts (as: Array α) (r: α → α → Bool) (low := 0) (high := as.size - 1)
      (hhs: low < high → high < as.size)
      (hrtle: ITransLeB as low high r):
      ISortOfLeB r low high as (qsort.sort r as low high hhs) := by
      unfold qsort.sort
      by_cases hlh: low ≥ high
      case pos =>
        simp [hlh]
        constructor
        case ord =>
          intro i j hli hij hjh hjs
          have hlh' := Nat.lt_of_le_of_lt hli (Nat.lt_of_lt_of_le hij hjh)
          exfalso
          have hlh'': ¬(low ≥ high) := by
            exact Nat.not_le_of_lt hlh'
          exact hlh'' hlh
        case perm =>
          exact IPerm.refl
      case neg =>
        simp only [hlh]
        have hlh: low < high := Nat.gt_of_not_le hlh
        have hlh': low ≤ high := Nat.le_of_lt hlh

        apply ISortOf.trans
        case hs =>
          apply qsort.sort_loop_pivot_swap_sorts

          case hlm => exact Nat.left_le_add_div_two.mpr hlh'
          case hmh => exact Nat.add_div_two_lt_right.mpr hlh

          case hrtle =>
            apply hrtle.transport_enclosing ?hp (Nat.le_refl _) (Nat.le_refl _)
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

theorem qsort_sorts (as: Array α) (r: α → α → Bool) (low := 0) (high := as.size - 1)
    (hrtle: ITransLeB as low high r):
    ISortOfLeB r low high as (qsort as r low high)  := by
    unfold qsort
    split
    case isTrue =>
      apply qsort.sort_sorts
      · exact hrtle
    case isFalse h =>
      have hsh: as.size - 1 ≤ high := by
        apply Nat.sub_le_of_le_add
        exact Nat.le_add_right_of_le (Nat.le_of_not_lt h)
      apply ISortOf.resize_out_of_bounds
      · apply qsort.sort_sorts
        case hrtle => exact hrtle.restrict (Nat.le_refl _) hsh
      · simp only [qsort.size_sort, Nat.le_refl]
      · exact hsh

end Array
