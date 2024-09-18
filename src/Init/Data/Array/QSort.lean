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

@[inline] def qsort (as : Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1) : Array α :=
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

      let as := if f (as[mid]'(hs ▸ hms)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨mid, hs ▸ hms⟩ else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if f (as[high]'(hs ▸ hhs)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨high, hs ▸ hhs⟩  else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if f (as[mid]'(hs ▸ hms)) (as[high]'(hs ▸ hhs)) then as.swap ⟨mid, hs ▸ hms⟩ ⟨high, hs ▸ hhs⟩ else as
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

          if f (as[j]'(hs ▸ hjs)) pivot then
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

@[simp] theorem qsort.size_sort (as : Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1)
    (hhs: low < high → high < as.size):
    (qsort.sort f as low high hhs).1.size = as.size := by
  exact (qsort.sort f as low high hhs).2

@[simp] theorem size_qsort (as : Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1):
    (qsort as f low high).size = as.size := by
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

def IForAllIco (P: α → Prop) (low high: Nat) (as: Array α) :=
  ∀ k, (hks: k < as.size) → low ≤ k → (hkh: k < high) → P (as[k]'hks)

def IForAllIcc (P: α → Prop) (low high: Nat) (as: Array α) :=
  (i: Nat) → (his: i < as.size) → low ≤ i → i ≤ high →
  P (as[i]'his)

def IForAllIcc2 (P: α → α → Prop) (low high: Nat) (as: Array α) :=
  (i: Nat) → (his: i < as.size) → low ≤ i → i ≤ high →
  (j: Nat) → (hjs: j < as.size) → low ≤ j → j ≤ high →
  P (as[i]'his) (as[j]'hjs)

def IForAllIcc3 (P: α → α → α → Prop) (low high: Nat) (as: Array α) :=
  (i: Nat) → (his: i < as.size) → low ≤ i → i ≤ high →
  (j: Nat) → (hjs: j < as.size) → low ≤ j → j ≤ high →
  (k: Nat) → (hks: k < as.size) → low ≤ k → k ≤ high →
  P (as[i]'his) (as[j]'hjs) (as[k]'hks)

/-
def IForAllIcc2I (P: Nat → Nat → α → α → Prop) (low high: Nat) (as: Array α) :=
  (i: Nat) → (his: i < as.size) → low ≤ i → i ≤ high →
  (j: Nat) → (hjs: j < as.size) → low ≤ j → j ≤ high →
  P i j (as[i]'his) (as[j]'hjs)

--  equivalent IForAllIcc2I (λ i j x y ↦ i < j → r x y) low high as
-/

def IPairwise (r:  α → α → Prop) (low high: Nat) (as: Array α) :=
   ∀ i j, (hli: low ≤ i) → (hij: i < j) → (hjh: j ≤ high) → (hjs: j < as.size) →
  r (as[i]'(Nat.lt_trans hij hjs)) (as[j]'hjs)

abbrev IForAllIcoSwap (as: Array α) (i j) (his: i < as.size) (hjs: j < as.size) (low high: Nat) (P: α → Prop)  :=
  IForAllIco P low high (as.swap ⟨i, his⟩ ⟨j, hjs⟩)

namespace IForAllIco
theorem map {P: α → Prop} {Q: α → Prop} (ha: IForAllIco P low high as) (f: (a: α) → P a → Q a):
  IForAllIco Q low high as := by
  intro k hks hlk hkh
  specialize ha k hks hlk hkh
  exact f as[k] ha

theorem swap_left
    (hij: i ≤ j) {hjs: j < as.size} (hjp: P (as[j]'hjs))
    (ha: IForAllIco P low i as):
    IForAllIcoSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs low (i + 1) P := by
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
    (hb: IForAllIco P i j as):
    IForAllIcoSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs (i + 1) (j + 1) P := by
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
    (h: IForAllIcoSwap as i j (Nat.lt_of_le_of_lt hij hjs) hjs
      low high P): IForAllIco P low high as := by
  have his := Nat.lt_of_le_of_lt hij hjs
  intro k hks hlk hkh
  simp [IForAllIcoSwap, IForAllIco, size_swap, swap_def] at h
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
end IForAllIco

abbrev ITrans (r:  α → α → Prop) :=
  IForAllIcc3 (λ x y z ↦ r x y → r y z → r x z)

 /--
 Turns a relation into one that behaves like le
 If r is <, then this means a[i] < a[j] or a[j] !< a[i] => a[i] ≤ a[j]
 If r is <=, then this means a[i] ≤ a[j] or a[j] !≤ a[i] => a[i] ≤ a[j]
  -/
abbrev Completion (r:  α → α → Prop) := λ x y ↦ r x y ∨ ¬r y x

namespace Completion

def pos (h: r x y): Completion r x y := by
  left
  exact h

def neg (h: ¬r y x): Completion r x y := by
  right
  exact h

def wtotal (h: ¬Completion r x y): Completion r y x := by
  right
  intro h'
  exact h (Or.inl h')

def refl [DecidableRel r] (x): Completion r x x := by
  by_cases h: r x x
  · exact pos h
  · exact neg h

def stotal [DecidableRel r]: Completion r x y ∨ Completion r y x := by
  by_cases h: Completion r x y
  · left
    exact h
  · right
    exact wtotal h

end Completion

abbrev ICompat (hr:  α → α → Prop) (r:  α → α → Prop) :=
  IForAllIcc2 (λ x y ↦ hr x y → r x y)

abbrev ITransCompat (hr: α → α → Prop) (r: α → α → Prop) (low high: Nat) (as: Array α) :=
  (ICompat hr r low high as) ∧ (ITrans r low high as)

abbrev ITransCompatCB (f: α → α → Bool) (r: α → α → Prop) (low high: Nat) (as: Array α) :=
  ITransCompat (Completion (f · ·)) r low high as

inductive ITransGen {α} (r : α → α → Prop) (low high: Nat) (as: Array α) : α → α → Prop
| base (i: Nat) (his: i < as.size) (hli: low ≤ i) (hih: i ≤ high) (j: Nat) (hjs: j < as.size) (hlj: low ≤ j) (hjh: j ≤ high)
    (h: r (as[i]'his) (as[j]'hjs)): ITransGen r low high as (as[i]'his) (as[j]'hjs)
| trans {a b c} : ITransGen r low high as a b → ITransGen r low high as b c → ITransGen r low high as a c

namespace ITransCompat

def compat (h: ITransCompat hr r low high as): ICompat hr r low high as := h.1
def trans (h: ITransCompat hr r low high as): ITrans r low high as := h.2

def mkITransGen: ITransCompatCB f (ITransGen (Completion (f · ·)) low high as) low high as := by
  constructor
  · apply ITransGen.base
  · intro i his _ _ j hjs _ _ k hks _ _
    apply ITransGen.trans

end ITransCompat

namespace ITransCompatCB

export ITransCompat (compat trans)

end ITransCompatCB

local macro "elementwise"
  t:term : tactic =>
`(tactic| {
    intros
    constructor
    all_goals
      apply $t
      all_goals assumption
})

local macro "elementwise"
 t:term "using" h:ident : tactic =>
`(tactic| {
    intros
    constructor
    · apply $t
      try any_goals assumption
      exact $h.1
    · apply $t
      try any_goals assumption
      exact $h.2
})

class Trivial (α) (T: Nat → Nat → Array α → Prop) (ub': Nat → Nat → Prop) where
  trivial (hll: ub' high low): T low high as

export Trivial (trivial)

instance [Trivial α T1 ub'] [Trivial α T2 ub']:
    Trivial α (λ low high as ↦ (T1 low high as) ∧ (T2 low high as)) ub' where
  trivial hhl := by elementwise trivial hhl

instance {k: Nat} {as: Array α} [Trivial α T LE.le]: Inhabited (T k k as) where
  default := trivial (Nat.le_refl _)

instance {k: Nat} {as: Array α} [Trivial α T LE.le]: Inhabited (T k (k - 1) as) where
  default := trivial (Nat.sub_le k 1)

instance {k: Nat} {as: Array α} [Trivial α T LE.le]: Inhabited (T (k + 1) k as) where
  default := trivial (Nat.le_add_right k 1)

instance {k: Nat} {as: Array α} [Trivial α T LT.lt]: Inhabited (T (k + 1) k as) where
  default := trivial (Nat.lt_add_one k)

class Restrictable (α) (T: Nat → Nat → Array α → Prop) where
  restrict (ha: T low high as)
    (hll: low ≤ low') (hhh: high' ≤ high)
    : T low' high' as

export Restrictable (restrict)

instance [Restrictable α T1] [Restrictable α T2]:
    Restrictable α (λ low high as ↦ (T1 low high as) ∧ (T2 low high as)) where
  restrict h := by elementwise restrict using h

class RestrictableOutOfBounds (α) (T: Nat → Nat → Array α → Prop) (ub: outParam (Nat → Nat → Prop)) where
  restrict_out_of_bounds {low high: Nat} {as: Array α} {high': Nat} (ha: T low high as)
    (hsh: ub (as.size - 1) high): T low high' as

export RestrictableOutOfBounds (restrict_out_of_bounds)

instance [RestrictableOutOfBounds α T1 ub] [RestrictableOutOfBounds α T2 ub]:
    RestrictableOutOfBounds α (λ low high as ↦ (T1 low high as) ∧ (T2 low high as)) ub where
  restrict_out_of_bounds h := by elementwise restrict_out_of_bounds using h

class TransportableOutside (α) (T: Nat → Nat → Array α → Prop) (ub: outParam (Nat → Nat → Prop)) where
  transport_outside
    (h : T low high as)
    (hp : IPerm plow phigh as as')
    (hd: (k: Nat) → (hlk: low ≤ k) → (hkh: ub k high) → (hplk: plow ≤ k) → (hkph: k ≤ phigh) → False):
    T low high as'

export TransportableOutside (transport_outside)

instance [TransportableOutside α T1 ub] [TransportableOutside α T2 ub]:
    TransportableOutside α (λ low high as ↦ (T1 low high as) ∧ (T2 low high as)) ub where
  transport_outside h := by elementwise transport_outside using h

class LteOp (r: Nat → Nat → Prop) where
  co: Nat → Nat → Prop
  of_le_of: ∀ {x y z: Nat}, (x ≤ y) → (r y z) → r x z
  not: ¬(co a b) ↔ (r b a)
  succ: Nat → Nat
  r_succ: ∀ x, r x (succ x)

instance: LteOp (LE.le) where
  co := LT.lt
  of_le_of xy yz := Nat.le_trans xy yz
  not := Nat.not_lt
  succ x := x
  r_succ x := Nat.le_refl x

instance: LteOp (LT.lt) where
  co := LE.le
  of_le_of xy yz := Nat.lt_of_le_of_lt xy yz
  not := Nat.not_le
  succ x := (x + 1)
  r_succ x := Nat.lt_add_one x

theorem transport_lower {α} {T: Nat → Nat → Array α → Prop}
    [TransportableOutside α T r] [LteOp r]
   {low high: Nat} {as: Array α}{plow phigh: Nat} {as': Array α}
    (h : T low high as)
    (hp : IPerm plow phigh as as')
    (hd: LteOp.co r high plow):
    T low high as' := by
  apply transport_outside h hp (ub := r)
  intro k _ hkh hplk _
  exact LteOp.not.mpr (LteOp.of_le_of hplk hkh) hd

theorem transport_higher {α} {T: Nat → Nat → Array α → Prop}
    [TransportableOutside α T r] [LteOp r]
    {low high: Nat} {as: Array α}{plow phigh: Nat} {as': Array α}
    (h : T low high as)
    (hp : IPerm plow phigh as as')
    (hd: phigh < low):
    T low high as' := by
  apply transport_outside h hp (ub := r)
  intro k hlk _ _ hkph
  exact Nat.not_lt.mpr (Nat.le_trans hlk hkph) hd

class TransportableEnclosing (α) (T: Nat → Nat → Array α → Prop) (ub: outParam (Nat → Nat → Prop))
    extends TransportableOutside α T ub where
  transport_enclosing
    (h : T low high as)
    (hp : IPerm plow phigh as as')
    (hll: low ≤ plow)
    (hhh: ub phigh high) :
    T low high as'

export TransportableEnclosing (transport_enclosing)

instance [TransportableEnclosing α T1 ub] [TransportableEnclosing α T2 ub]:
    TransportableEnclosing α (λ low high as ↦ (T1 low high as) ∧ (T2 low high as)) ub where
  transport_enclosing h := by elementwise transport_enclosing using h

theorem transport_exact_icc {α} {T: Nat → Nat → Array α → Prop}
    [TransportableEnclosing α T LE.le]
    {low high: Nat} {as: Array α} {as': Array α}
    (h : T low high as)
    (hp : IPerm low high as as'):
    T low high as' := by
  apply transport_enclosing h hp
  · exact Nat.le_refl _
  · exact Nat.le_refl high

theorem transport_exact_ico {α} {T: Nat → Nat → Array α → Prop}
    [TransportableEnclosing α T LT.lt]
    {low high: Nat} {as: Array α} {as': Array α}
    (h : T low (high + 1) as)
    (hp : IPerm low high as as'):
    T low (high + 1) as' := by
  apply transport_enclosing h hp
  · exact Nat.le_refl _
  · exact Nat.lt_add_one high

set_option hygiene false in
scoped macro "impl_trivial"
  α:ident
  "(" T:term ")"
  "(" ub'':term ")"
  intros:num : command =>
`(
  instance: Trivial $α ($T) $ub'' where
    trivial hhl := by
      iterate $intros intro _
      exfalso
      suffices hlh: $ub'' _ _ by
        first
        | exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hlh hhl)
        | exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hhl hlh)
        | done

      try rw [Nat.lt_succ]
      first
      | exact Nat.lt_of_le_of_lt (by assumption) (by assumption)
      | exact Nat.le_trans (by assumption) (by assumption)
      | exact Nat.le_trans (by assumption) (Nat.le_of_lt (by assumption))
      | exact Nat.lt_of_le_of_lt (by assumption) (Nat.lt_of_lt_of_le (by assumption) (by assumption))
      | exact Nat.le_trans (by assumption) (Nat.le_trans (Nat.le_of_lt (by assumption)) (by assumption))
      | done
)

scoped macro "impl_transport_outside"
  α:ident
  "(" T:term ")"
  "(" ub:term ")"
  "(" ub':term ")"
  intros:num : command =>
`(
  impl_trivial $α ($T) ($ub') $intros

  instance: Restrictable $α ($T) where
    restrict h hll hhh := by
      iterate $intros intro _
      apply h
      all_goals
        try first
        | apply Nat.le_trans hll _
        | apply Nat.le_trans _ hhh
        assumption

  instance: RestrictableOutOfBounds $α ($T) $ub where
    restrict_out_of_bounds h hsh := by
      iterate $intros intro _
      apply h
      repeat'
        first
        | assumption
        | apply Nat.le_trans _ hsh
        | apply Nat.succ_le_succ
        | apply Nat.le_sub_one_of_lt
        | done

  instance: TransportableOutside $α ($T) $ub where
    transport_outside h hp hd := by
      induction hp with
      | refl => exact h
      | trans _ _ ih ih' => exact ih' (ih h)
      | swap as i his hli hih j hjs hlj hjh  =>
        iterate $intros intro _
        simp only [swap_def]
        repeat rw [getElem_set_ne]
        · apply h
          all_goals assumption
        all_goals
          intro he
          subst_eqs
          first
          | apply hd i
            all_goals
              first
              | assumption
              | exact (Nat.le_trans (by assumption) (Nat.le_of_lt (by assumption)))
              | exact (Nat.le_of_lt (Nat.lt_of_lt_of_le (by assumption) (by assumption)))
              | done
          | apply hd j
            all_goals
              first
              | assumption
              | exact (Nat.le_trans (by assumption) (Nat.le_of_lt (by assumption)))
              | exact (Nat.le_of_lt (Nat.lt_of_lt_of_le (by assumption) (by assumption)))
              | done
)

scoped macro "impl_transport"
  α:ident
  "(" T:term ")"
  "(" ub:term ")"
  "(" ub':term ")"
  intros:num : command =>
`(
  impl_transport_outside $α ($T) ($ub) ($ub') $intros

  instance: TransportableEnclosing $α ($T) $ub where
    transport_enclosing h hp hll hhh := by
      induction hp with
      | refl => exact h
      | trans _ _ ih ih' => exact ih' (ih h)
      | swap as a has hpla haph b hbs hplb hbph =>
        have hla := Nat.le_trans hll hpla
        have hlb := Nat.le_trans hll hplb
        have hah := LteOp.of_le_of haph hhh
        have hbh := LteOp.of_le_of hbph hhh
        iterate $intros intro _
        simp [swap_def]
        repeat rw [getElem_set]
        repeat' split
        all_goals
          apply h
          all_goals assumption
)

namespace IPairwise
variable {α} {P: α → α → Prop}

impl_trivial α (IPairwise P) (LE.le) 6
impl_transport_outside α (IPairwise P) (LE.le) (LT.lt) 6
end IPairwise

namespace IForAllIco
variable {α} {P: α → Prop}

impl_transport α (IForAllIco P) (LT.lt) (LE.le) 4
end IForAllIco

namespace IForAllIcc
variable {α} {P: α → Prop}

impl_transport α (IForAllIcc P) (LE.le) (LT.lt) 4
end IForAllIcc

namespace IForAllIcc2
variable {α} {P: α → α → Prop}

impl_transport α (IForAllIcc2 P) (LE.le) (LT.lt) 8
end IForAllIcc2

namespace IForAllIcc3
variable {α} {P: α → α → α → Prop}

impl_transport α (IForAllIcc3 P) (LE.le) (LT.lt) 12
end IForAllIcc3

/-
namespace IForAllIcc2I
variable {α} {P: Nat → Nat → α → α → Prop}

impl_transport_outside α (IForAllIcc2I P) (LE.le) 8
end IForAllIcc2I
-/

namespace IPairwise

theorem glue_with_pivot
    {r: α → α → Prop}
    {p: Nat} (hps: p < as.size) (hlp: low ≤ p) (hph: p ≤ high) (hp: pivot = as[p]'hps)
    (ha : IForAllIco (r · pivot) low (i + 1) as)
    (hb : IForAllIco (r pivot ·) (i + 1) (high + 1) as)
    (hrel : ITrans r low high as)
    (h1 : IPairwise r low i as)
    (h2 : IPairwise r (i + 1) high as):
    IPairwise r low high as := by
  unfold IPairwise
  intro a b hla hab hbh hbs
  have has := Nat.lt_trans hab hbs
  have hlb := Nat.le_trans hla (Nat.le_of_lt hab)
  have hah: a ≤ high := Nat.le_trans (Nat.le_of_lt hab) hbh

  by_cases hbi: b ≤ i
  · exact h1 a b hla hab hbi hbs

  have hib: i < b := Nat.succ_le_of_lt (Nat.gt_of_not_le hbi)
  by_cases hia: i + 1 ≤ a
  · exact h2 a b hia hab hbh hbs

  have hai: a < i + 1 := by exact Nat.gt_of_not_le hia

  exact hrel a has hla hah p hps hlp hph b hbs hlb hbh
    (hp ▸ (ha a has hla hai))
    (hp ▸ (hb b hbs hib (Nat.lt_add_one_of_le hbh)))

theorem glue_with_middle
    (i : Nat)
    (his: i < as.size) {r: α → α → Prop}
    (ha : IForAllIco (r · (as[i]'his)) low i as)
    (hb : IForAllIco (r (as[i]'his) ·) (i + 1) (high + 1) as)
    (hrel : ITrans r low high as)
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
    · exact hrel a has hla hah i his hli hih b hbs hlb hbh (ha hai') (hb hib')
    · have hib: i = b := by exact Nat.le_antisymm hib (Nat.le_of_not_lt hib')
      subst b
      exact (ha hai')
  · have hai: a = i := by exact Nat.le_antisymm hai (Nat.le_of_not_lt hai')
    subst a
    exact (hb hab)

theorem glue_with_middle_eq_pivot
    {r : α → α → Prop} {low high : Nat} {as : Array α}
    (i : Nat) (pivot: α)
    (his: i < as.size)
    (hpi: as[i]'his = pivot)
    (ha : as.IForAllIco (r · pivot) low i)
    (hb : as.IForAllIco (r pivot ·) (i + 1) (high + 1))
    (hrel : ITrans r low high as)
    (h1 : IPairwise r low (i - 1) as)
    (h2 : IPairwise r (i + 1) high as):
    IPairwise r low high as := by
    subst pivot
    apply glue_with_middle i
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

namespace ISortOf
instance [Trivial α (IPairwise r) ub']:
    Trivial α (λ low high as ↦ ISortOf r low high as as) ub' where
  trivial hhl := by
    constructor
    case perm => exact IPerm.refl
    case ord => exact trivial hhl

def trivial {high low: Nat} (hhl: high ≤ low): ISortOf r low high as as :=
  instTrivialOfIPairwise.trivial hhl

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
  case ord => exact restrict_out_of_bounds h.ord hsh
end ISortOf


mutual
  theorem qsort.sort_sort_sorts (f: α → α → Bool) (r: α → α → Prop) (low high : Nat) (pivot : α) (i : Nat) (as: Array α)
      (hlh: low < high) (hli : low ≤ i) (hih : i ≤ high) (hhs : high < as.size)
      (hpi: as[i]'(Nat.lt_of_le_of_lt hih hhs) = pivot)
      (ha: IForAllIco (r · pivot) low (i + 1) as)
      (hb: IForAllIco (r pivot ·) (i + 1) (high + 1) as)
      (hrel: ITransCompatCB f r low high as):
      have ⟨as', hs'⟩ := qsort.sort f as low (i - 1) (λ _ ↦ Nat.lt_of_le_of_lt (Nat.sub_le i 1) (Nat.lt_of_le_of_lt hih hhs))
      ISortOf r low high as (qsort.sort f as' (i + 1) high (λ _ ↦ hs' ▸ hhs)) := by
    have his := Nat.lt_of_le_of_lt hih hhs
    have h1ih: i - 1 ≤ high := Nat.le_trans (Nat.sub_le i 1) hih
    have h1is: i - 1 < as.size := Nat.lt_of_le_of_lt h1ih hhs

    have h1 := by
      apply qsort.sort_sorts as f r low (i - 1) (λ _ ↦ h1is) ?_
      apply restrict hrel (Nat.le_refl low) h1ih

    let ahs' := qsort.sort f as low (i - 1) (λ _ ↦ h1is)
    let as' := ahs'.1
    let hs' := ahs'.2
    have his': i < as'.size := Nat.lt_of_lt_of_eq his hs'.symm
    have h2 := by
      apply qsort.sort_sorts as' f r (i + 1) high (λ _ ↦ hs' ▸ hhs) ?_
      apply transport_higher ?_ h1.perm (Nat.sub_lt_succ i 1)
      exact restrict hrel (Nat.le_succ_of_le hli) (Nat.le_refl high)

    apply ISortOf.mk
    case perm =>
      apply IPerm.trans
      · apply IPerm.expand (Nat.le_refl _) h1ih h1.perm
      · apply IPerm.expand (Nat.le_add_right_of_le hli) (Nat.le_refl _) h2.perm

    case ord =>
      apply IPairwise.glue_with_middle_eq_pivot
      case i => exact i
      case his => simpa [qsort.size_sort]
      case pivot => exact pivot

      case hrel =>
        apply transport_enclosing ?_ h2.perm (Nat.le_add_right_of_le hli) (Nat.le_refl high)
        exact transport_enclosing hrel.trans h1.perm (Nat.le_refl _) h1ih

      case ha =>
        apply restrict ?_ (Nat.le_refl low) (Nat.le_add_right i 1)
        apply transport_lower ?_ h2.perm (Nat.le_refl (i + 1))
        exact transport_enclosing ha h1.perm (Nat.le_refl low) (Nat.sub_lt_succ i 1)

      case hb =>
        apply transport_exact_ico ?_ h2.perm
        exact transport_higher hb h1.perm (Nat.sub_lt_succ i 1)

      case hpi =>
        subst pivot
        by_cases h0i: 0 < i
        · rw [h1.perm.getElem_higher (Nat.sub_one_lt_of_lt h0i)]
          rw [h2.perm.getElem_lower (Nat.le_refl i.succ)]
          exact his'
        · -- degenerate case when i - 1 saturates, unfortunately have to handle it explicitly
          have h0i: i = 0 := Nat.eq_zero_of_not_pos h0i
          subst i
          have: low = 0 := Nat.eq_zero_of_le_zero hli
          subst low
          simp only [Nat.le_refl, h1.perm.eq_of_trivial]
          rw [h2.perm.getElem_lower]
          exact Nat.one_pos

      case h1 =>
        apply transport_lower h1.ord h2.perm (Nat.sub_lt_succ i 1)

      case h2 =>
        exact h2.ord

      termination_by (high - low, 0, 0)

  theorem qsort.sort_loop_sorts (f: α → α → Bool) (r: α → α → Prop) (low high : Nat) (hlh: low < high) (as: Array α)
      (i j : Nat)
      (hli : low ≤ i) (hij : i ≤ j) (hjh : j ≤ high) (hhs : high < as.size) (hph: as[high]'hhs = pivot)
      (ha: IForAllIco (r · pivot) low i as)
      (hb: IForAllIco (r pivot ·) i j as)
      (hrel: ITransCompatCB f r low high as):
      ISortOf r low high as (qsort.sort.loop f low high hlh pivot as i j hli hij hjh hhs) := by
    unfold qsort.sort.loop

    have hjs: j < as.size := Nat.lt_of_le_of_lt hjh hhs
    have his: i < as.size := Nat.lt_of_le_of_lt hij hjs
    have hih: i ≤ high := Nat.le_trans hij hjh
    have hlj: low ≤ j := Nat.le_trans hli hij

    by_cases hjh': j < high
    all_goals simp only [hjh', ↓reduceDIte]

    case pos =>
      have hjs: j < as.size := Nat.lt_trans hjh' hhs
      by_cases hjp: f (as[j]'hjs) pivot = true
      all_goals simp only [hjp, Bool.false_eq_true, ↓reduceIte]

      case pos =>
        have hrjp := hrel.compat j hjs hlj hjh high hhs (Nat.le_trans hli hih) (Nat.le_refl high) (.pos (hph ▸ hjp))
        apply ISortOf.trans
        case hp =>
          exact .swap as i his hli hih j hjs hlj hjh
        case hs =>
          apply qsort.sort_loop_sorts
          case hph => simpa only [getElem_after_swap _ hij hjh' hhs]
          case ha => exact ha.swap_left hij (hph ▸ hrjp)
          case hb => exact hb.swap_right hij hjs
          case hrel => exact transport_exact_icc hrel (IPerm.swap _ _ _ hli hih _ _ hlj hjh)

      case neg =>
        have hrjp := hrel.compat high hhs (Nat.le_trans hli hih) (Nat.le_refl high) j hjs hlj hjh (.neg (hph ▸ hjp))
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
            exact hph ▸ hrjp

        case hrel => exact hrel

    case neg =>
      have hjh: j = high := Nat.le_antisymm hjh (Nat.le_of_not_lt hjh')
      subst j
      apply ISortOf.trans
      case hp =>
        exact IPerm.swap as i his hli hih high hhs (Nat.le_of_lt hlh) (Nat.le_refl _)

      case hs =>
        apply qsort.sort_sort_sorts
        case hli => exact hli
        case hih => exact hih
        case hlh => exact hlh
        case hhs => simpa [size_swap]

        case ha =>
          have hrpp := hrel.compat
            high hhs (Nat.le_trans hli hih) (Nat.le_refl high)
            high hhs (Nat.le_trans hli hih) (Nat.le_refl high)
            (Completion.refl (r := (f · ·)) (as[high]'hhs))
          exact (hph ▸ ha).swap_left hij hrpp

        case hb =>
          exact (hph ▸ hb).swap_right hij hhs

        case hrel =>
          exact transport_exact_icc hrel (IPerm.swap _ _ _ hli hih _ _ hlj hjh)

        case hpi =>
          simp only [swap_def, get_eq_getElem, getElem_set, getElem_set_eq, ite_eq_right_iff, ↓reduceIte]
          intro h
          simp only [h]
    termination_by (high - low, 1, high - j)

  theorem qsort.sort_loop_pivot_swap_sorts (f: α → α → Bool) (low high : Nat) (hlh: low < high) (as: Array α)
      (mid: Nat) (hlm: low ≤ mid) (hmh: mid < high) (hhs : high < as.size)
      (hrel: ITransCompatCB f r low high as):

      let as' := if f (as[mid]'(Nat.lt_trans hmh hhs)) (as[high]'hhs) then as.swap ⟨mid, Nat.lt_trans hmh hhs⟩ ⟨high, hhs⟩ else as
      have hs': as'.size = as.size := by dsimp only [as']; split; all_goals simp_all only [Array.size_swap]

      ISortOf r low high as (qsort.sort.loop f low high hlh (as'[high]'(hs' ▸ hhs)) as' low low
        (Nat.le_refl low) (Nat.le_refl low) (Nat.le_trans hlm (Nat.le_of_lt hmh)) (hs' ▸ hhs)).1 := by
    have hms := Nat.lt_trans hmh hhs
    have hlh := Nat.le_trans hlm (Nat.le_of_lt hmh)

    apply ISortOf.trans

    case hs =>
      apply qsort.sort_loop_sorts
      case hph => rfl
      case hrel =>
        apply transport_enclosing hrel ?_ (Nat.le_refl _) (Nat.le_refl _)
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

  theorem qsort.sort_sorts (as: Array α) (f: α → α → Bool) (r: α → α → Prop) (low := 0) (high := as.size - 1)
      (hhs: low < high → high < as.size)
      (hrel: ITransCompatCB f r low high as):
      ISortOf r low high as (qsort.sort f as low high hhs) := by
    unfold qsort.sort

    by_cases hlh: high ≤ low
    case pos =>
      simp only [ge_iff_le, hlh, ↓reduceDIte]
      exact ISortOf.trivial hlh
    case neg =>
      simp only [hlh]
      have hlh: low < high := Nat.gt_of_not_le hlh
      have hlh': low ≤ high := Nat.le_of_lt hlh

      apply ISortOf.trans
      case hs =>
        apply qsort.sort_loop_pivot_swap_sorts

        case hlm => exact Nat.left_le_add_div_two.mpr hlh'
        case hmh => exact Nat.add_div_two_lt_right.mpr hlh

        case hrel =>
          apply transport_enclosing hrel ?hp (Nat.le_refl _) (Nat.le_refl _)

          case hp =>
            repeat'
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

theorem qsort_sorts_as (as: Array α) (f: α → α → Bool) (r: α → α → Prop) (low := 0) (high := as.size - 1)
    (hrel: ITransCompatCB f r low high as):
    ISortOf r low high as (qsort as f low high)  := by
  unfold qsort
  split
  case isTrue =>
    apply qsort.sort_sorts
    · exact hrel
  case isFalse h =>
    have hsh: as.size - 1 ≤ high := by
      apply Nat.sub_le_of_le_add
      exact Nat.le_add_right_of_le (Nat.le_of_not_lt h)
    apply ISortOf.resize_out_of_bounds
    · apply qsort.sort_sorts
      case hrel => exact restrict hrel (Nat.le_refl _) hsh
    · simp only [qsort.size_sort, Nat.le_refl]
    · exact hsh

theorem iTransCompat_of_trans_total (f: α → α → Bool)
    (trans: ∀ {x y z}, f x y → f y z → f x z) (total: ∀ {x y}, f x y ∨ f y x):
  ITransCompatCB (f · ·) (f · · = true) low high as := by
  constructor
  case left =>
    intro i his _ _ j hjs _ _ h
    cases h
    case inl h =>
      exact h
    case inr h =>
      apply Or.resolve_right
      apply total
      exact h
  case right =>
    intro i his _ _ j hjs _ _ k hks _ _ hxy hyz
    apply trans hxy hyz

theorem iTransCompat_of_wlinear_asymm (f: α → α → Bool)
    (wlinear: ∀ {x y z}, f x z → f x y ∨ f y z) (asymm: ∀ {x y}, f x y → ¬f y x):
  ITransCompatCB (f · ·) (λ x y ↦ f y x = false) low high as := by
  constructor
  case left =>
    intro i his _ _ j hjs _ _ h
    cases h
    case inl h =>
      apply eq_false_of_ne_true
      apply asymm
      exact h
    case inr h =>
      apply eq_false_of_ne_true
      exact h
  case right =>
    intro i his _ _ j hjs _ _ k hks _ _ hxy hyz
    apply eq_false_of_ne_true
    intro hki
    apply not_or_intro (ne_true_of_eq_false hyz) (ne_true_of_eq_false hxy)
    apply wlinear
    exact hki

/--
We prove that qsort produces an array that:
- Is a permutation of the input (generated by the input by a finite sequence of swaps)
- Is ordered according to the transitive completion of the total completion of f

The latter means that for any indices i0 < i1 in the range, there is a chain i0 ≤~ k_0 ≤~ ... ≤~ k_n ≤~ i1
of indices in range, where i ≤~ j means that f(as[i], as[j]) = true or f(as[j], as[i]) = false.

If f corresponds to a ≤ or < function on a totally ordered type, this simplifies to i < j → as[i] ≤ as[j].
See [qsort_sorts_of_is_le] or [qsort_sorts_of_is_lt] for this special case.
--/
theorem qsort_sorts (as: Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1):
    ISortOf (ITransGen (Completion (f · ·)) low high as) low high as (qsort as f low high)  := by
  apply qsort_sorts_as
  exact ITransCompat.mkITransGen

/--
If f is a lawful ≤, i.e. a total order, meaning a transitive total relation, qsort sorts according to f:
- The output is a permutation of the input
- If i < j, then f (qsort as f _ _)[i] ≤ f (qsort as f _ _)[j]
--/
theorem qsort_sorts_of_is_le (as: Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1)
    (trans: ∀ {x y z}, f x y → f y z → f x z) (total: ∀ {x y}, f x y ∨ f y x):
    ISortOf (f · ·) low high as (qsort as f low high)  := by
  apply qsort_sorts_as
  exact iTransCompat_of_trans_total f trans total

/--
If f is a lawful <, i.e. a strict total order, meaning a weakly linear asymmetric relation, qsort sorts according to f:
- The output is a permutation of the input
- If i < j, then ¬ f (qsort as f _ _)[j] < f (qsort as f _ _)[i]
--/
theorem qsort_sorts_of_is_lt (as: Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1)
    (wlinear: ∀ {x y z}, f x z → f x y ∨ f y z) (asymm: ∀ {x y}, f x y → ¬f y x):
    ISortOf (λ x y ↦ f y x = false) low high as (qsort as f low high)  := by
  apply qsort_sorts_as
  exact iTransCompat_of_wlinear_asymm f wlinear asymm

end Array
