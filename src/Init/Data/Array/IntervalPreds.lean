prelude
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas

/-!
## Predicates about intervals of arrays

This file contains objects that represent predicates holding over an interval of an array.
It is used to prove the correctness of array manipulation algorithms, and in particular sort algorithms.
-/

namespace Array.IntervalPreds

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
  exact f (as[k]'hks) ha

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

abbrev ICompat (hr:  α → α → Prop) (r:  α → α → Prop) :=
  IForAllIcc2 (λ x y ↦ hr x y → r x y)

abbrev ITransCompat (hr: α → α → Prop) (r: α → α → Prop) (low high: Nat) (as: Array α) :=
  (ICompat hr r low high as) ∧ (ITrans r low high as)

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

abbrev ITransCompatC (hr: α → α → Prop) (r: α → α → Prop) (low high: Nat) (as: Array α) :=
  ITransCompat (Completion hr) r low high as

abbrev ITransCompatCB (f: α → α → Bool) (r: α → α → Prop) (low high: Nat) (as: Array α) :=
  ITransCompatC (f · ·) r low high as

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
    (ha : IForAllIco (r · pivot) low i as)
    (hb : IForAllIco (r pivot ·) (i + 1) (high + 1) as)
    (hrel : ITrans r low high as)
    (h1 : IPairwise r low (i - 1) as)
    (h2 : IPairwise r (i + 1) high as):
    IPairwise r low high as := by
    subst pivot
    apply glue_with_middle i
    all_goals assumption

end IPairwise

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

end Array.IntervalPreds
