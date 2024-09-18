/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Init.Data.Array.IntervalPreds
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod

namespace Array

/--
Sorts the array using QuickSort according to function f.

The function can be a ≤, a <, or in fact an arbitrary function (with weaker guarantees).

See [qsort_sorts_of_is_le], [qsort_sorts_of_is_lt], [qsort_sorts], [qsort_sorts_as] for proofs.
--/
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

open Array.IntervalPreds

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

/--
We prove that qsort produces an array that:
- Is a permutation of the input (generated by the input by a finite sequence of swaps)
- Is ordered according to r, where r is any relation that is transitive and such that f is compatible with r

f is compatible with r means that f x y → r x y and ¬f y x → r x y

See [qsort_sorts], [qsort_sorts_of_is_lt] and [qsort_sorts_of_is_le] for more specific versions.
--/
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

/--
We prove that qsort produces an array that:
- Is a permutation of the input (generated by the input by a finite sequence of swaps)
- Is ordered according to the transitive completion of the total completion of f

The latter means that for any indices i0 < i1 in the range, there is a chain i0 ≤~ k_0 ≤~ ... ≤~ k_n ≤~ i1
of indices in range, where i ≤~ j means that f(as[i], as[j]) = true or f(as[j], as[i]) = false.

If f corresponds to a ≤ or < function on a totally ordered type, this simplifies to i < j → as[i] ≤ as[j].
See [qsort_sorts_of_is_le] or [qsort_sorts_of_is_lt] for these special cases.
--/
theorem qsort_sorts (as: Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1):
    ISortOf (ITransGenCB f low high as) low high as (qsort as f low high)  := by
  apply qsort_sorts_as
  exact ITransCompat.mkITransGen

/--
If f is a lawful ≤, i.e. a total order, meaning a transitive total relation, qsort sorts according to f:
- The output is a permutation of the input
- If i < j, then f out[i] out[j]

See [qsort_sorts] for the result for arbitrary f
--/
theorem qsort_sorts_of_is_le (as: Array α) (f: α → α → Bool) (low) (high)
    (trans: ∀ {x y z}, f x y → f y z → f x z) (total: ∀ {x y}, f x y ∨ f y x):
    ISortOf (f · ·) low high as (qsort as f low high)  := by
  apply Iff.mp
  · exact ISortOf.iff_of_trans_total trans total
  · exact qsort_sorts as f low high

/--
If f is a lawful <, i.e. a strict total order, meaning a weakly linear asymmetric relation, qsort sorts according to f:
- The output is a permutation of the input
- If i < j, then ¬ f out[j] < f out[i]

See [qsort_sorts] for the result for arbitrary f
--/
theorem qsort_sorts_of_is_lt (as: Array α) (f: α → α → Bool) (low := 0) (high := as.size - 1)
    (wlinear: ∀ {x y z}, f x z → f x y ∨ f y z) (asymm: ∀ {x y}, f x y → ¬f y x):
    ISortOf (λ x y ↦ ¬(f y x)) low high as (qsort as f low high)  := by
  apply Iff.mp
  · exact ISortOf.iff_of_wlinear_asymm wlinear asymm
  · exact qsort_sorts as f low high

end Array
