/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.lemmas init.wf

namespace list

-- Note: we can't use the equation compiler here because
-- init.meta.well_founded_tactics uses this file
def qsort.F {α} (lt : α → α → bool) : Π (x : list α),
  (Π (y : list α), length y < length x → list α) → list α
| []     IH := []
| (h::t) IH := begin
    induction e : partition (λ x, lt h x = tt) t with large small,
    have : length small < length (h::t) ∧ length large < length (h::t),
    { rw partition_eq_filter_filter at e,
      injection e,
      subst large, subst small,
      constructor;
      exact nat.succ_le_succ (length_le_of_sublist (filter_sublist _)) },
    exact IH small this.left ++ h :: IH large this.right
  end

/- This is based on the minimalist Haskell "quicksort".

   Remark: this is *not* really quicksort since it doesn't partition the elements in-place -/
def qsort {α} (lt : α → α → bool) : list α → list α :=
well_founded.fix (inv_image.wf length nat.lt_wf) (qsort.F lt)

@[simp] theorem qsort_nil {α} (lt : α → α → bool) : qsort lt [] = [] :=
by rw [qsort, well_founded.fix_eq, qsort.F]

@[simp] theorem qsort_cons {α} (lt : α → α → bool) (h t) : qsort lt (h::t) =
  let (large, small) := partition (λ x, lt h x = tt) t in
  qsort lt small ++ h :: qsort lt large :=
begin
  rw [qsort, well_founded.fix_eq, qsort.F],
  induction e : partition (λ x, lt h x = tt) t with large small,
  simp [e], rw [e]
end

end list
