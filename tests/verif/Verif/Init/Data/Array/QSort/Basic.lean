module

/-!
Verifies `Array.qsort`: for an asymmetric and transitive comparator, it returns a permutation of its
input in which no element is less than an earlier one.
-/

namespace Verif.Array.QSort
variable {α : Type _}

variable (lt : α → α → Bool)

variable (asymm : ∀ a b, lt a b = true → lt b a = false)
  (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
include asymm

include trans in
public theorem qsort_spec (as : Array α) :
    (as.qsort lt).Perm as ∧
      ∀ i j (hj : j < (as.qsort lt).size) (hij : i < j),
        ¬lt (as.qsort lt)[j] ((as.qsort lt)[i]'(by omega)) = true

end Verif.Array.QSort
