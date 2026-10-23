module
import all Init.Data.Array.QSort.Basic
/-!
Tests `lia` facts proved at a case split (see `grind_lia_split_facts.lean`) when the goals created
by `apply_assumption` contain metavariables. The branch proofs are then behind delayed assignments
that `instantiateMVars` does not resolve, and the split must still find the facts they use.
-/
namespace Array
open List Vector

theorem qpartition_loop_spec₁
    (hhi : hi < n) (ilo : lo ≤ i) (ik : i ≤ k) (w : k < n) (khi : k ≤ hi)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ l, (hk₁ : lo ≤ l) → (hk₂ : l < i) → lt as[l] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i k).fst.1) (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i k).2) :
    ∀ l, (h₁ : lo ≤ l) → (h₂ : l < mid) → lt as'[l] as'[mid] := by
  fun_induction qpartition.loop with unfold qpartition.loop at w_mid w_as
  | case1
  | case2 => apply_assumption <;> grind
  | case3 => grind
