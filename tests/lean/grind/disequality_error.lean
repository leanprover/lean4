open Array

reset_grind_attrs%

attribute [grind] Vector.getElem_swap_of_ne

theorem qpartition_loop_spec₁ {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega)
    {ilo : lo ≤ i} {jh : j < n} {w : i ≤ j} (jhi : j ≤ hi := by omega)
    (as : Vector α n) (hpivot : pivot = as[hi])
    (q : ∀ k, (hk₁ : lo ≤ k) → (hk₂ : k < i) → lt as[k] as[hi]) (mid as')
    (w_mid : mid = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2) :
    ∀ k, (h₁ : lo ≤ k) → (h₂ : k < mid) → lt as'[k] as'[mid] := by
  sorry

/--
warning: The `grind` tactic is experimental and still under development. Avoid using it in production projects.
---
error: internal `grind` error, failed to build disequality proof for
  (lo + hi) / 2
and
  lo
-/
#guard_msgs in
example {n} (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) (w : lo ≤ hi := by omega)
    (as : Vector α n) (mid as')
    (w_mid : mid = (qpartition as lt lo hi hlo hhi).fst.1)
    (hmid : mid < n)
    (w_as : as' = (qpartition as lt lo hi hlo hhi).2) :
    ∀ i, (h₁ : lo ≤ i) → (h₂ : i < mid) → lt as'[i] as'[mid] := by
  grind [qpartition, qpartition_loop_spec₁]
