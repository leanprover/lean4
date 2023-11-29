
-- set_option trace.Elab.definition.wf true
def foo : (n : Nat) → ∃ m, m > n
 | 0 => ⟨1, Nat.zero_lt_one⟩
 | n+1 => by
  cases foo n
  · case _ m hm => exact ⟨m+1, Nat.succ_lt_succ hm⟩
decreasing_by
  -- With the case tactic, we get the recursive
  -- call as an assumption
  solve
  | have this_is_in_the_context : ∃ m, m > n := by assumption
    -- trace_state
    cases this_is_in_the_context
    exact Nat.lt_succ_self _
  | exact Nat.lt_succ_self _


/-
[Elab.definition.wf] replaceRecApps:
      match n with
      | 0 => Exists.intro 1 Nat.zero_lt_one
      | Nat.succ n =>
        Exists.casesOn (motive := fun t => foo n = t → ∃ m, m > n + 1) (foo n)
          (fun w h h_1 => Exists.intro (w + 1) (Nat.succ_lt_succ h)) (Eq.refl (foo n))
-/
