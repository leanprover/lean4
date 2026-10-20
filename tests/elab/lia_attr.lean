/-!
# The `@[lia]` attribute supplies a small lemma set to the `lia` tactic

`lia` is `grind` restricted to the `cutsat` solver. It does not use the `@[grind]`
lemma set, but lemmas tagged with `@[lia]` are instantiated via E-matching, so `cutsat`
can see definitions such as `min`/`max`.
-/

-- `Nat.min_def`/`Nat.max_def`/`Int.min_def`/`Int.max_def` are tagged `@[lia]`, so `lia`
-- proves goals involving `min`/`max` out of the box.
example (a b : Int) : min a b ≤ max a b := by lia
example (a b : Nat) : min a b ≤ max a b := by lia
example (a b : Int) (h : a ≤ b) : max a b = b := by lia
example (a b : Nat) : min a b ≤ a := by lia

-- The `@[lia]` attribute also works on user lemmas, with the same modifiers as `@[grind]`.
-- Without a `@[lia]` lemma, `lia` treats `clamp` as opaque and cannot finish.
private def clamp (n : Int) : Int := if n ≤ 0 then 0 else n
example (n : Int) : 0 ≤ clamp n := by
  fail_if_success lia
  unfold clamp; split <;> omega

-- Tagging the defining lemma adds it to the `@[lia]` set, and now `lia` succeeds.
@[lia =] private theorem clamp_def (n : Int) : clamp n = if n ≤ 0 then 0 else n := rfl
example (n : Int) : 0 ≤ clamp n := by lia

-- The `@[grind]` lemma set stays disabled under `lia`: a `@[grind]`-only lemma is not used,
-- so `lia` cannot unfold `g`, while `grind` can.
private def g (n : Int) : Int := n + 1
@[grind =] private theorem g_def (n : Int) : g n = n + 1 := rfl
example (n : Int) : g n = n + 1 := by
  fail_if_success lia
  grind
