example (n : nat) (h : n < 5) : n < 5 :=
begin
  revert h n, -- user provided a "bad" order, then we must sort
  intro n, intro h, exact h
end

constant p {n m : nat} : n < m → Prop

example (n m : nat) (h1 : n < 5) (h2 : p h1) : p h1 :=
begin
  revert n h2,  -- there is an extra dependency that must be reverted too
  intro n, intro h1, intro h2, exact h2
end

example (n m : nat) (h1 : n < 5) (h2 : p h1) : p h1 :=
begin
  revert n, -- there are extra dependencies that must be reverted too
  intro n, intro h1, intro h2, exact h2
end

-- set_option pp.purify_metavars false

example : let n := 5 in ∀ (m : nat) (h1 : n < 5) (h2 : p h1), p h1 :=
begin
  intros n m h1 h2,
  /-
    The goal is `?M1 : (n : ℕ := 5) (m : ℕ) (h1 : n < 5) (h2 : p h1) ⊢ p h1`
  -/
  (do g ← list.head <$> tactic.get_goals, tactic.trace g, n ← tactic.get_local `n, tactic.revert n, tactic.instantiate_mvars g >>= tactic.trace),
  /-
    The goal is now `?M1' : (m : ℕ) ⊢ let n : ℕ := 5 in ∀ (h1 : n < 5) (h2 : p h1), p h1`
    and we performed the assignment
    `?M1 := ?M1' h1 h2`
  -/
  intros n h1 h2,
  exact h2
end

constant f (g : nat → nat) (h : ∀ x, g x = x) (n m : nat) (g n = m) : n = m

example (n m : nat) (h : n = m) : n = m :=
begin
  fapply f,
  /- main goal is
     ?M1 :  (n m : ℕ) ⊢ ℕ → ℕ -/
  intro a,
  /- main goal is now
     `?M1' : (n m : ℕ) (a : ℕ) ⊢ ℕ`
     and (in Lean3) we perform the assignment
     `?M1 := fun a, ?M1'[a]` where
     `?M1'[a]` denotes a delayed abstraction.
     In Lean4, we don't have delayed abstractions anymore, and the assignment above is represented as
     `?M1 := (lctx, [a], ?M1')`
     Remark: `lctx` is the local context that contains `a` definition.
   -/
  (tactic.rotate_left 1),
  /- We moved to the second goal:
     `?M2 : (n m : ℕ) ⊢ ∀ (x : ℕ), ?M1 x = x`
     In Lean3, the goal would be
     `?M2 : (n m : ℕ) ⊢ ∀ (x : ℕ), ?M1'[x] x = x`
     In Lean4, we only substitute `?M1` when `?M1'` is fully assigned, and we can abstract `a` since we have
     `?M1 := (lctx, [a], ?M1')` -/
  intro b,
  /-
     `?M2' : (n m : ℕ) (b : ℕ) ⊢ ?M1 b = b`
      and we perform the assignment
     `?M2 := (lctx, [b], ?M2')`
  -/
  exact (eq.refl b),
  /- The `exact` tactic should produce an error in Lean4.
     Reason: the goal contains a metavariable that was partially assigned (`?M1`) by an `intro` tactic.
     Remark: this is a bizarre case, and it can only happen if the user tried to solve a goal `G1` a little bit,
     and then uses rotate to work on a goal `G2` that depends on `G1`.
     On the other hand, we don't have delayed abstractions in Lean4, and users will never see (and by confused by) them in goals.
     The error is detected at `type_context::is_def_eq`, when it finds a metavariable that is delayed assigned.
  -/
  exact n, exact m,
  exact rfl,
  exact h
end
