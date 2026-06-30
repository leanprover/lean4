/-!
Regression test: `case <ctor>` must keep working after `congr; ext _; cases _`
even though the subgoal tags produced by `apply`-family tactics now inherit
the parent tag (without appending the binder name) when only one subgoal is
left. The case-tag matcher erases macro scopes so that `case yield` still
matches tags like `e_a.yield._@._internal._hyg.0`.
-/

example {δ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (x : m (ForInStep δ))
    (f g : ForInStep δ → m (ForInStep δ))
    (h : ∀ a, f a = g a) :
    (x >>= f) = (x >>= g) := by
  congr
  ext step
  cases step
  case yield => apply h
  case done  => apply h
