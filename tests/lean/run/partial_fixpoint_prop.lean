/--
Tests that `partial_fixpoint` is not picking up the partial order structure on Prop, that is exclusively used for defining (co)inductive predicates. Since `Prop` is inhabitted, `partial_fixpoint` will synthetise a `FlatOrder` instance, but in the provided example, it will not be able to prove that the recursive calls are monotone in their arguments.
-/

-- This works as `∨` is monotone in its arguments with respect to the (`ImplicationOrder`/`ReverseImplicationOrder` on `Prop`.
def f (x : Nat) : Prop :=
  f (x + 1) ∨ f ( x + 2)
  coinductive_fixpoint

def f' (x : Nat) : Prop :=
  f' (x + 1) ∨ f' ( x + 2)
  inductive_fixpoint

/--
error: Could not prove 'f''' to be monotone in its recursive calls:
  Cannot eliminate recursive call `f'' (x + 1)` enclosed in
    f'' (x + 1) ∨ f'' (x + 2)
  Tried to apply 'Lean.Order.implication_order_monotone_or' and 'Lean.Order.coind_monotone_or', but failed.
  Possible cause: A missing `Lean.Order.MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
-/
#guard_msgs in
def f'' (x : Nat) : Prop :=
  f'' (x + 1) ∨ f'' ( x + 2)
  partial_fixpoint
