open tactic

constant f : nat → nat

noncomputable def f' (x y : nat) : nat :=
f x

/-
  Unifier should be able to solve

    ?m 0 =?= f' 0 b

  by unfolding f'

-/
noncomputable def ex1 (a b : nat) : nat :=
by do
    mvar_type ← to_expr ```(nat → nat),
    mvar1 ← mk_meta_var mvar_type,
    z     ← to_expr ```(0),
    t     ← to_expr ```(f' 0 b),
    unify (mvar1 z) t semireducible tt, -- should work, type_context should unfold (f' 0 b)
    trace mvar1,
    exact (mvar1 z)

meta def ITac := tactic unit

/-
  Unifier should be able to solve

    ?m unit =?= ITac

  by unfolding ITac
-/
meta def ex2 : Type :=
by do
    mvar_type ← to_expr ```(Type → Type),
    mvar1 ← mk_meta_var mvar_type,
    u     ← to_expr ```(unit),
    t     ← to_expr ```(ITac),
    unify (mvar1 u) t semireducible tt, -- should work, type_context should unfod ITac
    trace mvar1,
    exact (mvar1 u)
