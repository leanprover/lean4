/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic

private meta definition get_constructors_for (e : expr) : tactic (list name) :=
do env ← get_env,
   I   ← return $ expr.const_name (expr.get_app_fn e),
   when (environment.is_inductive env I = ff) (fail "constructor tactic failed, target is not an inductive datatype"),
   return $ environment.constructors_of env I

private meta definition try_constructors : list name → tactic unit
| []      := fail "constructor tactic failed, none of the constructors is applicable"
| (c::cs) := (mk_const c >>= apply) <|> try_constructors cs

meta definition constructor : tactic unit :=
target >>= get_constructors_for >>= try_constructors

meta definition left : tactic unit :=
do tgt ← target,
   [c₁, c₂] ← get_constructors_for tgt | fail "left tactic failed, target is not an inductive datatype with two constructors",
   mk_const c₁ >>= apply

meta definition right : tactic unit :=
do tgt ← target,
   [c₁, c₂] ← get_constructors_for tgt | fail "left tactic failed, target is not an inductive datatype with two constructors",
   mk_const c₂ >>= apply

meta definition constructor_idx (idx : nat) : tactic unit :=
do cs     ← target >>= get_constructors_for,
   some c ← return $ list.nth cs (idx - 1) | fail "constructor_idx tactic failed, target is an inductive datatype, but it does not have sufficient constructors",
   mk_const c >>= apply

meta definition split : tactic unit :=
do [c] ← target >>= get_constructors_for | fail "split tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= apply

open expr

private meta definition apply_num_metavars : expr → expr → nat → tactic expr
| f ftype 0     := return f
| f ftype (n+1) := do
  pi m bi d b ← whnf ftype | failed,
  a          ← mk_meta_var d,
  new_f      ← return $ f a,
  new_ftype  ← return $ expr.instantiate_var b a,
  apply_num_metavars new_f new_ftype n

meta definition existsi (e : expr) : tactic unit :=
do [c]     ← target >>= get_constructors_for | fail "existsi tactic failed, target is not an inductive datatype with only one constructor",
   fn      ← mk_const c,
   fn_type ← infer_type fn,
   n       ← get_arity fn,
   when (n < 2) (fail "existsi tactic failed, constructor must have at least two arguments"),
   t       ← apply_num_metavars fn fn_type (n - 2),
   apply (app t e)

end tactic
