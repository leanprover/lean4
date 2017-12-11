/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic

/- Return target after instantiating metavars and whnf -/
private meta def target' : tactic expr :=
target >>= instantiate_mvars >>= whnf

meta def get_constructors_for (e : expr) : tactic (list name) :=
do env ← get_env,
   I   ← return e.extract_opt_auto_param.get_app_fn.const_name,
   when (¬env.is_inductive I) (fail "constructor tactic failed, target is not an inductive datatype"),
   return $ env.constructors_of I

private meta def try_constructors (cfg : apply_cfg): list name → tactic (list (name × expr))
| []      := fail "constructor tactic failed, none of the constructors is applicable"
| (c::cs) := (mk_const c >>= λ e, apply e cfg) <|> try_constructors cs

meta def constructor (cfg : apply_cfg := {}): tactic (list (name × expr)) :=
target' >>= get_constructors_for >>= try_constructors cfg

meta def econstructor : tactic (list (name × expr)) :=
constructor {new_goals := new_goals.non_dep_only}

meta def fconstructor : tactic (list (name × expr)) :=
constructor {new_goals := new_goals.all}

meta def left : tactic (list (name × expr)) :=
do tgt ← target',
   [c₁, c₂] ← get_constructors_for tgt | fail "left tactic failed, target is not an inductive datatype with two constructors",
   mk_const c₁ >>= apply

meta def right : tactic (list (name × expr)) :=
do tgt ← target',
   [c₁, c₂] ← get_constructors_for tgt | fail "left tactic failed, target is not an inductive datatype with two constructors",
   mk_const c₂ >>= apply

meta def constructor_idx (idx : nat) : tactic (list (name × expr)) :=
do cs     ← target' >>= get_constructors_for,
   some c ← return $ cs.nth (idx - 1) | fail "constructor_idx tactic failed, target is an inductive datatype, but it does not have sufficient constructors",
   mk_const c >>= apply

meta def split : tactic (list (name × expr)) :=
do [c] ← target' >>= get_constructors_for | fail "split tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= apply

open expr

private meta def apply_num_metavars : expr → expr → nat → tactic expr
| f ftype 0     := return f
| f ftype (n+1) := do
  pi m bi d b ← whnf ftype,
  a          ← mk_meta_var d,
  new_f      ← return $ f a,
  new_ftype  ← return $ b.instantiate_var a,
  apply_num_metavars new_f new_ftype n

meta def existsi (e : expr) : tactic unit :=
do [c]     ← target' >>= get_constructors_for | fail "existsi tactic failed, target is not an inductive datatype with only one constructor",
   fn      ← mk_const c,
   fn_type ← infer_type fn,
   n       ← get_arity fn,
   when (n < 2) (fail "existsi tactic failed, constructor must have at least two arguments"),
   t       ← apply_num_metavars fn fn_type (n - 2),
   eapply (app t e),
   t_type  ← infer_type t >>= whnf,
   e_type  ← infer_type e,
   (guard t_type.is_pi <|> fail "existsi tactic failed, failed to infer type"),
   (unify t_type.binding_domain e_type <|> fail "existsi tactic failed, type mismatch between given term witness and expected type")

end tactic
