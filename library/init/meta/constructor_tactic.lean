/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.function

namespace tactic
open bool option list

private meta_definition get_constructors_for (e : expr) : tactic (list name) :=
do env ← get_env,
   I   ← return $ expr.const_name (expr.get_app_fn e),
   when (environment.is_inductive env I = ff) (fail "constructor tactic failed, target is not an inductive datatype"),
   return $ environment.constructors_of env I

private meta_definition try_constructors : list name → tactic unit
| []      := fail "constructor tactic failed, none of the constructors is applicable"
| (c::cs) :=
  do { mk_const c >>= apply } <|> try_constructors cs

meta_definition constructor : tactic unit :=
do tgt ← target,
   cs  ← get_constructors_for tgt,
   try_constructors cs

meta_definition left : tactic unit :=
do tgt ← target,
   cs  ← get_constructors_for tgt,
   match cs with
   | [c₁, c₂] := mk_const c₁ >>= apply
   | _        := fail "left tactic failed, target is not an inductive datatype with two constructors"
   end

meta_definition right : tactic unit :=
do tgt ← target,
   cs  ← get_constructors_for tgt,
   match cs with
   | [c₁, c₂] := mk_const c₂ >>= apply
   | _        := fail "left tactic failed, target is not an inductive datatype with two constructors"
   end

meta_definition constructor_idx (idx : nat) : tactic unit :=
do tgt ← target,
   cs  ← get_constructors_for tgt,
   match nth cs (idx - 1) with
   | some c := mk_const c >>= apply
   | none   := fail "constructor_idx tactic failed, target is an inductive datatype, but it does not have sufficient constructors"
   end

meta_definition split : tactic unit :=
do tgt ← target,
   cs  ← get_constructors_for tgt,
   match cs with
   | [c] := mk_const c >>= apply
   | _   := fail "split tactic failed, target is not an inductive datatype with only one constructor"
   end

private meta_definition apply_num_metavars : expr → expr → nat → tactic expr
| f ftype 0     := return f
| f ftype (n+1) := do
  ftype' ← whnf ftype,
  match ftype' with
  | expr.pi _ _ d b := do
    a         ← mk_meta_var d,
    new_f     ← return $ expr.app f a,
    new_ftype ← return $ expr.instantiate_var b a,
    apply_num_metavars new_f new_ftype n
  | _           := failed
  end

meta_definition existsi (e : expr) : tactic unit :=
do tgt ← target,
   cs  ← get_constructors_for tgt,
   match cs with
   | [c] := do
     fn      ← mk_const c,
     fn_type ← infer_type fn,
     n       ← get_arity fn,
     when (n < 2) (fail "existsi tactic failed, constructor must have at least two arguments"),
     t : expr ← apply_num_metavars fn fn_type (n - 2),
     apply (t e)
   | _   := fail "existsi tactic failed, target is not an inductive datatype with only one constructor"
   end

end tactic
