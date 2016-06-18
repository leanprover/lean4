/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic

namespace tactic
open bool option list

private meta_definition get_constructors_for (e : expr) : tactic (list name) :=
do env ← get_env,
   I   ← return (expr.const_name (expr.get_app_fn e)),
   when (environment.is_inductive env I = ff) (fail "constructor tactic failed, target is not an inductive datatype"),
   return (environment.constructors_of env I)

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

end tactic
