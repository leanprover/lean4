/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type is inhabited.
-/
prelude
import init.meta.interactive_base
import init.meta.contradiction_tactic init.meta.constructor_tactic
import init.meta.injection_tactic init.meta.relation_tactics

namespace tactic
open expr environment list

/- Retrieve the name of the type we are building an inhabitant instance for. -/
private meta def get_inhabited_type_name : tactic name :=
do {
  (app (const n ls) t) ← target >>= whnf,
  when (n ≠ `inhabited) failed,
  (const I ls) ← return (get_app_fn t),
  return I }
<|>
fail "mk_inhabited_instance tactic failed, target type is expected to be of the form (inhabited ...)"

/- Try to synthesize constructor argument using type class resolution -/
private meta def mk_inhabited_arg : tactic unit :=
do tgt  ← target,
   inh  ← mk_app `inhabited [tgt],
   inst ← mk_instance inh,
   mk_app `inhabited.default [inst] >>= exact

private meta def try_constructors : nat → nat → tactic unit
| 0     n := failed
| (i+1) n :=
  do {constructor_idx (n - i), all_goals mk_inhabited_arg, done}
  <|>
  try_constructors i n

meta def mk_inhabited_instance : tactic unit :=
do
  I      ← get_inhabited_type_name,
  env    ← get_env,
  let n  := length (constructors_of env I),
  when (n = 0) (fail format!"mk_inhabited_instance failed, type '{I}' does not have constructors"),
  constructor,
  (try_constructors n n)
  <|>
  (fail format!"mk_inhabited_instance failed, failed to build instance using all constructors of '{I}'")

end tactic
