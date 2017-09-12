/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for constructing has_sizeof instance.
-/
prelude
import init.meta.rec_util init.meta.constructor_tactic

namespace tactic
open expr environment list

/- Retrieve the name of the type we are building a has_sizeof instance for. -/
private meta def get_has_sizeof_type_name : tactic name :=
do {
  (app (const n ls) t) ← target >>= whnf,
  when (n ≠ `has_sizeof) failed,
  (const I ls) ← return (get_app_fn t),
  return I }
<|>
fail "mk_has_sizeof_instance tactic failed, target type is expected to be of the form (has_sizeof ...)"

/- Try to synthesize constructor argument using type class resolution -/
private meta def mk_has_sizeof_instance_for (a : expr) (use_default : bool) : tactic expr :=
do t    ← infer_type a,
   do {
     m    ← mk_app `has_sizeof [t],
     inst ← mk_instance m,
     mk_app `sizeof [t, inst, a] }
   <|>
   if use_default
   then return (const `nat.zero [])
   else do
     f ← pp t,
     fail (to_fmt "mk_has_sizeof_instance failed, failed to generate instance for" ++ format.nest 2 (format.line ++ f))

private meta def mk_sizeof : bool → name → name → list name → nat → tactic (list expr)
| use_default I_name F_name []              num_rec := return []
| use_default I_name F_name (fname::fnames) num_rec := do
  field ← get_local fname,
  rec   ← is_type_app_of field I_name,
  sz    ← if rec then mk_brec_on_rec_value F_name num_rec else mk_has_sizeof_instance_for field use_default,
  szs   ← mk_sizeof use_default I_name F_name fnames (if rec then num_rec + 1 else num_rec),
  return (sz :: szs)

private meta def mk_sum : list expr → expr
| []      := app (const `nat.succ []) (const `nat.zero [])
| (e::es) := app (app (const `nat.add []) e) (mk_sum es)

private meta def has_sizeof_case (use_default : bool) (I_name F_name : name) (field_names : list name) : tactic unit :=
do szs ← mk_sizeof use_default I_name F_name field_names 0,
   exact (mk_sum szs)

private meta def for_each_has_sizeof_goal : bool → name → name → list (list name) → tactic unit
| d I_name F_name [] := done <|> fail "mk_has_sizeof_instance failed, unexpected number of cases"
| d I_name F_name (ns::nss) := do
  solve1 (has_sizeof_case d I_name F_name ns),
  for_each_has_sizeof_goal d I_name F_name nss

meta def mk_has_sizeof_instance_core (use_default : bool) : tactic unit :=
do I_name ← get_has_sizeof_type_name,
   constructor,
   env ← get_env,
   v_name : name ← return `_v,
   F_name : name ← return `_F,
   let num_indices := inductive_num_indices env I_name,
   let idx_names := list.map (λ (p : name × nat), mk_num_name p.fst p.snd)
                             (list.zip (list.repeat `idx num_indices) (list.iota num_indices)),
   -- Use brec_on if type is recursive.
   -- We store the functional in the variable F.
   if is_recursive env I_name
   then intro `_v >>= (λ x, induction x (idx_names ++ [v_name, F_name]) (some $ I_name <.> "brec_on") >> return ())
   else intro v_name >> return (),
   arg_names : list (list name) ← mk_constructors_arg_names I_name `_p,
   get_local v_name >>= λ v, cases v (join arg_names),
   for_each_has_sizeof_goal use_default I_name F_name arg_names

meta def mk_has_sizeof_instance : tactic unit :=
mk_has_sizeof_instance_core ff

end tactic
