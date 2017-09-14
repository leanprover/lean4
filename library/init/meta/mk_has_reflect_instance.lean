/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Helper tactic for constructing a has_reflect instance.
-/
prelude
import init.meta.rec_util

namespace tactic
open expr environment list

/- Retrieve the name of the type we are building a has_reflect instance for. -/
private meta def get_has_reflect_type_name : tactic name :=
do {
  (app (const n ls) t) ← target,
  when (n ≠ `has_reflect) failed,
  (const I ls) ← return (get_app_fn t),
  return I }
<|>
fail "mk_has_reflect_instance tactic failed, target type is expected to be of the form (has_reflect ...)"

/- Try to synthesize constructor argument using type class resolution -/
private meta def mk_has_reflect_instance_for (a : expr) : tactic expr :=
do t    ← infer_type a,
   do {
     m    ← mk_app `reflected [a],
     inst ← mk_instance m
     <|> do {
       f ← pp t,
       fail (to_fmt "mk_has_reflect_instance failed, failed to generate instance for" ++ format.nest 2 (format.line ++ f))
     },
     mk_app `reflect [a, inst] }

/- Synthesize (recursive) instances of `reflected` for all fields -/
private meta def mk_reflect : name → name → list name → nat → tactic (list expr)
| I_name F_name []              num_rec := return []
| I_name F_name (fname::fnames) num_rec := do
  field ← get_local fname,
  rec   ← is_type_app_of field I_name,
  quote    ← if rec then mk_brec_on_rec_value F_name num_rec else mk_has_reflect_instance_for field,
  quotes   ← mk_reflect I_name F_name fnames (if rec then num_rec + 1 else num_rec),
  return (quote :: quotes)

/- Solve the subgoal for constructor `F_name` -/
private meta def has_reflect_case (I_name F_name : name) (field_names : list name) : tactic unit :=
do field_quotes ← mk_reflect I_name F_name field_names 0,
   -- fn should be of the form `F_name ps fs`, where ps are the inductive parameter arguments,
   -- and `fs.length = field_names.length`
   `(reflected %%fn) ← target,
   -- `reflected (F_name ps)` should be synthesizable directly, using instances from the context
   let fn := field_names.foldl (λ fn _, expr.app_fn fn) fn,
   quote ← mk_app `reflected [fn] >>= mk_instance,
   -- now extend to an instance of `reflected (F_name ps fs)`
   quote ← field_quotes.mfoldl (λ quote fquote, to_expr ``(reflected.subst %%quote %%fquote)) quote,
   exact quote

private meta def for_each_has_reflect_goal : name → name → list (list name) → tactic unit
| I_name F_name [] := done <|> fail "mk_has_reflect_instance failed, unexpected number of cases"
| I_name F_name (ns::nss) := do
  solve1 (has_reflect_case I_name F_name ns),
  for_each_has_reflect_goal I_name F_name nss

/-- Solves a goal of the form `has_reflect α` where α is an inductive type.
    Needs to synthesize a `reflected` instance for each inductive parameter type of α
    and for each constructor parameter of α. -/
meta def mk_has_reflect_instance : tactic unit :=
do I_name ← get_has_reflect_type_name,
   env ← get_env,
   v_name : name ← return `_v,
   F_name : name ← return `_F,
   guard (env.inductive_num_indices I_name = 0) <|>
     fail "mk_has_reflect_instance failed, indexed families are currently not supported",
   -- Use brec_on if type is recursive.
   -- We store the functional in the variable F.
   if is_recursive env I_name
   then intro `_v >>= (λ x, induction x [v_name, F_name] (some $ I_name <.> "brec_on") >> return ())
   else intro v_name >> return (),
   arg_names : list (list name) ← mk_constructors_arg_names I_name `_p,
   get_local v_name >>= λ v, cases v (join arg_names),
   for_each_has_reflect_goal I_name F_name arg_names

end tactic
