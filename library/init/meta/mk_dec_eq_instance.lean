/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type has decidable equality.
-/
prelude
import init.meta.contradiction_tactic init.meta.constructor_tactic
import init.meta.injection_tactic init.meta.relation_tactics

namespace tactic
open expr environment list

/- Retrieve the name of the type we are building a decidable equality proof for. -/
private meta_definition get_dec_eq_type_name : tactic name :=
do {
  (pi _ _ d1 (pi _ _ d2 b)) ← target >>= whnf | failed,
  (const n _) ← return (get_app_fn b) | failed,
  when (n ≠ `decidable) failed,
  (const I _) ← return (get_app_fn d1) | failed,
  return I }
<|>
fail "mk_dec_eq_instance tactic failed, target type is expected to be of the form (decidable_eq ...)"

/- Extract (lhs, rhs) from a goal (decidable (lhs = rhs)) -/
private meta_definition get_lhs_rhs : tactic (expr × expr) :=
do
  (app dec lhs_eq_rhs) ← target | fail "mk_dec_eq_instance failed, unexpected case",
  match_eq lhs_eq_rhs

private meta_definition find_next_target : list expr → list expr → tactic (expr × expr)
| (t::ts) (r::rs) := if t = r then find_next_target ts rs else return (t, r)
| _       _       := failed

/- Create an inhabitant of (decidable (lhs = rhs)) -/
private meta_definition mk_dec_eq_for (lhs : expr) (rhs : expr) : tactic expr :=
do lhs_type ← infer_type lhs,
   dec_type ← mk_app `decidable_eq [lhs_type] >>= whnf,
   do {
     inst : expr ← mk_instance dec_type,
     return $ inst lhs rhs }
   <|>
   do {
     f ← pp dec_type,
     fail $ to_fmt "mk_dec_eq_instance failed, failed to generate instance for" ++ format.nest 2 (format.line ++ f) }

private meta_definition is_rec_arg (I_name : name) (e : expr) : tactic bool :=
do t ← infer_type e,
   return $ is_constant_of (get_app_fn t) I_name

/- Auxiliary function for using brec_on "dictionary" -/
private meta_definition mk_rec_inst_aux : expr → nat → tactic expr
| F 0     := do
   F' ← mk_app `prod.pr1 [F],
   F_type ← infer_type F' >>= whnf,
   if is_pi F_type = tt
   then return F'
   else mk_app `prod.pr1 [F']
| F (n+1) := do
  F' ← mk_app `prod.pr2 [F],
  mk_rec_inst_aux F' n

/- Use brec_on F_name (dictionary) argument to create an decidable_eq instance for (i+1)-th recursive argument. -/
private meta_definition mk_rec_inst (F_name : name) (i : nat) : tactic expr :=
do F ← get_local F_name,
   mk_rec_inst_aux F i

/- Target is of the form (decidable (C ... = C ...)) where C is a constructor -/
private meta_definition dec_eq_same_constructor (I_name : name) (F_name : name) (num_rec : nat) : tactic unit :=
do
  (lhs, rhs) ← get_lhs_rhs,
  -- Try easy case first, where the proof is just reflexivity
  (unify lhs rhs >> right >> reflexivity)
  <|>
  do {
    lhs_list : list expr ← return $ get_app_args lhs,
    rhs_list : list expr ← return $ get_app_args rhs,
    when (length lhs_list ≠ length rhs_list) (fail "mk_dec_eq_instance failed, constructor applications have different number of arguments"),
    (lhs_arg,  rhs_arg) ← find_next_target lhs_list rhs_list,
    rec ← is_rec_arg I_name lhs_arg,
    inst ← if rec = tt
    then do {
      inst_fn : expr ← mk_rec_inst F_name num_rec,
      return $ inst_fn rhs_arg }
    else do {
      mk_dec_eq_for lhs_arg rhs_arg
    },
    tgt      ← target,
    by_cases ← mk_mapp_core transparency.all `decidable.by_cases [none, some tgt, some inst],
    apply by_cases,
    -- discharge first (positive) case by recursion
    intro "_" >>= subst >> dec_eq_same_constructor I_name F_name (if rec = tt then num_rec + 1 else num_rec),
    -- discharge second (negative) case by contradiction
    intro "_", left, -- decidable.ff
    intro "_" >>= injection,
    intros, contradiction,
    return () }

/- Easy case: target is of the form (decidable (C_1 ... = C_2 ...)) where C_1 and C_2 are distinct constructors -/
private meta_definition dec_eq_diff_constructor : tactic unit :=
left >> intron 1 >> contradiction

/- This tactic is invoked for each case of decidable_eq. There n^2 cases, where n is the number
   of constructors. -/
private meta_definition dec_eq_case_2 (I_name : name) (F_name : name) : tactic unit :=
do
  (lhs, rhs)       ← get_lhs_rhs,
  lhs_fn : expr    ← return $ get_app_fn lhs,
  rhs_fn : expr    ← return $ get_app_fn rhs,
  if lhs_fn = rhs_fn
  then dec_eq_same_constructor I_name F_name 0
  else dec_eq_diff_constructor

private meta_definition dec_eq_case_1 (I_name : name) (F_name : name) : tactic unit :=
intro "w" >>= cases >> all_goals (dec_eq_case_2 I_name F_name)

meta_definition mk_dec_eq_instance : tactic unit :=
do I_name ← get_dec_eq_type_name,
   env ← get_env,
   v_name ← return ("_v" : name),
   F_name ← return ("_F" : name),
   -- Use brec_on if type is recursive.
   -- We store the functional in the variable F.
   if (is_recursive env I_name = tt)
   then intro "_" >>= (λ x, induction_core semireducible x (I_name <.> "brec_on") [v_name, F_name])
   else intro v_name >> return (),
   -- Apply cases to first element of type (I ...)
   get_local v_name >>= cases,
   all_goals (dec_eq_case_1 I_name F_name)

end tactic
