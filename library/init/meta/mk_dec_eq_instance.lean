/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper tactic for showing that a type has decidable equality.
-/
prelude
import init.meta.contradiction_tactic init.meta.constructor_tactic
import init.meta.injection_tactic init.meta.relation_tactics
import init.meta.rec_util init.meta.interactive

namespace tactic
open expr environment list

/- Retrieve the name of the type we are building a decidable equality proof for. -/
private meta definition get_dec_eq_type_name : tactic name :=
do {
  (pi x1 i1 d1 (pi x2 i2 d2 b)) ← target >>= whnf | failed,
  (const n ls) ← return (get_app_fn b) | failed,
  when (n ≠ `decidable) failed,
  (const I ls) ← return (get_app_fn d1) | failed,
  return I }
<|>
fail "mk_dec_eq_instance tactic failed, target type is expected to be of the form (decidable_eq ...)"

/- Extract (lhs, rhs) from a goal (decidable (lhs = rhs)) -/
private meta definition get_lhs_rhs : tactic (expr × expr) :=
do
  (app dec lhs_eq_rhs) ← target | fail "mk_dec_eq_instance failed, unexpected case",
  match_eq lhs_eq_rhs

private meta definition find_next_target : list expr → list expr → tactic (expr × expr)
| (t::ts) (r::rs) := if t = r then find_next_target ts rs else return (t, r)
| l1       l2     := failed

/- Create an inhabitant of (decidable (lhs = rhs)) -/
private meta definition mk_dec_eq_for (lhs : expr) (rhs : expr) : tactic expr :=
do lhs_type ← infer_type lhs,
   dec_type ← mk_app `decidable_eq [lhs_type] >>= whnf,
   do {
     inst : expr ← mk_instance dec_type,
     return $ app_of_list inst [lhs, rhs] }
   <|>
   do {
     f ← pp dec_type,
     fail $ to_fmt "mk_dec_eq_instance failed, failed to generate instance for" ++ format.nest 2 (format.line ++ f) }

/- Target is of the form (decidable (C ... = C ...)) where C is a constructor -/
private meta definition dec_eq_same_constructor : name → name → nat → tactic unit
| I_name F_name num_rec :=
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
    rec ← is_type_app_of lhs_arg I_name,
    inst ← if rec then do {
      inst_fn : expr ← mk_brec_on_rec_value F_name num_rec,
      return $ app inst_fn rhs_arg }
    else do {
      mk_dec_eq_for lhs_arg rhs_arg
    },
    `[apply @decidable.by_cases _ _ %%inst],
    -- discharge first (positive) case by recursion
    intro1 >>= subst >> dec_eq_same_constructor I_name F_name (if rec then num_rec + 1 else num_rec),
    -- discharge second (negative) case by contradiction
    intro1, left, -- decidable.is_false
    intro1 >>= injection,
    intros, contradiction,
    return () }

/- Easy case: target is of the form (decidable (C_1 ... = C_2 ...)) where C_1 and C_2 are distinct constructors -/
private meta definition dec_eq_diff_constructor : tactic unit :=
left >> intron 1 >> contradiction

/- This tactic is invoked for each case of decidable_eq. There n^2 cases, where n is the number
   of constructors. -/
private meta definition dec_eq_case_2 (I_name : name) (F_name : name) : tactic unit :=
do
  (lhs, rhs)       ← get_lhs_rhs,
  lhs_fn : expr    ← return $ get_app_fn lhs,
  rhs_fn : expr    ← return $ get_app_fn rhs,
  if lhs_fn = rhs_fn
  then dec_eq_same_constructor I_name F_name 0
  else dec_eq_diff_constructor

private meta definition dec_eq_case_1 (I_name : name) (F_name : name) : tactic unit :=
intro `w >>= cases >> all_goals (dec_eq_case_2 I_name F_name)

meta definition mk_dec_eq_instance : tactic unit :=
do I_name ← get_dec_eq_type_name,
   env ← get_env,
   v_name ← return `_v,
   F_name ← return `_F,
   -- Use brec_on if type is recursive.
   -- We store the functional in the variable F.
   if is_recursive env I_name
   then intro1 >>= (λ x, induction_core semireducible x (I_name <.> "brec_on") [v_name, F_name])
   else intro v_name >> return (),
   -- Apply cases to first element of type (I ...)
   get_local v_name >>= cases,
   all_goals (dec_eq_case_1 I_name F_name)

end tactic
