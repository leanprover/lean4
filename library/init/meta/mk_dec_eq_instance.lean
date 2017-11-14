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
private meta def get_dec_eq_type_name : tactic name :=
do {
  (pi x1 i1 d1 (pi x2 i2 d2 b)) ← target >>= whnf,
  (const n ls) ← return (get_app_fn b),
  when (n ≠ `decidable) failed,
  (const I ls) ← return (get_app_fn d1),
  return I }
<|>
fail "mk_dec_eq_instance tactic failed, target type is expected to be of the form (decidable_eq ...)"

/- Extract (lhs, rhs) from a goal (decidable (lhs = rhs)) -/
private meta def get_lhs_rhs : tactic (expr × expr) :=
do
  (app dec lhs_eq_rhs) ← target | fail "mk_dec_eq_instance failed, unexpected case",
  match_eq lhs_eq_rhs

private meta def find_next_target : list expr → list expr → tactic (expr × expr)
| (t::ts) (r::rs) := if t = r then find_next_target ts rs else return (t, r)
| l1       l2     := failed

/- Create an inhabitant of (decidable (lhs = rhs)) -/
private meta def mk_dec_eq_for (lhs : expr) (rhs : expr) : tactic expr :=
do lhs_type ← infer_type lhs,
   dec_type ← mk_app `decidable_eq [lhs_type] >>= whnf,
   do {
     inst ← mk_instance dec_type,
     return $ inst lhs rhs }
   <|>
   do {
     f ← pp dec_type,
     fail $ to_fmt "mk_dec_eq_instance failed, failed to generate instance for" ++ format.nest 2 (format.line ++ f) }

private meta def apply_eq_of_heq (h : expr) : tactic unit :=
do pr ← mk_app `eq_of_heq [h],
   ty ← infer_type pr,
   assertv `h' ty pr >> skip

/- Target is of the form (decidable (C ... = C ...)) where C is a constructor -/
private meta def dec_eq_same_constructor : name → name → nat → tactic unit
| I_name F_name num_rec :=
do
  (lhs, rhs) ← get_lhs_rhs,
  -- Try easy case first, where the proof is just reflexivity
  (unify lhs rhs >> right >> reflexivity)
  <|>
  do {
    let lhs_list := get_app_args lhs,
    let rhs_list := get_app_args rhs,
    when (length lhs_list ≠ length rhs_list) (fail "mk_dec_eq_instance failed, constructor applications have different number of arguments"),
    (lhs_arg,  rhs_arg) ← find_next_target lhs_list rhs_list,
    rec ← is_type_app_of lhs_arg I_name,
    inst ← if rec then do {
      inst_fn ← mk_brec_on_rec_value F_name num_rec,
      return $ app inst_fn rhs_arg }
    else do {
      mk_dec_eq_for lhs_arg rhs_arg
    },
    `[eapply @decidable.by_cases _ _ %%inst],
    -- discharge first (positive) case by recursion
    intro1 >>= subst >> dec_eq_same_constructor I_name F_name (if rec then num_rec + 1 else num_rec),
    -- discharge second (negative) case by contradiction
    intro1, left, -- decidable.is_false
    intro1 >>= injection,
    intros,
    contradiction <|> do {
      lc ← local_context,
      lc.mmap' (λ h, try (apply_eq_of_heq h) <|> skip),
      contradiction },
    return () }

/- Easy case: target is of the form (decidable (C_1 ... = C_2 ...)) where C_1 and C_2 are distinct constructors -/
private meta def dec_eq_diff_constructor : tactic unit :=
left >> intron 1 >> contradiction

/- This tactic is invoked for each case of decidable_eq. There n^2 cases, where n is the number
   of constructors. -/
private meta def dec_eq_case_2 (I_name : name) (F_name : name) : tactic unit :=
do
  (lhs, rhs)       ← get_lhs_rhs,
  let lhs_fn      := get_app_fn lhs,
  let rhs_fn      := get_app_fn rhs,
  if lhs_fn = rhs_fn
  then dec_eq_same_constructor I_name F_name 0
  else dec_eq_diff_constructor

private meta def dec_eq_case_1 (I_name : name) (F_name : name) : tactic unit :=
intro `w >>= cases >> all_goals (dec_eq_case_2 I_name F_name)

meta def mk_dec_eq_instance_core : tactic unit :=
do I_name ← get_dec_eq_type_name,
   env ← get_env,
   let v_name := `_v,
   let F_name := `_F,
   let num_indices := inductive_num_indices env I_name,
   let idx_names   := list.map (λ (p : name × nat), mk_num_name p.fst p.snd) (list.zip (list.repeat `idx num_indices) (list.iota num_indices)),
   -- Use brec_on if type is recursive.
   -- We store the functional in the variable F.
   if is_recursive env I_name
   then intro1 >>= (λ x, induction x (idx_names ++ [v_name, F_name]) (some $ I_name <.> "brec_on") >> return ())
   else intro v_name >> return (),
   -- Apply cases to first element of type (I ...)
   get_local v_name >>= cases,
   all_goals (dec_eq_case_1 I_name F_name)

meta def mk_dec_eq_instance : tactic unit :=
do env ← get_env,
   (pi x1 i1 d1 (pi x2 i2 d2 b)) ← target >>= whnf,
   (const I_name ls) ← return (get_app_fn d1),
   when (is_ginductive env I_name ∧ ¬ is_inductive env I_name) $
      do { d1' ← whnf d1,
           (app I_basic_const I_idx) ← return d1',
           I_idx_type ← infer_type I_idx,
           new_goal ← to_expr ``(∀ (_idx : %%I_idx_type), decidable_eq (%%I_basic_const _idx)),
           assert `_basic_dec_eq new_goal,
           swap,
           `[exact _basic_dec_eq %%I_idx],
           intro1,
           return () },
   mk_dec_eq_instance_core

meta instance binder_info.has_decidable_eq : decidable_eq binder_info :=
by mk_dec_eq_instance

@[derive_handler] meta def decidable_eq_derive_handler :=
instance_derive_handler ``decidable_eq tactic.mk_dec_eq_instance

end tactic
