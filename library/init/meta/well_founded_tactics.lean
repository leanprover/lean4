/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta init.data.sigma.lex init.data.nat.lemmas init.data.list.instances
import init.data.list.qsort init.data.string.instances

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/
lemma nat.lt_add_of_zero_lt_left (a b : nat) (h : 0 < b) : a < a + b :=
suffices a + 0 < a + b, by {simp at this, assumption},
by {apply nat.add_lt_add_left, assumption}

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/
lemma nat.zero_lt_one_add (a : nat) : 0 < 1 + a :=
suffices 0 < a + 1, by {simp, assumption},
nat.zero_lt_succ _

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/
lemma nat.lt_add_right (a b c : nat) : a < b → a < b + c :=
λ h, lt_of_lt_of_le h (nat.le_add_right _ _)

/- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer. -/
lemma nat.lt_add_left (a b c : nat) : a < b → a < c + b :=
λ h, lt_of_lt_of_le h (nat.le_add_left _ _)

namespace well_founded_tactics
open tactic

private meta def clear_wf_rec_goal_aux : list expr → tactic unit
| []      := return ()
| (h::hs) := clear_wf_rec_goal_aux hs >> try (guard (h.local_pp_name.is_internal || h.is_aux_decl) >> clear h)

meta def clear_internals : tactic unit :=
local_context >>= clear_wf_rec_goal_aux

meta def unfold_wf_rel : tactic unit :=
dunfold_target [``has_well_founded.r] {fail_if_unchanged := ff}

meta def is_psigma_mk : expr → tactic (expr × expr)
| `(psigma.mk %%a %%b) := return (a, b)
| _                    := failed

meta def process_lex : tactic unit → tactic unit
| tac :=
  do t ← target >>= whnf,
  if t.is_napp_of `psigma.lex 6 then
     let a := t.app_fn.app_arg in
     let b := t.app_arg in
     do (a₁, a₂) ← is_psigma_mk a,
        (b₁, b₂) ← is_psigma_mk b,
        (is_def_eq a₁ b₁ >> `[apply psigma.lex.right] >> process_lex tac)
        <|>
        (`[apply psigma.lex.left] >> tac)
  else
     tac

private meta def unfold_sizeof_measure : tactic unit :=
dunfold_target [``sizeof_measure, ``measure, ``inv_image] {fail_if_unchanged := ff}

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def collect_sizeof_lemmas (e : expr) : tactic simp_lemmas :=
e.mfold simp_lemmas.mk $ λ c d s,
  if c.is_constant then
    match c.const_name with
    | name.mk_string "sizeof" p :=
      do eqns ← get_eqn_lemmas_for tt c.const_name,
         add_simps s eqns
    | _ := return s
    end
  else
    return s

private meta def unfold_sizeof_loop : tactic unit :=
do
  dunfold_target [``sizeof, ``has_sizeof.sizeof] {fail_if_unchanged := ff},
  S ← target >>= collect_sizeof_lemmas,
  (simp_target S >> unfold_sizeof_loop)
  <|>
  try `[simp]

meta def unfold_sizeof : tactic unit :=
unfold_sizeof_measure >> unfold_sizeof_loop

/- The following section should be removed as soon as we implement the
   algebraic normalizer. -/
section simple_dec_tac
open tactic expr

private meta def collect_add_args : expr → list expr
| `(%%a + %%b) := collect_add_args a ++ collect_add_args b
| e            := [e]

private meta def mk_nat_add : list expr → tactic expr
| []      := to_expr ``(0)
| [a]     := return a
| (a::as) := do
  rs ← mk_nat_add as,
  to_expr ``(%%a + %%rs)

private meta def mk_nat_add_add : list expr → list expr → tactic expr
| [] b  := mk_nat_add b
| a  [] := mk_nat_add a
| a  b  :=
  do t ← mk_nat_add a,
     s ← mk_nat_add b,
     to_expr ``(%%t + %%s)

private meta def get_add_fn (e : expr) : expr :=
if is_napp_of e `has_add.add 4 then e.app_fn.app_fn
else e

private meta def prove_eq_by_perm (a b : expr) : tactic expr :=
(is_def_eq a b >> to_expr ``(eq.refl %%a))
<|>
perm_ac (get_add_fn a) `(nat.add_assoc) `(nat.add_comm) a b

private meta def num_small_lt (a b : expr) : bool :=
if a = b then ff
else if is_napp_of a `has_one.one 2 then tt
else if is_napp_of b `has_one.one 2 then ff
else a.lt b

private meta def sort_args (args : list expr) : list expr :=
args.qsort num_small_lt

meta def cancel_nat_add_lt : tactic unit :=
do `(%%lhs < %%rhs) ← target,
   ty ← infer_type lhs >>= whnf,
   guard (ty = `(nat)),
   let lhs_args := collect_add_args lhs,
   let rhs_args := collect_add_args rhs,
   let common   := lhs_args.bag_inter rhs_args,
   if common = [] then return ()
   else do
     let lhs_rest := lhs_args.diff common,
     let rhs_rest := rhs_args.diff common,
     new_lhs    ← mk_nat_add_add common (sort_args lhs_rest),
     new_rhs    ← mk_nat_add_add common (sort_args rhs_rest),
     lhs_pr     ← prove_eq_by_perm lhs new_lhs,
     rhs_pr     ← prove_eq_by_perm rhs new_rhs,
     target_pr  ← to_expr ``(congr (congr_arg (<) %%lhs_pr) %%rhs_pr),
     new_target ← to_expr ``(%%new_lhs < %%new_rhs),
     replace_target new_target target_pr,
     `[apply nat.add_lt_add_left] <|> `[apply nat.lt_add_of_zero_lt_left]

meta def check_target_is_value_lt : tactic unit :=
do `(%%lhs < %%rhs) ← target,
    guard lhs.is_numeral

meta def trivial_nat_lt : tactic unit :=
comp_val
<|>
`[apply nat.zero_lt_one_add]
<|>
assumption
<|>
(do check_target_is_value_lt,
    (`[apply nat.lt_add_right] >> trivial_nat_lt)
    <|>
    (`[apply nat.lt_add_left] >> trivial_nat_lt))
<|>
failed
end simple_dec_tac

meta def default_dec_tac : tactic unit :=
abstract $
do clear_internals,
   unfold_wf_rel,
   process_lex (unfold_sizeof >> cancel_nat_add_lt >> trivial_nat_lt)

end well_founded_tactics

/-- Argument for using_well_founded

  The tactic `rel_tac` has to synthesize an element of type (has_well_founded A).
  The two arguments are: a local representing the function being defined by well
  founded recursion, and a list of recursive equations.
  The equations can be used to decide which well founded relation should be used.

  The tactic `dec_tac` has to synthesize decreasing proofs.
-/
meta structure well_founded_tactics :=
(rel_tac : expr → list expr → tactic unit := λ _ _, tactic.apply_instance)
(dec_tac : tactic unit := well_founded_tactics.default_dec_tac)

meta def well_founded_tactics.default : well_founded_tactics :=
{}
