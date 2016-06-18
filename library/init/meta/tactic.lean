/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.trace init.meta.base_tactic init.meta.environment init.meta.qexpr

meta_constant tactic_state : Type₁

namespace tactic_state
meta_constant env         : tactic_state → environment
meta_constant to_format   : tactic_state → format
/- Format expression with respect to the main goal in the tactic state.
   If the tactic state does not contain any goals, then format expression
   using an empty local context. -/
meta_constant format_expr : tactic_state → expr → format
meta_constant get_options : tactic_state → options
meta_constant set_options : tactic_state → options → tactic_state
end tactic_state

meta_definition tactic_state.has_to_format [instance] : has_to_format tactic_state :=
has_to_format.mk tactic_state.to_format

meta_definition tactic [reducible] (A : Type) := base_tactic tactic_state A

namespace tactic
open tactic_state

meta_definition get_env : tactic environment :=
do s ← read,
   return (env s)

meta_definition set_bool_option (n : name) (v : bool) : tactic unit :=
do s ← read,
   write (tactic_state.set_options s (options.set_bool (tactic_state.get_options s) n v))

meta_definition set_nat_option (n : name) (v : nat) : tactic unit :=
do s ← read,
   write (tactic_state.set_options s (options.set_nat (tactic_state.get_options s) n v))

meta_definition set_string_option (n : name) (v : string) : tactic unit :=
do s ← read,
   write (tactic_state.set_options s (options.set_string (tactic_state.get_options s) n v))

meta_definition get_decl (n : name) : tactic declaration :=
do s ← read,
   returnex (environment.get (env s) n)

meta_definition trace (s : string) : tactic unit :=
return (_root_.trace s (λ u, ()))

meta_definition trace_fmt (fmt : format) : tactic unit :=
return (_root_.trace_fmt fmt (λ u, ()))

/- Trace expression with respect to the main goal -/
meta_definition trace_expr (e : expr) : tactic unit :=
do s ← read,
   trace_fmt (format_expr s e)

meta_definition trace_state : tactic unit :=
do s ← read,
   trace_fmt (to_fmt s)

meta_definition format_expr (e : expr) : tactic format :=
do s ← read, return (tactic_state.format_expr s e)

inductive transparency :=
| all | semireducible | reducible | none

/- Return the partial term/proof constructed so far. Note that the resultant expression
   may contain variables that are not declarate in the current main goal. -/
meta_constant result        : tactic expr
/- Display the partial term/proof constructed so far. This tactic is *not* equivalent to
   do { r ← result, s ← read, return (format_expr s r) } because this one will format the result with respect
   to the current goal, and trace_result will do it with respect to the initial goal. -/
meta_constant format_result : tactic format
/- Return target type of the main goal. Fail if tactic_state does not have any goal left. -/
meta_constant target        : tactic expr
meta_constant intro         : name → tactic unit
meta_constant intron        : nat → tactic unit
meta_constant rename        : name → name → tactic unit
meta_constant clear         : name → tactic unit
meta_constant revert_lst    : list name → tactic unit
meta_constant infer_type    : expr → tactic expr
meta_constant whnf          : expr → tactic expr
meta_constant unify_core    : expr → expr → transparency → tactic unit
meta_constant get_local     : name → tactic expr
/- Return the hypothesis in the main goal. Fail if tactic_state does not have any goal left. -/
meta_constant local_context : tactic (list expr)
/-  Helper tactic for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
        rel.{l_1 l_2} : Pi (A : Type.{l_1}) (B : A -> Type.{l_2}), (Pi x : A, B x) -> (Pi x : A, B x) -> , Prop
        nat     : Type.{1}
        real    : Type.{1}
        vec.{l} : Pi (A : Type.{l}) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    then
        mk_app "rel" [f, g]
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g -/
meta_constant mk_app        : name → list expr → tactic expr
/- Similar to mk_app, but allows to specify which arguments are explicit/implicit.
   Example, given
     a b : nat
   then
     mk_mapp "ite" [some (a > b), none, none, some a, some b]
   returns the application
     @ite.{1} (a > b) (nat.decidable_gt a b) nat a b -/
meta_constant mk_mapp       : name → list (option expr) → tactic expr
meta_constant subst         : name → tactic unit
meta_constant exact         : expr → tactic unit
/- Elaborate the given quoted expression with respect to the current main goal. -/
meta_constant to_expr       : qexpr → tactic expr
/- Return true if the given expression is a type class. -/
meta_constant is_class      : expr → tactic bool
/- Try to create an instance of the given type class. -/
meta_constant mk_instance   : expr → tactic expr
/- Simplify the given expression using [defeq] lemmas.
   The resulting expression is definitionally equal to the input. -/
meta_constant defeq_simp    : expr → tactic expr
/- Change the target of the main goal.
   The input expression must be definitionally equal to the current target. -/
meta_constant change        : expr → tactic unit
/- (assert H T), adds a new goal for T, and the hypothesis (H : T := ?M) in the current goal -/
meta_constant assert        : name → expr → tactic unit
/- rotate goals to the left -/
meta_constant rotate_left   : nat → tactic unit
meta_constant get_goals     : tactic (list expr)
meta_constant set_goals     : list expr → tactic unit
/- (apply_core e t all insts), apply the expression e to the main goal,
   the unification is performed using the given transparency mode.
   If all is tt, then all unassigned meta-variables are added as new goals.
   If insts is tt, then use type class resolution to instantiate unassigned meta-variables. -/
meta_constant apply_core    : expr → transparency → bool → bool → tactic unit
/- Create a fresh meta universe variable. -/
meta_constant mk_meta_univ  : tactic level
/- Create a fresh meta-variable with the given type.
   The scope of the new meta-variable is the local context of the main goal. -/
meta_constant mk_meta_var   : expr → tactic expr
/- Return the value assigned to the given universe meta-variable.
   Fail if argument is not an universe meta-variable or if it is not assigned. -/
meta_constant get_univ_assignment : level → tactic level
/- Return the value assigned to the given meta-variable.
   Fail if argument is not a meta-variable or if it is not assigned. -/
meta_constant get_assignment : expr → tactic expr
meta_constant mk_fresh_name : tactic name
open list nat

meta_definition intros : tactic unit :=
do t ← target,
   match t with
   | expr.pi   _ _ _ _ := do intro "_", intros
   | expr.elet _ _ _ _ := do intro "_", intros
   | _                 := skip
   end

meta_definition intro_lst : list name → tactic unit
| []      := skip
| (n::ns) := do intro n, intro_lst ns

meta_definition revert (n : name) : tactic unit :=
revert_lst [n]

meta_definition clear_lst : list name → tactic unit
| []      := skip
| (n::ns) := do clear n, clear_lst ns

meta_definition unify (a b : expr) : tactic unit :=
unify_core a b transparency.semireducible

meta_definition get_local_type (n : name) : tactic expr :=
get_local n >>= infer_type

meta_definition trace_result : tactic unit :=
format_result >>= trace_fmt

open bool
/- (find_same_type t es) tries to find in es an expression with type definitionally equal to t -/
meta_definition find_same_type : expr → list expr → tactic expr
| e []         := failed
| e (H :: Hs) :=
  do t ← infer_type H,
     (unify e t >> return H) <|> find_same_type e Hs

meta_definition assumption : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     H   ← find_same_type t ctx,
     exact H }
<|> fail "assumption tactic failed"

meta_definition dsimp : tactic unit :=
target >>= defeq_simp >>= change

/- Return the number of goals that need to be solved -/
meta_definition num_goals     : tactic nat :=
do gs ← get_goals,
   return (length gs)

/- We have to provide the instance argument `[has_mod nat]` because
   mod for nat was not defined yet -/
meta_definition rotate_right (n : nat) [has_mod nat] : tactic unit :=
do ng ← num_goals,
   if ng = 0 then skip
   else rotate_left (ng - n % ng)

meta_definition rotate : nat → tactic unit :=
rotate_left

meta_definition focus (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   match gs with
   | []      := fail "focus tactic failed, there isn't any goal left to focus"
   | (g::rs) :=
     do set_goals [g],
        tac,
        gs' ← get_goals,
        match gs' with
        | [] := set_goals gs
        | _  := fail "focus tactic failed, focused goal has not been solved"
        end
   end

private meta_definition all_goals_core : tactic unit → list expr → list expr → tactic unit
| tac []        acc := set_goals acc
| tac (g :: gs) acc :=
  do set_goals [g],
     tac,
     new_gs ← get_goals,
     all_goals_core tac gs (acc ++ new_gs)

/- Apply the given tactic to all goals. -/
meta_definition all_goals (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   all_goals_core tac gs []

meta_definition when (c : Prop) [decidable c] (tac : tactic unit) : tactic unit :=
if c then tac else skip

/- Fail if there are no remaining goals. -/
meta_definition fail_if_no_goals : tactic unit :=
do n ← num_goals,
   when (n = 0) (fail "tactic failed, there are no goals to be solved")

/- Fail if there are unsolved goals. -/
meta_definition now : tactic unit :=
do n ← num_goals,
   when (n ≠ 0) (fail "now tactic failed, there are unsolved goals")

/- Swap first two goals, do nothing if tactic state does not have at least two goals. -/
meta_definition swap : tactic unit :=
do gs ← get_goals,
   match gs with
   | g₁ :: g₂ :: rs := set_goals (g₂ :: g₁ :: rs)
   | _              := skip
   end

meta_definition apply (e : expr) : tactic unit :=
apply_core e transparency.semireducible ff tt

meta_definition fapply (e : expr) : tactic unit :=
apply_core e transparency.semireducible tt tt

/- Try to solve the main goal using type class resolution. -/
meta_definition apply_instance : tactic unit :=
do tgt ← target,
   b   ← is_class tgt,
   if b = tt then mk_instance tgt >>= exact
   else fail "apply_instance tactic fail, target is not a type class"

/- Create a list of universe meta-variables of the given size. -/
meta_definition mk_num_meta_univs : nat → tactic (list level)
| 0        := return []
| (succ n) := do
  l  ← mk_meta_univ,
  ls ← mk_num_meta_univs n,
  return (l::ls)

/- Return (expr.const c [l_1, ..., l_n]) where l_i's are fresh universe meta-variables. -/
meta_definition mk_const (c : name) : tactic expr :=
do env  ← get_env,
   decl ← returnex (environment.get env c),
   num  ← return (length (declaration.univ_params decl)),
   ls   ← mk_num_meta_univs num,
   return (expr.const c ls)

/- Create a fresh universe ?u, a metavariable (?T : Type.{?u}),
   and return metavariable (?M : ?T).
   This action can be used to create a meta-variable when
   we don't know its type at creation time -/
meta_definition mk_mvar : tactic expr :=
do u ← mk_meta_univ,
   t ← mk_meta_var (expr.sort u),
   mk_meta_var t

private meta_definition get_arity_aux : expr → tactic nat
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
     l     ← return (expr.free_var m n bi d),
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_arity_aux new_b,
     return (r + 1)
| _                  := return 0

/- Compute the arity of the given function -/
meta_definition get_arity (fn : expr) : tactic nat :=
infer_type fn >>= whnf >>= get_arity_aux

end tactic
