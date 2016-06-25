/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.trace init.function init.option
import init.meta.base_tactic init.meta.environment init.meta.qexpr

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

meta_definition tactic.format_expr (e : expr) : tactic format :=
do s ← tactic.read, return (tactic_state.format_expr s e)

structure has_to_tactic_format [class] (A : Type) :=
(to_tactic_format : A → tactic format)

meta_definition expr_has_to_tactic_format [instance] : has_to_tactic_format expr :=
has_to_tactic_format.mk tactic.format_expr

meta_definition tactic.pp {A : Type} [has_to_tactic_format A] : A → tactic format :=
has_to_tactic_format.to_tactic_format

open tactic format

meta_definition list_to_tactic_format_aux {A : Type} [has_to_tactic_format A] : bool → list A → tactic format
| _  []     := return ""
| b (x::xs) := do
  f₁ ← pp x,
  f₂ ← list_to_tactic_format_aux ff xs,
  return $ (if b = ff then "," ++ line else nil) ++ f₁ ++ f₂

meta_definition list_to_tactic_format {A : Type} [has_to_tactic_format A] : list A → tactic format
| []      := return "[]"
| (x::xs) := do
  f ← list_to_tactic_format_aux tt (x::xs),
  return $ "[" ++ group (nest 1 f) ++ "]"

meta_definition list_has_to_tactic_format [instance] {A : Type} [has_to_tactic_format A] : has_to_tactic_format (list A) :=
has_to_tactic_format.mk list_to_tactic_format

meta_definition has_to_format_to_has_to_tactic_format [instance] (A : Type) [has_to_format A] : has_to_tactic_format A :=
has_to_tactic_format.mk (return ∘ to_fmt)

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

meta_definition trace {A : Type} [has_to_tactic_format A] (a : A) : tactic unit :=
do fmt ← pp a,
   return (_root_.trace_fmt fmt (λ u, ()))

meta_definition trace_state : tactic unit :=
do s ← read,
   trace (to_fmt s)

inductive transparency :=
| all | semireducible | reducible | none

export transparency (reducible semireducible)

/- Return the partial term/proof constructed so far. Note that the resultant expression
   may contain variables that are not declarate in the current main goal. -/
meta_constant result        : tactic expr
/- Display the partial term/proof constructed so far. This tactic is *not* equivalent to
   do { r ← result, s ← read, return (format_expr s r) } because this one will format the result with respect
   to the current goal, and trace_result will do it with respect to the initial goal. -/
meta_constant format_result : tactic format
/- Return target type of the main goal. Fail if tactic_state does not have any goal left. -/
meta_constant target        : tactic expr
meta_constant intro         : name → tactic expr
meta_constant intron        : nat → tactic unit
meta_constant rename        : name → name → tactic unit
/- Clear the given local constant. The tactic fails if the given expression is not a local constant. -/
meta_constant clear         : expr → tactic unit
meta_constant revert_lst    : list expr → tactic nat
meta_constant whnf          : expr → tactic expr
meta_constant unify_core    : transparency → expr → expr → tactic unit
/- Infer the type of the given expression.
   Remark: transparency does not affect type inference -/
meta_constant infer_type    : expr → tactic expr

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
        mk_app_core semireducible "rel" [f, g]
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g -/
meta_constant mk_app_core   : transparency → name → list expr → tactic expr
/- Similar to mk_app, but allows to specify which arguments are explicit/implicit.
   Example, given
     a b : nat
   then
     mk_mapp_core semireducible "ite" [some (a > b), none, none, some a, some b]
   returns the application
     @ite.{1} (a > b) (nat.decidable_gt a b) nat a b -/
meta_constant mk_mapp_core  : transparency → name → list (option expr) → tactic expr
/- Given a local constant t, if t has type (lhs = rhs) apply susbstitution.
   Otherwise, try to find a local constant that has type of the form (t = t') or (t' = t).
   The tactic fails if the given expression is not a local constant. -/
meta_constant subst         : expr → tactic unit
meta_constant exact         : expr → tactic unit
/- Elaborate the given quoted expression with respect to the current main goal. -/
meta_constant to_expr       : qexpr → tactic expr
/- Return true if the given expression is a type class. -/
meta_constant is_class      : expr → tactic bool
/- Try to create an instance of the given type class. -/
meta_constant mk_instance   : expr → tactic expr
/- Simplify the given expression using [defeq] lemmas.
   The resulting expression is definitionally equal to the input. -/
meta_constant defeq_simp_core : transparency → expr → tactic expr
/- Simplify the given expression using [simp] and [congr] lemmas.
   The result is the simplified expression along with a proof that the new
   expression is equivalent to the old one.
   Fails if no simplifications can be performed. -/
meta_constant simplify    : expr → tactic (prod expr expr)
/- Change the target of the main goal.
   The input expression must be definitionally equal to the current target. -/
meta_constant change        : expr → tactic unit
/- (assert H T), adds a new goal for T, and the hypothesis (H : T) in the current goal. -/
meta_constant assert        : name → expr → tactic unit
/- (assertv H T P), adds the hypothesis (H : T) in the current goal if P has type T. -/
meta_constant assertv       : name → expr → expr → tactic unit
/- (define H T), adds a new goal for T, and the hypothesis (H : T := ?M) in the current goal. -/
meta_constant define        : name → expr → tactic unit
/- (definev H T P), adds the hypothesis (H : T := P) in the current goal if P has type T. -/
meta_constant definev       : name → expr → expr → tactic unit
/- rotate goals to the left -/
meta_constant rotate_left   : nat → tactic unit
meta_constant get_goals     : tactic (list expr)
meta_constant set_goals     : list expr → tactic unit
/- (apply_core t all insts e), apply the expression e to the main goal,
   the unification is performed using the given transparency mode.
   If all is tt, then all unassigned meta-variables are added as new goals.
   If insts is tt, then use type class resolution to instantiate unassigned meta-variables. -/
meta_constant apply_core    : transparency → bool → bool → expr → tactic unit
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
/- Return a hash code for expr that ignores inst_implicit arguments,
   and proofs. -/
meta_constant abstract_hash : expr → tactic nat
/- Return the "weight" of the given expr while ignoring inst_implicit arguments,
   and proofs. -/
meta_constant abstract_weight : expr → tactic nat
meta_constant abstract_eq     : expr → expr → tactic bool
open list nat

/- Add (H : T := pr) to the current goal -/
meta_definition note (n : name) (pr : expr) : tactic unit :=
do t ← infer_type pr,
   definev n t pr

meta_definition intros : tactic (list expr) :=
do t ← target,
   match t with
   | expr.pi   _ _ _ _ := do H ← intro "_", Hs ← intros, return (H :: Hs)
   | expr.elet _ _ _ _ := do H ← intro "_", Hs ← intros, return (H :: Hs)
   | _                 := return []
   end

meta_definition intro_lst : list name → tactic (list expr)
| []      := return []
| (n::ns) := do H ← intro n, Hs ← intro_lst ns, return (H :: Hs)

meta_definition mk_app : name → list expr → tactic expr :=
mk_app_core semireducible

meta_definition mk_mapp : name → list (option expr) → tactic expr :=
mk_mapp_core semireducible

meta_definition revert (l : expr) : tactic nat :=
revert_lst [l]

meta_definition clear_lst : list name → tactic unit
| []      := skip
| (n::ns) := do H ← get_local n, clear H, clear_lst ns

meta_definition unify : expr → expr → tactic unit :=
unify_core semireducible

open option
meta_definition match_eq (e : expr) : tactic (expr × expr) :=
do match expr.is_eq e with
| some (lhs, rhs) := return (lhs, rhs)
| none            := fail "expression is not an equality"
end

meta_definition match_heq (e : expr) : tactic (expr × expr × expr × expr) :=
do match expr.is_heq e with
| some (A, lhs, B, rhs) := return (A, lhs, B, rhs)
| none                  := fail "expression is not a heterogeneous equality"
end

meta_definition get_local_type (n : name) : tactic expr :=
get_local n >>= infer_type

meta_definition trace_result : tactic unit :=
format_result >>= trace

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

/- Swap first two goals, do nothing if tactic state does not have at least two goals. -/
meta_definition swap : tactic unit :=
do gs ← get_goals,
   match gs with
   | g₁ :: g₂ :: rs := set_goals (g₂ :: g₁ :: rs)
   | _              := skip
   end

-- TODO(Leo): remove unifier.conservative after we finish new elaborator
set_option unifier.conservative true

meta_definition defeq_simp : expr → tactic expr :=
defeq_simp_core reducible

meta_definition dsimp : tactic unit :=
target >>= defeq_simp >>= change

meta_definition dsimp_at (H : expr) : tactic unit :=
do num_reverted : ℕ ← revert H,
   (expr.pi n bi d b : expr) ← target | failed,
   H_simp : expr ← defeq_simp d,
   change $ expr.pi n bi H_simp b,
   intron num_reverted

-- TODO(Leo): remove unifier.conservative after we finish new elaborator
set_option unifier.conservative true

meta_definition simp : tactic unit :=
do (new_target, Heq) ← target >>= simplify,
   assert "Htarget" new_target, swap,
   ns       ← return $ (if expr.is_eq Heq ≠ none then "eq" else "iff"),
   Ht       ← get_local "Htarget",
   mk_app (ns <.> "mpr") [Heq, Ht] >>= exact

meta_definition mk_eq_simp_ext (simp_ext : expr → tactic (prod expr expr)) : tactic unit :=
do gs ← get_goals,
   match gs with
   | [g] := do tgt ← target,
               match expr.is_eq tgt with
               | option.none := fail "simplifier extension expects a goal of the form [ctx |- l = ?r]"
               | option.some (start, res) := do r ← simp_ext start,
                                                unify res (prod.pr1 r),
                                                unify g (prod.pr2 r)
               end
   | _ := fail "simplifier extension expects a goal of the form [ctx |- l = ?r]"
   end


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

/- first [t_1, ..., t_n] applies the first tactic that doesn't fail.
   The tactic fails if all t_i's fail. -/
meta_definition first : list (tactic unit) → tactic unit
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> first ts

/- Applies the given tactic to the main goal and fails if it is not solved. -/
meta_definition solve1 (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   match gs with
   | []      := fail "focus tactic failed, there isn't any goal left to focus"
   | (g::rs) :=
     do set_goals [g],
        tac,
        gs' ← get_goals,
        match gs' with
        | [] := set_goals rs
        | _  := fail "focus tactic failed, focused goal has not been solved"
        end
   end

/- solve [t_1, ... t_n] applies the first tactic that solves the main goal. -/
meta_definition solve (ts : list (tactic unit)) : tactic unit :=
first $ map solve1 ts

 private meta_definition focus_aux : list (tactic unit) → list expr → list expr → tactic unit
| []       gs      rs := set_goals $ gs ++ rs
| (t::ts)  (g::gs) rs := do
  set_goals [g], t, rs' ← get_goals,
  focus_aux ts gs (rs ++ rs')
| (t::ts)  []      rs := fail "focus tactic failed, insufficient number of goals"

/- focus [t_1, ..., t_n] applies t_i to the i-th goal. Fails if there are less tha n goals. -/
meta_definition focus (ts : list (tactic unit)) : tactic unit :=
do gs ← get_goals, focus_aux ts gs []

private meta_definition all_goals_core : tactic unit → list expr → list expr → tactic unit
| tac []        ac := set_goals ac
| tac (g :: gs) ac :=
  do set_goals [g],
     tac,
     new_gs ← get_goals,
     all_goals_core tac gs (ac ++ new_gs)

/- Apply the given tactic to all goals. -/
meta_definition all_goals (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   all_goals_core tac gs []

/- LCF-style AND_THEN tactic. It applies tac1, and if succeed applies tac2 to each subgoal produced by tac1 -/
meta_definition seq (tac1 : tactic unit) (tac2 : tactic unit) : tactic unit :=
do g::gs ← get_goals | failed,
   set_goals [g],
   tac1, all_goals tac2,
   gs' ← get_goals,
   set_goals (gs' ++ gs)

infixl `;`:1 := seq

/- Applies tac if c holds -/
meta_definition when (c : Prop) [decidable c] (tac : tactic unit) : tactic unit :=
if c then tac else skip

meta_constant is_trace_enabled_for : name → bool

/- Execute tac only if option trace.n is set to true. -/
meta_definition when_tracing (n : name) (tac : tactic unit) : tactic unit :=
when (is_trace_enabled_for n = tt) tac

/- Fail if there are no remaining goals. -/
meta_definition fail_if_no_goals : tactic unit :=
do n ← num_goals,
   when (n = 0) (fail "tactic failed, there are no goals to be solved")

/- Fail if there are unsolved goals. -/
meta_definition now : tactic unit :=
do n ← num_goals,
   when (n ≠ 0) (fail "now tactic failed, there are unsolved goals")

meta_definition apply : expr → tactic unit :=
apply_core semireducible ff tt

meta_definition fapply : expr → tactic unit :=
apply_core semireducible tt tt

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
     l     ← return (expr.local_const m n bi d),
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_arity_aux new_b,
     return (r + 1)
| _                  := return 0

/- Compute the arity of the given function -/
meta_definition get_arity (fn : expr) : tactic nat :=
infer_type fn >>= whnf >>= get_arity_aux

meta_definition triv : tactic unit := mk_const "trivial" >>= exact

end tactic
