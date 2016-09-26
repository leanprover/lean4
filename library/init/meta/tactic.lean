/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.trace init.function init.option init.monad init.alternative init.nat_div
import init.meta.exceptional init.meta.format init.meta.environment init.meta.pexpr
meta constant tactic_state : Type

namespace tactic_state
meta constant env         : tactic_state → environment
meta constant to_format   : tactic_state → format
/- Format expression with respect to the main goal in the tactic state.
   If the tactic state does not contain any goals, then format expression
   using an empty local context. -/
meta constant format_expr : tactic_state → expr → format
meta constant get_options : tactic_state → options
meta constant set_options : tactic_state → options → tactic_state
end tactic_state

meta instance : has_to_format tactic_state :=
⟨tactic_state.to_format⟩

inductive tactic_result (A : Type)
| success   : A → tactic_state → tactic_result
| exception : (unit → format) → tactic_state → tactic_result

open tactic_result

section
variables {A : Type}
variables [has_to_string A]

meta definition tactic_result_to_string : tactic_result A → string
| (success a s)   := to_string a
| (exception .A e s) := "Exception: " ++ to_string (e ())

meta instance : has_to_string (tactic_result A) :=
⟨tactic_result_to_string⟩
end

attribute [reducible]
meta definition tactic (A : Type) :=
tactic_state → tactic_result A

section
variables {A B : Type}

attribute [inline]
meta definition tactic_fmap (f : A → B) (t : tactic A) : tactic B :=
λ s, tactic_result.cases_on (t s)
  (λ a s', success (f a) s')
  (λ e s', exception B e s')

attribute [inline]
meta definition tactic_bind (t₁ : tactic A) (t₂ : A → tactic B) : tactic B :=
λ s,  tactic_result.cases_on (t₁ s)
  (λ a s', t₂ a s')
  (λ e s', exception B e s')

attribute [inline]
meta definition tactic_return (a : A) : tactic A :=
λ s, success a s

meta definition tactic_orelse {A : Type} (t₁ t₂ : tactic A) : tactic A :=
λ s, tactic_result.cases_on (t₁ s)
  success
  (λ e₁ s', tactic_result.cases_on (t₂ s)
     success
     (exception A))
end

meta instance : monad tactic :=
⟨@tactic_fmap, @tactic_return, @tactic_bind⟩

meta definition tactic.fail {A B : Type} [has_to_format B] (msg : B) : tactic A :=
λ s, exception A (λ u, to_fmt msg) s

meta definition tactic.failed {A : Type} : tactic A :=
tactic.fail "failed"

meta instance : alternative tactic :=
⟨@tactic_fmap, (λ A a s, success a s), (@fapp _ _), @tactic.failed, @tactic_orelse⟩

namespace tactic
variables {A : Type}

meta definition try (t : tactic A) : tactic unit :=
λ s, tactic_result.cases_on (t s)
 (λ a, success ())
 (λ e s', success () s)

meta definition skip : tactic unit :=
success ()

open list
meta definition foreach : list A → (A → tactic unit) → tactic unit
| []      fn := skip
| (e::es) fn := do fn e, foreach es fn

open nat
/- (repeat_at_most n t): repeat the given tactic at most n times or until t fails -/
meta definition repeat_at_most : nat → tactic unit → tactic unit
| 0        t := skip
| (succ n) t := (do t, repeat_at_most n t) <|> skip

/- (repeat_exactly n t) : execute t n times -/
meta definition repeat_exactly : nat → tactic unit → tactic unit
| 0        t := skip
| (succ n) t := do t, repeat_exactly n t

meta definition repeat : tactic unit → tactic unit :=
repeat_at_most 100000

meta definition returnex (e : exceptional A) : tactic A :=
λ s, match e with
| (exceptional.success a)       := tactic_result.success a s
| (exceptional.exception .A f) := tactic_result.exception A (λ u, f options.mk) s -- TODO(Leo): extract options from environment
end

meta definition returnopt (e : option A) : tactic A :=
λ s, match e with
| (some a) := tactic_result.success a s
| none     := tactic_result.exception A (λ u, to_fmt "failed") s
end

/- Decorate t's exceptions with msg -/
meta definition decorate_ex (msg : format) (t : tactic A) : tactic A :=
λ s, tactic_result.cases_on (t s)
  success
  (λ e, exception A (λ u, msg ++ format.nest 2 (format.line ++ e u)))

attribute [inline]
meta definition write (s' : tactic_state) : tactic unit :=
λ s, success () s'

attribute [inline]
meta definition read : tactic tactic_state :=
λ s, success s s
end tactic

meta definition tactic_format_expr (e : expr) : tactic format :=
do s ← tactic.read, return (tactic_state.format_expr s e)

class has_to_tactic_format (A : Type) :=
(to_tactic_format : A → tactic format)

meta instance : has_to_tactic_format expr :=
⟨tactic_format_expr⟩

meta definition tactic.pp {A : Type} [has_to_tactic_format A] : A → tactic format :=
has_to_tactic_format.to_tactic_format

open tactic format

meta definition list_to_tactic_format_aux {A : Type} [has_to_tactic_format A] : bool → list A → tactic format
| b  []     := return $ to_fmt ""
| b (x::xs) := do
  f₁ ← pp x,
  f₂ ← list_to_tactic_format_aux ff xs,
  return $ (if ¬ b then to_fmt "," ++ line else nil) ++ f₁ ++ f₂

meta definition list_to_tactic_format {A : Type} [has_to_tactic_format A] : list A → tactic format
| []      := return $ to_fmt "[]"
| (x::xs) := do
  f ← list_to_tactic_format_aux tt (x::xs),
  return $ to_fmt "[" ++ group (nest 1 f) ++ to_fmt "]"

meta instance {A : Type} [has_to_tactic_format A] : has_to_tactic_format (list A) :=
⟨list_to_tactic_format⟩

meta instance has_to_format_to_has_to_tactic_format (A : Type) [has_to_format A] : has_to_tactic_format A :=
⟨(λ x, return x) ∘ to_fmt⟩

namespace tactic
open tactic_state

meta definition get_env : tactic environment :=
do s ← read,
   return $ env s

meta definition get_decl (n : name) : tactic declaration :=
do s ← read,
   returnex $ environment.get (env s) n

meta definition trace {A : Type} [has_to_tactic_format A] (a : A) : tactic unit :=
do fmt ← pp a,
   return $ _root_.trace_fmt fmt (λ u, ())

meta definition trace_state : tactic unit :=
do s ← read,
   trace $ to_fmt s

inductive transparency
| all | semireducible | reducible | none

export transparency (reducible semireducible)

/- Return the partial term/proof constructed so far. Note that the resultant expression
   may contain variables that are not declarate in the current main goal. -/
meta constant result        : tactic expr
/- Display the partial term/proof constructed so far. This tactic is *not* equivalent to
   do { r ← result, s ← read, return (format_expr s r) } because this one will format the result with respect
   to the current goal, and trace_result will do it with respect to the initial goal. -/
meta constant format_result : tactic format
/- Return target type of the main goal. Fail if tactic_state does not have any goal left. -/
meta constant target        : tactic expr
meta constant intro_core    : name → tactic expr
meta constant intron        : nat → tactic unit
meta constant rename        : name → name → tactic unit
/- Clear the given local constant. The tactic fails if the given expression is not a local constant. -/
meta constant clear         : expr → tactic unit
meta constant revert_lst    : list expr → tactic nat
meta constant whnf_core     : transparency → expr → tactic expr
meta constant eta_expand    : expr → tactic expr
meta constant unify_core    : transparency → expr → expr → tactic unit
/- is_def_eq_core is similar to unify_core, but it treats metavariables as constants. -/
meta constant is_def_eq_core : transparency → expr → expr → tactic unit
/- Infer the type of the given expression.
   Remark: transparency does not affect type inference -/
meta constant infer_type    : expr → tactic expr

meta constant get_local     : name → tactic expr
/- Return the hypothesis in the main goal. Fail if tactic_state does not have any goal left. -/
meta constant local_context : tactic (list expr)
meta constant get_unused_name : name → option nat → tactic name
/-  Helper tactic for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
        rel.{l_1 l_2} : Pi (A : Type.{l_1}) (B : A -> Type.{l_2}), (Pi x : A, B x) -> (Pi x : A, B x) -> , Prop
        nat     : Type 1
        real    : Type 1
        vec.{l} : Pi (A : Type l) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    then
        mk_app_core semireducible "rel" [f, g]
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g -/
meta constant mk_app_core   : transparency → name → list expr → tactic expr
/- Similar to mk_app, but allows to specify which arguments are explicit/implicit.
   Example, given
     a b : nat
   then
     mk_mapp_core semireducible "ite" [some (a > b), none, none, some a, some b]
   returns the application
     @ite.{1} (a > b) (nat.decidable_gt a b) nat a b -/
meta constant mk_mapp_core  : transparency → name → list (option expr) → tactic expr
/- Given a local constant t, if t has type (lhs = rhs) apply susbstitution.
   Otherwise, try to find a local constant that has type of the form (t = t') or (t' = t).
   The tactic fails if the given expression is not a local constant. -/
meta constant subst         : expr → tactic unit
meta constant exact         : expr → tactic unit
/- Elaborate the given quoted expression with respect to the current main goal.
   If the boolean argument is tt, then metavariables are tolerated and
   become new goals. -/
meta constant to_expr_core  : bool → pexpr → tactic expr
/- Return true if the given expression is a type class. -/
meta constant is_class      : expr → tactic bool
/- Try to create an instance of the given type class. -/
meta constant mk_instance   : expr → tactic expr
/- Change the target of the main goal.
   The input expression must be definitionally equal to the current target. -/
meta constant change        : expr → tactic unit
/- (assert H T), adds a new goal for T, and the hypothesis (H : T) in the current goal. -/
meta constant assert        : name → expr → tactic unit
/- (assertv H T P), adds the hypothesis (H : T) in the current goal if P has type T. -/
meta constant assertv       : name → expr → expr → tactic unit
/- (define H T), adds a new goal for T, and the hypothesis (H : T := ?M) in the current goal. -/
meta constant define        : name → expr → tactic unit
/- (definev H T P), adds the hypothesis (H : T := P) in the current goal if P has type T. -/
meta constant definev       : name → expr → expr → tactic unit
/- rotate goals to the left -/
meta constant rotate_left   : nat → tactic unit
meta constant get_goals     : tactic (list expr)
meta constant set_goals     : list expr → tactic unit
/- (apply_core t all insts e), apply the expression e to the main goal,
   the unification is performed using the given transparency mode.
   If all is tt, then all unassigned meta-variables are added as new goals.
   If insts is tt, then use type class resolution to instantiate unassigned meta-variables. -/
meta constant apply_core    : transparency → bool → bool → expr → tactic unit
/- Create a fresh meta universe variable. -/
meta constant mk_meta_univ  : tactic level
/- Create a fresh meta-variable with the given type.
   The scope of the new meta-variable is the local context of the main goal. -/
meta constant mk_meta_var   : expr → tactic expr
/- Return the value assigned to the given universe meta-variable.
   Fail if argument is not an universe meta-variable or if it is not assigned. -/
meta constant get_univ_assignment : level → tactic level
/- Return the value assigned to the given meta-variable.
   Fail if argument is not a meta-variable or if it is not assigned. -/
meta constant get_assignment : expr → tactic expr
meta constant mk_fresh_name : tactic name
/- Return a hash code for expr that ignores inst_implicit arguments,
   and proofs. -/
meta constant abstract_hash : expr → tactic nat
/- Return the "weight" of the given expr while ignoring inst_implicit arguments,
   and proofs. -/
meta constant abstract_weight : expr → tactic nat
meta constant abstract_eq     : expr → expr → tactic bool
/- (induction_core m H rec ns) induction on H using recursor rec, names for the new hypotheses
   are retrieved from ns. If ns does not have sufficient names, then use the internal binder names in the recursor. -/
meta constant induction_core : transparency → expr → name → list name → tactic unit
/- (cases_core m H ns) apply cases_on recursor, names for the new hypotheses are retrieved from ns.
   H must be a local constant -/
meta constant cases_core     : transparency → expr → list name → tactic unit
/- (generalize_core m e n) -/
meta constant generalize_core : transparency → expr → name → tactic unit
/- instantiate assigned metavariables in the given expression -/
meta constant instantiate_mvars : expr → tactic expr
/- Add the given declaration to the environment -/
meta constant add_decl : declaration → tactic unit
/- (set_basic_attribute_core attr_name c_name prio) set attribute attr_name for constant c_name with the given priority.
   If the priority is none, then use default -/
meta constant set_basic_attribute_core : name → name → option nat → tactic unit
/- (unset_attribute attr_name c_name) -/
meta constant unset_attribute : name → name → tactic unit

meta definition set_basic_attribute : name → name → tactic unit :=
λ a n, set_basic_attribute_core a n none

open list nat

/- Remark: set_goals will erase any solved goal -/
meta definition cleanup : tactic unit :=
get_goals >>= set_goals

/- Auxiliary definition used to implement begin ... end blocks -/
meta definition step {A : Type} (t : tactic A) : tactic unit :=
t >> cleanup

/- Add (H : T := pr) to the current goal -/
meta definition note (n : name) (pr : expr) : tactic unit :=
do t ← infer_type pr,
   definev n t pr

meta definition whnf : expr → tactic expr :=
whnf_core semireducible

meta definition whnf_target : tactic unit :=
target >>= whnf >>= change

meta definition intro (n : name) : tactic expr :=
do t ← target,
   if expr.is_pi t ∨ expr.is_let t then intro_core n
   else whnf_target >> intro_core n

meta definition intro1 : tactic expr :=
intro `_

/- Remark: the unit argument is a trick to allow us to write a recursive definition.
   Lean3 only allows recursive functions when "equations" are used. -/
meta definition intros_core : unit → tactic (list expr)
| u  :=
   do t ← target,
   match t with
   | (expr.pi   n bi d b) := do H ← intro1, Hs ← intros_core u, return (H :: Hs)
   | (expr.elet n t v b) := do H ← intro1, Hs ← intros_core u, return (H :: Hs)
   | e                   := return []
   end

meta definition intros : tactic (list expr) :=
intros_core ()

meta definition intro_lst : list name → tactic (list expr)
| []      := return []
| (n::ns) := do H ← intro n, Hs ← intro_lst ns, return (H :: Hs)

meta definition mk_app : name → list expr → tactic expr :=
mk_app_core semireducible

meta definition mk_mapp : name → list (option expr) → tactic expr :=
mk_mapp_core semireducible

meta definition to_expr : pexpr → tactic expr :=
to_expr_core tt

meta definition to_expr_strict : pexpr → tactic expr :=
to_expr_core ff

meta definition revert (l : expr) : tactic nat :=
revert_lst [l]

meta definition clear_lst : list name → tactic unit
| []      := skip
| (n::ns) := do H ← get_local n, clear H, clear_lst ns

meta definition unify : expr → expr → tactic unit :=
unify_core semireducible

meta definition is_def_eq : expr → expr → tactic unit :=
is_def_eq_core semireducible

meta definition match_not (e : expr) : tactic expr :=
match (expr.is_not e) with
| (some a) := return a
| none     := fail "expression is not a negation"
end

meta definition match_eq (e : expr) : tactic (expr × expr) :=
match (expr.is_eq e) with
| (some (lhs, rhs)) := return (lhs, rhs)
| none              := fail "expression is not an equality"
end

meta definition match_ne (e : expr) : tactic (expr × expr) :=
match (expr.is_ne e) with
| (some (lhs, rhs)) := return (lhs, rhs)
| none              := fail "expression is not a disequality"
end

meta definition match_heq (e : expr) : tactic (expr × expr × expr × expr) :=
do match (expr.is_heq e) with
| (some (A, lhs, B, rhs)) := return (A, lhs, B, rhs)
| none                    := fail "expression is not a heterogeneous equality"
end

meta definition match_refl_app (e : expr) : tactic (name × expr × expr) :=
do env ← get_env,
match (environment.is_refl_app env e) with
| (some (R, lhs, rhs)) := return (R, lhs, rhs)
| none                 := fail "expression is not an application of a reflexive relation"
end

meta definition get_local_type (n : name) : tactic expr :=
get_local n >>= infer_type

meta definition trace_result : tactic unit :=
format_result >>= trace

/- (find_same_type t es) tries to find in es an expression with type definitionally equal to t -/
meta definition find_same_type : expr → list expr → tactic expr
| e []         := failed
| e (H :: Hs) :=
  do t ← infer_type H,
     (unify e t >> return H) <|> find_same_type e Hs

meta definition assumption : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     H   ← find_same_type t ctx,
     exact H }
<|> fail "assumption tactic failed"

/- Swap first two goals, do nothing if tactic state does not have at least two goals. -/
meta definition swap : tactic unit :=
do gs ← get_goals,
   match gs with
   | (g₁ :: g₂ :: rs) := set_goals (g₂ :: g₁ :: rs)
   | e                := skip
   end

/- Return the number of goals that need to be solved -/
meta definition num_goals     : tactic nat :=
do gs ← get_goals,
   return (length gs)

/- We have to provide the instance argument `[has_mod nat]` because
   mod for nat was not defined yet -/
meta definition rotate_right (n : nat) [has_mod nat] : tactic unit :=
do ng ← num_goals,
   if ng = 0 then skip
   else rotate_left (ng - n % ng)

meta definition rotate : nat → tactic unit :=
rotate_left

/- first [t_1, ..., t_n] applies the first tactic that doesn't fail.
   The tactic fails if all t_i's fail. -/
meta definition first {A : Type} : list (tactic A) → tactic A
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> first ts

/- Applies the given tactic to the main goal and fails if it is not solved. -/
meta definition solve1 (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   match gs with
   | []      := fail "focus tactic failed, there isn't any goal left to focus"
   | (g::rs) :=
     do set_goals [g],
        tac,
        gs' ← get_goals,
        match gs' with
        | [] := set_goals rs
        | gs := fail "focus tactic failed, focused goal has not been solved"
        end
   end

/- solve [t_1, ... t_n] applies the first tactic that solves the main goal. -/
meta definition solve (ts : list (tactic unit)) : tactic unit :=
first $ map solve1 ts

 private meta definition focus_aux : list (tactic unit) → list expr → list expr → tactic unit
| []       gs      rs := set_goals $ gs ++ rs
| (t::ts)  (g::gs) rs := do
  set_goals [g], t, rs' ← get_goals,
  focus_aux ts gs (rs ++ rs')
| (t::ts)  []      rs := fail "focus tactic failed, insufficient number of goals"

/- focus [t_1, ..., t_n] applies t_i to the i-th goal. Fails if there are less tha n goals. -/
meta definition focus (ts : list (tactic unit)) : tactic unit :=
do gs ← get_goals, focus_aux ts gs []

private meta definition all_goals_core : tactic unit → list expr → list expr → tactic unit
| tac []        ac := set_goals ac
| tac (g :: gs) ac :=
  do set_goals [g],
     tac,
     new_gs ← get_goals,
     all_goals_core tac gs (ac ++ new_gs)

/- Apply the given tactic to all goals. -/
meta definition all_goals (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   all_goals_core tac gs []

/- LCF-style AND_THEN tactic. It applies tac1, and if succeed applies tac2 to each subgoal produced by tac1 -/
meta definition seq (tac1 : tactic unit) (tac2 : tactic unit) : tactic unit :=
do g::gs ← get_goals | failed,
   set_goals [g],
   tac1, all_goals tac2,
   gs' ← get_goals,
   set_goals (gs' ++ gs)

meta instance : has_andthen (tactic unit) :=
⟨seq⟩

/- Applies tac if c holds -/
meta definition when (c : Prop) [decidable c] (tac : tactic unit) : tactic unit :=
if c then tac else skip

meta constant is_trace_enabled_for : name → bool

/- Execute tac only if option trace.n is set to true. -/
meta definition when_tracing (n : name) (tac : tactic unit) : tactic unit :=
when (is_trace_enabled_for n = tt) tac

/- Fail if there are no remaining goals. -/
meta definition fail_if_no_goals : tactic unit :=
do n ← num_goals,
   when (n = 0) (fail "tactic failed, there are no goals to be solved")

/- Fail if there are unsolved goals. -/
meta definition now : tactic unit :=
do n ← num_goals,
   when (n ≠ 0) (fail "now tactic failed, there are unsolved goals")

meta definition apply : expr → tactic unit :=
apply_core semireducible ff tt

meta definition fapply : expr → tactic unit :=
apply_core semireducible tt tt

/- Try to solve the main goal using type class resolution. -/
meta definition apply_instance : tactic unit :=
do tgt ← target,
   b   ← is_class tgt,
   if b then mk_instance tgt >>= exact
   else fail "apply_instance tactic fail, target is not a type class"

/- Create a list of universe meta-variables of the given size. -/
meta definition mk_num_meta_univs : nat → tactic (list level)
| 0        := return []
| (succ n) := do
  l  ← mk_meta_univ,
  ls ← mk_num_meta_univs n,
  return (l::ls)

/- Return (expr.const c [l_1, ..., l_n]) where l_i's are fresh universe meta-variables. -/
meta definition mk_const (c : name) : tactic expr :=
do env  ← get_env,
   decl ← returnex (environment.get env c),
   num  ← return (length (declaration.univ_params decl)),
   ls   ← mk_num_meta_univs num,
   return (expr.const c ls)

/- Create a fresh universe ?u, a metavariable (?T : Type.{?u}),
   and return metavariable (?M : ?T).
   This action can be used to create a meta-variable when
   we don't know its type at creation time -/
meta definition mk_mvar : tactic expr :=
do u ← mk_meta_univ,
   t ← mk_meta_var (expr.sort u),
   mk_meta_var t

private meta definition get_pi_arity_aux : expr → tactic nat
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
     l     ← return (expr.local_const m n bi d),
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_pi_arity_aux new_b,
     return (r + 1)
| e                  := return 0

/- Compute the arity of the given (Pi-)type -/
meta definition get_pi_arity (type : expr) : tactic nat :=
whnf type >>= get_pi_arity_aux

/- Compute the arity of the given function -/
meta definition get_arity (fn : expr) : tactic nat :=
infer_type fn >>= get_pi_arity

meta definition triv : tactic unit := mk_const `trivial >>= exact

meta definition by_contradiction (H : name) : tactic expr :=
do tgt : expr ← target,
   (match_not tgt >> return ())
   <|>
   (mk_mapp `decidable.by_contradiction [some tgt, none] >>= apply)
   <|>
   fail "tactic by_contradiction failed, target is not a negation nor a decidable proposition (remark: when 'local attribute classical.prop_decidable [instance]' is used all propositions are decidable)",
   intro H

meta definition cases (H : expr) : tactic unit :=
cases_core semireducible H []

meta definition cases_using : expr → list name → tactic unit :=
cases_core semireducible

meta definition generalize : expr → name → tactic unit :=
generalize_core semireducible

meta definition generalizes : list expr → tactic unit
| []      := skip
| (e::es) := generalize e `x >> generalizes es

meta definition refine (e : pexpr) : tactic unit :=
do tgt : expr ← target,
   to_expr `((%%e : %%tgt)) >>= exact

meta definition expr_of_nat : nat → tactic expr
| n :=
  if n = 0 then to_expr `(0)
  else if n = 1 then to_expr `(1)
  else do
    r : expr ← expr_of_nat (n / 2),
    if n % 2 = 0 then to_expr `(bit0 %%r)
    else to_expr `(bit1 %%r)

notation `command`:max := tactic unit
end tactic
