/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.base_tactic init.meta.environment init.trace

meta_constant tactic_state : Type₁

namespace tactic_state
meta_constant env         : tactic_state → environment
meta_constant to_format   : tactic_state → format
/- Format expression with respect to the main goal in the tactic state.
   If the tactic state does not contain any goals, then format expression
   using an empty local context. -/
meta_constant format_expr : tactic_state → expr → format
end tactic_state

meta_definition tactic_state.has_to_format [instance] : has_to_format tactic_state :=
has_to_format.mk tactic_state.to_format

meta_definition tactic [reducible] (A : Type) := base_tactic tactic_state A

namespace tactic
open tactic_state

meta_definition get_env : tactic environment :=
do s ← read,
   return (env s)

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
meta_constant assumption    : tactic unit
meta_constant rename        : name → name → tactic unit
meta_constant clear         : name → tactic unit
meta_constant revert_lst    : list name → tactic unit
meta_constant infer_type    : expr → tactic expr
meta_constant whnf          : expr → tactic expr
meta_constant unify_core    : expr → expr → transparency → tactic bool
meta_constant get_local     : name → tactic expr
/- Return the hypothesis in the main goal. Fail if tactic_state does not have any goal left. -/
meta_constant local_context : tactic (list expr)
/- Return the number of goals that need to be solved -/
meta_constant num_goals     : tactic nat
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

meta_definition unify (a b : expr) : tactic bool :=
unify_core a b transparency.semireducible

meta_definition get_local_type (n : name) : tactic expr :=
do e ← get_local n,
   infer_type e

meta_definition trace_result : tactic unit :=
do f ← format_result,
   trace_fmt f

end tactic
