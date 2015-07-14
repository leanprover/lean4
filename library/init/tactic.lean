/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

This is just a trick to embed the 'tactic language' as a Lean
expression. We should view 'tactic' as automation that when execute
produces a term.  tactic.builtin is just a "dummy" for creating the
definitions that are actually implemented in C++
-/
prelude
import init.datatypes init.reserved_notation init.num

inductive tactic :
Type := builtin : tactic

namespace tactic
-- Remark the following names are not arbitrary, the tactic module
-- uses them when converting Lean expressions into actual tactic objects.
-- The bultin 'by' construct triggers the process of converting a
-- a term of type 'tactic' into a tactic that sythesizes a term
definition and_then    (t1 t2 : tactic) : tactic := builtin
definition or_else     (t1 t2 : tactic) : tactic := builtin
definition append      (t1 t2 : tactic) : tactic := builtin
definition interleave  (t1 t2 : tactic) : tactic := builtin
definition par         (t1 t2 : tactic) : tactic := builtin
definition fixpoint    (f : tactic → tactic) : tactic := builtin
definition repeat      (t : tactic) : tactic := builtin
definition at_most     (t : tactic) (k : num)  : tactic := builtin
definition discard     (t : tactic) (k : num)  : tactic := builtin
definition focus_at    (t : tactic) (i : num)  : tactic := builtin
definition try_for     (t : tactic) (ms : num) : tactic := builtin
definition all_goals   (t : tactic) : tactic := builtin
definition now         : tactic := builtin
definition assumption  : tactic := builtin
definition eassumption : tactic := builtin
definition state       : tactic := builtin
definition fail        : tactic := builtin
definition id          : tactic := builtin
definition beta        : tactic := builtin
definition info        : tactic := builtin
definition whnf        : tactic := builtin
definition contradiction : tactic := builtin
definition exfalso     : tactic := builtin
definition congruence  : tactic := builtin
definition rotate_left (k : num) := builtin
definition rotate_right (k : num) := builtin
definition rotate (k : num) := rotate_left k

-- This is just a trick to embed expressions into tactics.
-- The nested expressions are "raw". They tactic should
-- elaborate them when it is executed.
inductive expr : Type :=
builtin : expr

inductive expr_list : Type :=
| nil  : expr_list
| cons : expr → expr_list → expr_list

-- auxiliary type used to mark optional list of arguments
definition opt_expr_list := expr_list

-- auxiliary types used to mark that the expression is suppose to be an identifier, optional, or a list.
definition identifier := expr
definition identifier_list := expr_list
definition opt_identifier_list := expr_list

-- Marker for instructing the parser to parse it as '?(using <expr>)'
definition using_expr := expr
-- Constant used to denote the case were no expression was provided
definition none_expr : expr := expr.builtin

definition apply      (e : expr)         : tactic := builtin
definition eapply     (e : expr)         : tactic := builtin
definition fapply     (e : expr)         : tactic := builtin
definition rename     (a b : identifier) : tactic := builtin
definition intro      (e : identifier_list) : tactic := builtin
definition generalize_tac (e : expr) (id : identifier) : tactic := builtin
definition clear      (e : identifier_list) : tactic := builtin
definition revert     (e : identifier_list) : tactic := builtin
definition refine     (e : expr)         : tactic := builtin
definition exact      (e : expr)         : tactic := builtin
-- Relaxed version of exact that does not enforce goal type
definition rexact     (e : expr)         : tactic := builtin
definition check_expr (e : expr)         : tactic := builtin
definition trace      (s : string)       : tactic := builtin

-- rewrite_tac is just a marker for the builtin 'rewrite' notation
-- used to create instances of this tactic.
definition rewrite_tac  (e : expr_list) : tactic := builtin
definition xrewrite_tac (e : expr_list) : tactic := builtin
definition krewrite_tac (e : expr_list) : tactic := builtin

-- simp_tac is just a marker for the builtin 'simp' notation
-- used to create instances of this tactic.
-- Arguments:
--  - e : additional rewrites to be considered
--  - n : add rewrites from the give namespaces
--  - x : exclude the give global rewrites
--  - t : tactic for discharging conditions
--  - l : location
definition simp_tac (e : expr_list) (n : identifier_list) (x : identifier_list) (t : option tactic) (l : expr) : tactic := builtin

-- with_options_tac is just a marker for the builtin 'with_options' notation
definition with_options_tac (o : expr) (t : tactic) : tactic := builtin

definition cases (h : expr) (ids : opt_identifier_list) : tactic := builtin

definition induction (h : expr) (rec : using_expr) (ids : opt_identifier_list) : tactic := builtin

definition intros (ids : opt_identifier_list) : tactic := builtin

definition generalizes (es : expr_list) : tactic := builtin

definition clears  (ids : identifier_list) : tactic := builtin

definition reverts (ids : identifier_list) : tactic := builtin

definition change (e : expr) : tactic := builtin

definition assert_hypothesis (id : identifier) (e : expr) : tactic := builtin

definition lettac (id : identifier) (e : expr) : tactic := builtin

definition constructor (k : option num)  : tactic := builtin
definition fconstructor (k : option num) : tactic := builtin
definition existsi (e : expr)            : tactic := builtin
definition split                         : tactic := builtin
definition left                          : tactic := builtin
definition right                         : tactic := builtin

definition injection (e : expr) (ids : opt_identifier_list) : tactic := builtin

definition subst (ids : identifier_list) : tactic := builtin
definition substvars : tactic := builtin

definition reflexivity             : tactic := builtin
definition symmetry                : tactic := builtin
definition transitivity (e : expr) : tactic := builtin

definition try         (t : tactic) : tactic := or_else t id
definition repeat1     (t : tactic) : tactic := and_then t (repeat t)
definition focus       (t : tactic) : tactic := focus_at t 0
definition determ      (t : tactic) : tactic := at_most t 1
definition trivial                  : tactic := or_else (or_else (apply eq.refl) (apply true.intro)) assumption
definition do (n : num) (t : tactic) : tactic :=
nat.rec id (λn t', and_then t t') (nat.of_num n)
end tactic
tactic_infixl `;`:15 := tactic.and_then
tactic_notation `(` h `|` r:(foldl `|` (e r, tactic.or_else r e) h) `)` := r
