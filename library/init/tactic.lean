/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.tactic
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
opaque definition and_then    (t1 t2 : tactic) : tactic := builtin
opaque definition or_else     (t1 t2 : tactic) : tactic := builtin
opaque definition append      (t1 t2 : tactic) : tactic := builtin
opaque definition interleave  (t1 t2 : tactic) : tactic := builtin
opaque definition par         (t1 t2 : tactic) : tactic := builtin
opaque definition fixpoint    (f : tactic → tactic) : tactic := builtin
opaque definition repeat      (t : tactic) : tactic := builtin
opaque definition at_most     (t : tactic) (k : num)  : tactic := builtin
opaque definition discard     (t : tactic) (k : num)  : tactic := builtin
opaque definition focus_at    (t : tactic) (i : num)  : tactic := builtin
opaque definition try_for     (t : tactic) (ms : num) : tactic := builtin
opaque definition all_goals   (t : tactic) : tactic := builtin
opaque definition now         : tactic := builtin
opaque definition assumption  : tactic := builtin
opaque definition eassumption : tactic := builtin
opaque definition state       : tactic := builtin
opaque definition fail        : tactic := builtin
opaque definition id          : tactic := builtin
opaque definition beta        : tactic := builtin
opaque definition info        : tactic := builtin
opaque definition whnf        : tactic := builtin
opaque definition rotate_left (k : num) := builtin
opaque definition rotate_right (k : num) := builtin
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

-- auxiliary types used to mark that the expression (list) is an identifier (list)
definition identifier := expr
definition identifier_list := expr_list
definition opt_identifier_list := expr_list

opaque definition apply      (e : expr)         : tactic := builtin
opaque definition fapply     (e : expr)         : tactic := builtin
opaque definition rename     (a b : identifier) : tactic := builtin
opaque definition intro      (e : identifier_list) : tactic := builtin
opaque definition generalize (e : expr)            : tactic := builtin
opaque definition clear      (e : identifier_list) : tactic := builtin
opaque definition revert     (e : identifier_list) : tactic := builtin
opaque definition refine     (e : expr)         : tactic := builtin
opaque definition exact      (e : expr)         : tactic := builtin
-- Relaxed version of exact that does not enforce goal type
opaque definition rexact     (e : expr)         : tactic := builtin
opaque definition check_expr (e : expr)         : tactic := builtin
opaque definition trace      (s : string)       : tactic := builtin

-- rewrite_tac is just a marker for the builtin 'rewrite' notation
-- used to create instances of this tactic.
opaque definition rewrite_tac (e : expr_list) : tactic := builtin

opaque definition cases (id : identifier) (ids : opt_identifier_list) : tactic := builtin

opaque definition intros (ids : opt_identifier_list) : tactic := builtin

opaque definition generalizes (es : expr_list) : tactic := builtin

opaque definition clears  (ids : identifier_list) : tactic := builtin

opaque definition reverts (ids : identifier_list) : tactic := builtin

opaque definition change (e : expr) : tactic := builtin

opaque definition assert_hypothesis (id : identifier) (e : expr) : tactic := builtin

opaque definition lettac (id : identifier) (e : expr) : tactic := builtin

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
