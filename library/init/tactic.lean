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

opaque definition apply      (e : expr)   : tactic := builtin
opaque definition rapply     (e : expr)   : tactic := builtin
opaque definition fapply     (e : expr)   : tactic := builtin
opaque definition rename     (a b : expr) : tactic := builtin
opaque definition intro      (e : expr)   : tactic := builtin
opaque definition generalize (e : expr)   : tactic := builtin
opaque definition clear      (e : expr)   : tactic := builtin
opaque definition revert     (e : expr)   : tactic := builtin
opaque definition unfold     (e : expr)   : tactic := builtin
opaque definition exact      (e : expr)   : tactic := builtin
opaque definition trace      (s : string) : tactic := builtin
opaque definition inversion  (id : expr)  : tactic := builtin

notation a `↦` b:max := rename a b

inductive expr_list : Type :=
| nil  : expr_list
| cons : expr → expr_list → expr_list

-- rewrite_tac is just a marker for the builtin 'rewrite' notation
-- used to create instances of this tactic.
opaque definition rewrite_tac (e : expr_list) : tactic := builtin

opaque definition inversion_with  (id : expr) (ids : expr_list) : tactic := builtin
notation `cases` a:max := inversion a
notation `cases` a:max `with` `(` l:(foldr `,` (h t, expr_list.cons h t) expr_list.nil) `)` := inversion_with a l

opaque definition intro_lst (ids : expr_list) : tactic := builtin
notation `intros`   := intro_lst expr_list.nil
notation `intros` `(` l:(foldr `,` (h t, expr_list.cons h t) expr_list.nil) `)` := intro_lst l

opaque definition generalize_lst (es : expr_list) : tactic := builtin
notation `generalizes` `(` l:(foldr `,` (h t, expr_list.cons h t) expr_list.nil) `)` := generalize_lst l

opaque definition clear_lst  (ids : expr_list) : tactic := builtin
notation `clears` `(` l:(foldr `,` (h t, expr_list.cons h t) expr_list.nil) `)` := clear_lst l

opaque definition revert_lst (ids : expr_list) : tactic := builtin
notation `reverts` `(` l:(foldr `,` (h t, expr_list.cons h t) expr_list.nil) `)` := revert_lst l

opaque definition change_goal (e : expr) : tactic := builtin
notation `change` e := change_goal e

opaque definition assert_hypothesis (id : expr) (e : expr) : tactic := builtin

infixl `;`:15 := and_then
notation `[` h `|` r:(foldl `|` (e r, or_else r e) h) `]` := r

definition try         (t : tactic) : tactic := [t | id]
definition repeat1     (t : tactic) : tactic := t ; repeat t
definition focus       (t : tactic) : tactic := focus_at t 0
definition determ      (t : tactic) : tactic := at_most t 1

definition do (n : num) (t : tactic) : tactic :=
nat.rec id (λn t', (t;t')) (nat.of_num n)

end tactic
