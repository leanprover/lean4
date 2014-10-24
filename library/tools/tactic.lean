----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
----------------------------------------------------------------------------------------------------

import data.string data.num
-- This is just a trick to embed the 'tactic language' as a
-- Lean expression. We should view 'tactic' as automation
-- that when execute produces a term.
-- tactic.builtin is just a "dummy" for creating the
-- definitions that are actually implemented in C++
inductive tactic : Type :=
builtin : tactic

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

-- This is just a trick to embed expressions into tactics.
-- The nested expressions are "raw". They tactic should
-- elaborate them when it is executed.
inductive expr : Type :=
builtin : expr

opaque definition apply   (e : expr) : tactic := builtin
opaque definition rapply  (e : expr) : tactic := builtin
opaque definition rename  (a b : expr) : tactic := builtin
opaque definition intro   (e : expr) : tactic := builtin
opaque definition generalize (e : expr) : tactic := builtin

inductive expr_list : Type :=
nil  : expr_list,
cons : expr → expr_list → expr_list

opaque definition intro_list (es : expr_list) : tactic := builtin
notation `intros`   := intro_list expr_list.nil
notation `intros` `(` l:(foldr `,` (h t, expr_list.cons h t) expr_list.nil) `)` := intro_list l

opaque definition unfold      (e : expr) : tactic := builtin
opaque definition exact       (e : expr) : tactic := builtin
opaque definition trace       (s : string) : tactic := builtin
infixl `;`:15 := and_then
notation `[` h:10 `|`:10 r:(foldl 10 `|` (e r, or_else r e) h) `]` := r
definition try         (t : tactic) : tactic := [t | id]
definition repeat1     (t : tactic) : tactic := t ; repeat t
definition focus       (t : tactic) : tactic := focus_at t 0
definition determ      (t : tactic) : tactic := at_most t 1

end tactic
