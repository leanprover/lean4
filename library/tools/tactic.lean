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
definition and_then    [opaque] (t1 t2 : tactic) : tactic := builtin
definition or_else     [opaque] (t1 t2 : tactic) : tactic := builtin
definition append      [opaque] (t1 t2 : tactic) : tactic := builtin
definition interleave  [opaque] (t1 t2 : tactic) : tactic := builtin
definition par         [opaque] (t1 t2 : tactic) : tactic := builtin
definition fixpoint    [opaque] (f : tactic → tactic) : tactic := builtin
definition repeat      [opaque] (t : tactic) : tactic := builtin
definition at_most     [opaque] (t : tactic) (k : num)  : tactic := builtin
definition discard     [opaque] (t : tactic) (k : num)  : tactic := builtin
definition focus_at    [opaque] (t : tactic) (i : num)  : tactic := builtin
definition try_for     [opaque] (t : tactic) (ms : num) : tactic := builtin
definition now         [opaque] : tactic := builtin
definition assumption  [opaque] : tactic := builtin
definition eassumption [opaque] : tactic := builtin
definition state       [opaque] : tactic := builtin
definition fail        [opaque] : tactic := builtin
definition id          [opaque] : tactic := builtin
definition beta        [opaque] : tactic := builtin
definition apply       [opaque] {B : Type} (b : B) : tactic := builtin
definition unfold      [opaque] {B : Type} (b : B) : tactic := builtin
definition exact       [opaque] {B : Type} (b : B) : tactic := builtin
definition trace       [opaque] (s : string) : tactic := builtin
precedence `;`:200
infixl ; := and_then
notation `!` t:max     := repeat t
-- [ t_1 | ... | t_n ] notation
notation `[` h:100 `|` r:(foldl 100 `|` (e r, or_else r e) h) `]` := r
-- [ t_1 || ... || t_n ] notation
notation `[` h:100 `||` r:(foldl 100 `||` (e r, par r e) h) `]` := r
definition try         (t : tactic) : tactic := [ t | id ]
notation `?` t:max     := try t
definition repeat1     (t : tactic) : tactic := t ; !t
definition focus       (t : tactic) : tactic := focus_at t 0
definition determ      (t : tactic) : tactic := at_most t 1

end tactic
