-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic

-- This is just a trick to embed the 'tactic language' as a
-- Lean expression. We should view 'tactic' as automation
-- that when execute produces a term.
-- tactic_value is just a "dummy" for creating the "fake"
-- definitions
inductive tactic : Type :=
| tactic_value : tactic
-- Remark the following names are not arbitrary, the tactic module
-- uses them when converting Lean expressions into actual tactic objects.
-- The bultin 'by' construct triggers the process of converting a
-- a term of type 'tactic' into a tactic that sythesizes a term
definition then_tac   (t1 t2 : tactic) : tactic := tactic_value
definition orelse_tac (t1 t2 : tactic) : tactic := tactic_value
definition repeat_tac (t : tactic) : tactic := tactic_value
definition now_tac    : tactic := tactic_value
definition exact_tac  : tactic := tactic_value
definition state_tac  : tactic := tactic_value
definition fail_tac   : tactic := tactic_value
definition id_tac     : tactic := tactic_value
definition beta_tac   : tactic := tactic_value
definition apply      {B : Type} (b : B) : tactic := tactic_value
definition unfold_tac {B : Type} (b : B) : tactic := tactic_value

infixl `;`:200         := then_tac
infixl `|`:100         := orelse_tac
notation `!`:max t:max := repeat_tac t

