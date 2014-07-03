-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic string
using string

namespace tactic
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
definition and_then   (t1 t2 : tactic) : tactic := tactic_value
definition or_else    (t1 t2 : tactic) : tactic := tactic_value
definition repeat     (t : tactic) : tactic := tactic_value
definition now        : tactic := tactic_value
definition assumption : tactic := tactic_value
definition state      : tactic := tactic_value
definition fail       : tactic := tactic_value
definition id         : tactic := tactic_value
definition beta       : tactic := tactic_value
definition apply      {B : Type} (b : B) : tactic := tactic_value
definition unfold     {B : Type} (b : B) : tactic := tactic_value
definition trace      (s : string) : tactic := tactic_value
infixl `;`:200         := and_then
infixl `|`:100         := or_else
notation `!`:max t:max := repeat t
notation `⟦` t `⟧`     := apply t
end
