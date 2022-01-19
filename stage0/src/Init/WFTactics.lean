/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SizeOf
import Init.WF

macro "decreasing_tactic" : tactic =>
 `((simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel]
    repeat (first | apply Prod.Lex.right | apply Prod.Lex.left)
    repeat (first | apply PSigma.Lex.right | apply PSigma.Lex.left)
    first
    | apply Nat.lt_succ_self                   -- i < i+1
    | decide                                   -- e.g., 0 < 1
    | apply Nat.pred_lt; assumption            -- i-1 < i if i ≠ 0
    | apply Nat.pred_lt'; assumption           -- i-1 < i if j < i
    | apply Nat.sub_succ_lt_self; assumption   -- a - (i+1) < a - i if i < a
    | assumption
    -- TODO: linearith
    -- TODO: improve
))
