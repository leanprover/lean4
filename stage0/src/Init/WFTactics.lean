/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SizeOf
import Init.WF

macro "simp_wf" : tactic => `(simp [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel])

syntax "decreasing_trivial" : tactic -- Extensible helper tactic for `decreasing_tactic`

macro_rules | `(tactic| decreasing_trivial) => `(tactic| simp (config := { arith := true }); done)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| assumption)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply Nat.sub_succ_lt_self; assumption) -- a - (i+1) < a - i if i < a
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply Nat.pred_lt'; assumption) -- i-1 < i if j < i
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply Nat.pred_lt; assumption)  -- i-1 < i if i ≠ 0

macro "decreasing_with " ts:tacticSeq : tactic =>
 `((simp_wf
    repeat (first | apply Prod.Lex.right | apply Prod.Lex.left)
    repeat (first | apply PSigma.Lex.right | apply PSigma.Lex.left)
    first
    | $ts:tacticSeq
    | fail "failed to prove termination, possible solutions:\n  - Use `have`-expressions to prove the remaining goals\n  - Use `termination_by` to specify a different well-founded relation\n  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal"))

macro "decreasing_tactic" : tactic => `(decreasing_with first | decreasing_trivial | subst_vars; decreasing_trivial)
