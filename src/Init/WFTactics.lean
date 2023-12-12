/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SizeOf
import Init.MetaTypes
import Init.WF

/-- Unfold definitions commonly used in well founded relation definitions.
This is primarily intended for internal use in `decreasing_tactic`. -/
macro "simp_wf" : tactic =>
  `(tactic| try simp (config := { unfoldPartialApp := true }) [invImage, InvImage, Prod.lex, sizeOfWFRel, measure, Nat.lt_wfRel, WellFoundedRelation.rel])

/-- Extensible helper tactic for `decreasing_tactic`. This handles the "base case"
reasoning after applying lexicographic order lemmas.
It can be extended by adding more macro definitions, e.g.
```
macro_rules | `(tactic| decreasing_trivial) => `(tactic| linarith)
```
-/
syntax "decreasing_trivial" : tactic

macro_rules | `(tactic| decreasing_trivial) => `(tactic| (simp (config := { arith := true, failIfUnchanged := false })); done)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| assumption)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply Nat.sub_succ_lt_self; assumption) -- a - (i+1) < a - i if i < a
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply Nat.pred_lt'; assumption) -- i-1 < i if j < i
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply Nat.pred_lt; assumption)  -- i-1 < i if i ≠ 0

/-- Constructs a proof of decreasing along a well founded relation, by applying
lexicographic order lemmas and using `ts` to solve the base case. If it fails,
it prints a message to help the user diagnose an ill-founded recursive definition. -/
macro "decreasing_with " ts:tacticSeq : tactic =>
 `(tactic|
   (simp_wf
    repeat (first | apply Prod.Lex.right | apply Prod.Lex.left)
    repeat (first | apply PSigma.Lex.right | apply PSigma.Lex.left)
    first
    | done
    | $ts
    | fail "failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal"))

/-- `decreasing_tactic` is called by default on well-founded recursions in order
to synthesize a proof that recursive calls decrease along the selected
well founded relation. It can be locally overridden by using `decreasing_by tac`
on the recursive definition, and it can also be globally extended by adding
more definitions for `decreasing_tactic` (or `decreasing_trivial`,
which this tactic calls). -/
macro "decreasing_tactic" : tactic =>
  `(tactic| decreasing_with first | decreasing_trivial | subst_vars; decreasing_trivial)
