import Lean

/-!  Tests for `@[no_fallback]` on tactic elaborators and macros. -/

open Lean Elab Tactic

/-! ## Default behavior: fallback on error -/

syntax "myTac1" : tactic

elab_rules : tactic
  | `(tactic| myTac1) => logInfo "fallback"

elab_rules : tactic
  | `(tactic| myTac1) => throwError "first"

/-- info: fallback -/
#guard_msgs in
example : True := by myTac1; trivial

/-! ## `@[no_fallback]` prevents fallback on `.error` -/

syntax "myTac2" : tactic

elab_rules : tactic
  | `(tactic| myTac2) => logInfo "unreached"

@[no_fallback]
elab_rules : tactic
  | `(tactic| myTac2) => throwError "committed"

/-- error: committed -/
#guard_msgs in
example : True := by myTac2; trivial

/-! ## `@[no_fallback]` prevents fallback on `abortTactic` -/

syntax "myTac3" : tactic

elab_rules : tactic
  | `(tactic| myTac3) => logInfo "unreached"

@[no_fallback]
elab_rules : tactic
  | `(tactic| myTac3) => do
    logError "aborted"
    throwAbortTactic

/--
error: aborted
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by myTac3; trivial

/-! ## `@[no_fallback]` still allows `unsupportedSyntax` to fall back -/

syntax "myTac4" (ident)? : tactic

elab_rules : tactic
  | `(tactic| myTac4) => logInfo "without ident"

@[no_fallback]
elab_rules : tactic
  | `(tactic| myTac4 $_:ident) => logInfo "with ident"

/-- info: without ident -/
#guard_msgs in
example : True := by myTac4; trivial

/-! ## `@[no_fallback]` on a macro -/

syntax "myTac5" : tactic

elab_rules : tactic
  | `(tactic| myTac5) => logInfo "unreached"

@[no_fallback]
macro_rules
  | `(tactic| myTac5) => `(tactic| fail "macro expansion committed")

/--
error: macro expansion committed
⊢ True
-/
#guard_msgs in
example : True := by myTac5; trivial
