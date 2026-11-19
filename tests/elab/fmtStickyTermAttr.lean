import Lean
/-!
Tests for the `@[fmt_sticky_term]` attribute, which registers `Lean.Fmt.StickyTermFn`s
that determine whether a term propagates the stickiness of its right-hand side in
applications.
-/

open Lean

@[fmt_sticky_term]
def stickyFun : Fmt.StickyTermFn := fun t =>
  t.raw.isOfKind ``Parser.Term.fun

@[fmt_sticky_term]
def stickyParenthesizedFun : Fmt.StickyTermFn := fun t =>
  match t.raw with
  | `(Parser.Term.paren| ($_:fun)) => true
  | _ => false

open Elab Command in
def checkPropagatesRhsStickiness (t : Term) (expected : Bool) : CommandElabM Unit := do
  let actual := Fmt.propagatesRhsStickiness (← getEnv) t
  unless actual == expected do
    throwError "expected `propagatesRhsStickiness` to return {expected} for `{t}`"

open Elab Command in
#eval show CommandElabM Unit from do
  checkPropagatesRhsStickiness (← `(fun x => x)) true
  checkPropagatesRhsStickiness (← `((fun x => x))) true
  checkPropagatesRhsStickiness (← `(f x)) false
  checkPropagatesRhsStickiness (← `((1 + 1))) false

-- The attribute can only be applied to declarations of type `Lean.Fmt.StickyTermFn`.

/--
error: Cannot add attribute `[fmt_sticky_term]`: Declaration `notAStickyTermFn` has type
  Bool
but `[fmt_sticky_term]` can only be added to declarations of type
  Fmt.StickyTermFn
-/
#guard_msgs in
@[fmt_sticky_term] def notAStickyTermFn := true

-- The attribute cannot be applied locally or in scoped fashion.

/-- error: Invalid attribute scope: Attribute `[fmt_sticky_term]` must be global, not `local` -/
#guard_msgs in
attribute [local fmt_sticky_term] stickyFun
