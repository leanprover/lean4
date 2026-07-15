import Lean.Elab.GuardMsgs
import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.DocString.Builtin

/-!
Tests the non-builtin `@[deferred_doc_check]` attribute path: a custom doc role records a deferred
check carrying a number, and a handler registered via the attribute confirms the number is greater
than 5.
-/

open Lean Lean.Doc Elab Term
open scoped Lean.Doc.Syntax

/-- A deferred check that its number exceeds 5. -/
structure GreaterThanFive where
  n : Nat
deriving TypeName

@[deferred_doc_check GreaterThanFive]
def checkGreaterThanFive : DeferredCheckHandler := fun d => do
  let some ⟨n⟩ := d.get? GreaterThanFive
    | throwError "internal error: expected a `GreaterThanFive`"
  unless n > 5 do
    throwError "{n} is not greater than 5"

/-- Defers a check that the referenced number is greater than 5. -/
@[doc_role]
def gtFive (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  if h : xs.size = 1 then
    match xs[0] with
    | `(inline|code($s)) =>
      let some n := s.getString.toNat? | throwErrorAt s "expected a number"
      return .deferred (← addDeferredCheck (.mk (GreaterThanFive.mk n)) #[] (← getRef)) #[.code s.getString]
    | other => throwErrorAt other "expected a number"
  else
    throwError "expected precisely one code argument"

set_option doc.verso true

/-- Big enough: {gtFive}`7`. -/
def usesBig := 1

/-- Too small: {gtFive}`3`. -/
def usesSmall := 2

/--
info: FAIL usesSmall: 3 is not greater than 5
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let m := (← getEnv).mainModule
  let failures ← Lean.Doc.DeferredCheck.run (· == m)
  if failures.isEmpty then
    logInfo "all deferred checks passed"
  else
    for (_, c, msg) in failures do
      let site := match c.site with
        | .decl n => toString n
        | .moduleDoc i => s!"module docstring #{i}"
      logInfo m!"FAIL {site}: {msg}"
