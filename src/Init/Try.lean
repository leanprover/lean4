/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Tactics

public section

namespace Lean.Try
/--
Configuration for `try?`.
-/
structure Config where
  /-- If `main` is `true`, all functions in the current module are considered for function induction, unfolding, etc. -/
  main := true
  /-- If `name` is `true`, all functions in the same namespace are considered for function induction, unfolding, etc. -/
  name := true
  /-- If `targetOnly` is `true`, `try?` collects information using the goal target only. -/
  targetOnly := false
  /-- Maximum number of suggestions. -/
  max := 8
  /-- If `missing` is `true`, allows the construction of partial solutions where some of the subgoals are `sorry`. -/
  missing := false
  /-- If `only` is `true`, generates solutions using `grind only` and `simp only`. -/
  only := true
  /-- If `harder` is `true`, more expensive tactics and operations are tried. -/
  harder := false
  /--
  If `merge` is `true`, it tries to compress suggestions such as
  ```
  induction a
  · grind only [= f]
  · grind only [→ g]
  ```
  as
  ```
  induction a <;> grind only [= f, → g]
  ```
  -/
  merge := true
  /-- If `wrapWithBy` is `true`, suggestions are wrapped with `by` for term mode usage. -/
  wrapWithBy := false
  deriving Inhabited

end Lean.Try

namespace Lean.Parser.Tactic

syntax (name := tryTrace) "try?" optConfig : tactic

/-- Helper internal tactic for implementing the tactic `try?`. -/
syntax (name := attemptAll) "attempt_all " withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic

/-- Helper internal tactic for implementing the tactic `try?` with parallel execution. -/
syntax (name := attemptAllPar) "attempt_all_par " withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic

/-- Helper internal tactic for implementing the tactic `try?` with parallel execution, returning first success. -/
syntax (name := firstPar) "first_par " withPosition((ppDedent(ppLine) colGe "| " tacticSeq)+) : tactic

/-- Helper internal tactic used to implement `evalSuggest` in `try?` -/
syntax (name := tryResult) "try_suggestions " tactic* : tactic

end Lean.Parser.Tactic

namespace Lean.Parser.Command

/--
`register_try?_tactic tac` registers a tactic `tac` as a suggestion generator for the `try?` tactic.

An optional priority can be specified with `register_try?_tactic (priority := 500) tac`.
Higher priority generators are tried first. The default priority is 1000.
-/
syntax (name := registerTryTactic) (docComment)?
  "register_try?_tactic" ("(" &"priority" ":=" num ")")? tacticSeq : command

end Lean.Parser.Command

/-- `∎` (typed as `\qed`) is a macro that expands to `try?` in tactic mode. -/
macro "∎" : tactic => `(tactic| try?)

/-- `∎` (typed as `\qed`) is a macro that expands to `by try? (wrapWithBy := true)` in term mode.
    The `wrapWithBy` config option causes suggestions to be prefixed with `by`. -/
macro "∎" : term => `(by try? (wrapWithBy := true))

namespace Lean.Try

/--
Marker for try?-solved subproofs in `exact? +try?` suggestions.
When `exact?` uses try? as a discharger, it wraps the proof in this marker
so that the unexpander can replace it with `(by try?)` in the suggestion.
-/
@[inline] def Marker {α : Sort u} (a : α) : α := a

@[app_unexpander Marker]
meta def markerUnexpander : PrettyPrinter.Unexpander := fun _ => do
  `(by try?)

end Lean.Try
