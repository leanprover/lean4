/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Rotella
-/
prelude
import Lean.ErrorExplanation

/--
This error occurs when an alternative in a pattern match can never be reached: any values that would
match the provided patterns would also match some preceding alternative. Refer to the
[Pattern Matching](lean-manual://section/pattern-matching) manual section for additional details
about pattern matching.

This error may appear in any pattern matching expression, including `match` expressions, equational
function definitions, `if let` bindings, and monadic `let` bindings with fallback clauses.

In pattern-matches with multiple arms, this error may occur if a less-specific pattern precedes a
more-specific one that it subsumes. Bear in mind that expressions are matched against patterns from
top to bottom, so specific patterns should precede generic ones.

In `if let` bindings and monadic `let` bindings with fallback clauses, in which only one pattern is
specified, this error indicates that the specified pattern will always be matched. In this case, the
binding in question can be replaced with a standard pattern-matching `let`.

One common cause of this error is that a pattern that was intended to match a constructor was
instead interpreted as a variable binding. This occurs, for instance, if an unprefixed constructor
name (e.g., `cons`) is used outside of its namespace (`List`). The constructor-name-as-variable
linter, enabled by default, will display a warning on any variable patterns that resemble
constructor names.

This error nearly always indicates an issue with the code where it appears. If needed, however,
`set_option match.ignoreUnusedAlts true` will disable the check for this error and allow pattern
matches with redundant alternatives to be compiled by discarding the unused arms.

# Examples

## Incorrect ordering of pattern matches

```lean broken
def seconds : List (List α) → List α
  | [] => []
  | _ :: xss => seconds xss
  | (_ :: x :: _) :: xss => x :: seconds xss
```
```output
Redundant alternative: Any expression matching
  (head✝ :: x :: tail✝) :: xss
will match one of the preceding alternatives
```
```lean fixed
def seconds : List (List α) → List α
  | [] => []
  | (_ :: x :: _) :: xss => x :: seconds xss
  | _ :: xss => seconds xss
```

Since any expression matching `(_ :: x :: _) :: xss` will also match `_ :: xss`, the last
alternative in the broken implementation is never reached. We resolve this by moving the more
specific alternative before the more general one.

## Unnecessary fallback clause

```lean broken
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
    | return 0
  return m + n
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```lean fixed
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
  return m + n
```

Here, the fallback clause serves as a catch-all for all values of `p` that do not match `(m, n)`.
However, no such values exist, so the fallback clause is unnecessary and can be removed. A similar
error arises when using `if let pat := e` when `e` will always match `pat`.

## Pattern treated as variable, not constructor

```lean broken
example (xs : List Nat) : Bool :=
  match xs with
  | nil => false
  | _ => true
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```lean fixed
example (xs : List Nat) : Bool :=
  match xs with
  | .nil => false
  | _ => true
```

In the original example, `nil` is treated as a variable, not as a constructor name, since this
definition is not within the `List` namespace. Thus, all values of `xs` will match the first
pattern, rendering the second unused. Notice that the constructor-name-as-variable linter displays a
warning at `nil`, indicating its similarity to a valid constructor name. Using dot-prefix notation,
as shown in the fixed example, or specifying the full constructor name `List.nil` achieves the
intended behavior.
-/
register_error_explanation lean.redundantMatchAlt {
  summary := "Match alternative will never be reached."
  sinceVersion := "4.22.0"
}
