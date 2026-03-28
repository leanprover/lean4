/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Hint

public section

/-! # Basic support for auto bound implicit local names -/

namespace Lean.Elab

register_builtin_option autoImplicit : Bool := {
    defValue := true
    descr    := "Unbound local variables in declaration headers become implicit arguments. In \"relaxed\" mode (default), any atomic identifier is eligible, otherwise only single character followed by numeric digits are eligible. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}."
  }

register_builtin_option relaxedAutoImplicit : Bool := {
    defValue := true
    descr    := "When \"relaxed\" mode is enabled, any atomic nonempty identifier is eligible for auto bound implicit locals (see option `autoImplicit`)."
  }

/--
Checks whether a string is a name that can be auto-bound when the `relaxedAutoImplicit` option is
set to `false`.

In "strict" auto implicit mode, a identifier can only be auto-bound if it is a single character (`α`
or `x`) or has an arbitrary postfix sequence of numbers, subscripts, and underscores. Therefore,
both `αᵣₒₛₑ₂₁₁'''` and `X123_45` can be auto-bound even with `relaxedAutoBound` set to `false`.
-/
private def isValidAutoBoundSuffix (s : String) : Bool :=
  s.toRawSubstring.drop 1 |>.all fun c => c.isDigit || isSubScriptAlnum c || c == '_' || c == '\''

/-!
Remark: Issue #255 exposed a nasty interaction between macro scopes and auto-bound-implicit names.
```
local notation "A" => id x
theorem test : A = A := sorry
```
We used to use `n.eraseMacroScopes` at `isValidAutoBoundImplicitName` and `isValidAutoBoundLevelName`.
Thus, in the example above, when `A` is expanded, a `x` with a fresh macro scope is created.
`x`+macros-scope is not in scope and is a valid auto-bound implicit name after macro scopes are erased.
So, an auto-bound exception would be thrown, and `x`+macro-scope would be added as a new implicit.
When, we try again, a `x` with a new macro scope is created and this process keeps repeating.
Therefore, we don't consider identifier with macro scopes anymore.

An `.error` value should be treated as a `false`—this is not a valid auto-bound implicit name—
but it contains additional notes (above and beyond `Unknown identifier`) to attach to
an error message.
-/

def checkValidAutoBoundImplicitName (n : Name) (allowed : Bool) (relaxed : Bool) : Except MessageData Bool :=
  match n with
  | .str .anonymous s =>
    if s.length = 0 then
      .ok false
    else if allowed && (relaxed || isValidAutoBoundSuffix s) then
      .ok true
    else if !allowed then
      .error <| .note m!"It is not possible to treat `{.ofConstName n}` as an implicitly bound variable here because the `autoImplicit` option is set to `{.ofConstName ``false}`."
    else
      .error <| .note m!"It is not possible to treat `{.ofConstName n}` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `{.ofConstName ``false}`."
  | _ => .ok false

def isValidAutoBoundLevelName (n : Name) (relaxed : Bool) : Bool :=
  match n with
  | .str .anonymous s => s.length > 0 && (relaxed || (s.front.isLower && isValidAutoBoundSuffix s))
  | _ => false

/--
Tracks extra context needed within the scope of `Lean.Elab.Term.withAutoBoundImplicit`
-/
public structure AutoBoundImplicitContext where
  /--
  This always matches the `autoImplicit` option; it is duplicated here in
  order to support the behavior of the deprecated `Lean.Elab.Term.Context.autoImplicit`
  method.
  -/
  autoImplicitEnabled : Bool
  /--
  Tracks a working set of variables that the auto-binding process currently
  anticipates adding implicit binding for.
  -/
  boundVariables : PArray Expr := {}
deriving Inhabited

instance : EmptyCollection AutoBoundImplicitContext where
  emptyCollection := AutoBoundImplicitContext.mk (autoImplicitEnabled := false) (boundVariables := {})

/--
Pushes a new variable onto the autoImplicit context, indicating that it needs
to be bound as an implicit parameter.
-/
public def AutoBoundImplicitContext.push (ctx : AutoBoundImplicitContext) (x : Expr) :=
  { ctx with boundVariables := ctx.boundVariables.push x }

end Lean.Elab
