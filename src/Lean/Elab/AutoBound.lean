/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Data.Options
public import Lean.Message
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
Intuitively a variable can be auto-bound in strict mode if it is a single character (`α` or `x`),
but also it can have an arbitrary trailing sequence of numbers, subscripts, and underscores: both
`αᵣₒₛₑ₂₁₁'''` and `X123_45` can be auto-bound even with `relaxedAutoBound` set to `false`.
-/
private def isValidAutoBoundSuffix (s : String) : Bool :=
  s.toSubstring.drop 1 |>.all fun c => c.isDigit || isSubScriptAlnum c || c == '_' || c == '\''

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

An `.error` value should be treated as a `false` --- this is not a valid auto-bound implicit name --
but is tagged with additional notes and hints (above and beyond `Unknown identifier`) to attach to
an error message.
-/

def checkValidAutoBoundImplicitName (n : Name) (allowed : Bool) (relaxed : Bool) : Except (CoreM MessageData) Bool :=
  match n with
  | .str .anonymous s =>
    if s.length = 0 then
      .ok false
    else if allowed && (relaxed || isValidAutoBoundSuffix s) then
      .ok true
    else if !allowed then
      .error <| do
        return (.note m!"It is not possible to treat `{.ofConstName n}` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.")
    else
      .error <| pure (.note m!"It is not possible to treat `{.ofConstName n}` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `false`.")
  | _ => .ok false

def isValidAutoBoundLevelName (n : Name) (relaxed : Bool) : Bool :=
  match n with
  | .str .anonymous s => s.length > 0 && (relaxed || (s.front.isLower && isValidAutoBoundSuffix s))
  | _ => false

end Lean.Elab
