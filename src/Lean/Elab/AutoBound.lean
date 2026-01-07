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
    descr    := "Unbound local variables in declaration headers become implicit arguments. By default, only lowercase identifiers followed by numbers, subscripts, underscores, and apostrophes are eligible for automatic implicit binding. If the `relaxedAutoImplicit` option is also set, any atomic identifier is eligible to become an implicit argument."
  }

register_builtin_option relaxedAutoImplicit : Bool := {
    defValue := false
    descr    := "When \"relaxed\" mode is enabled, any atomic nonempty identifier is eligible for auto bound implicit locals (see option `autoImplicit`). This option has no effect with `autoImplicit` is `false`."
  }

/--
A valid automatically bound implicit (in not-relaxed mode) must begin with a lower-case letter;
this function captures some of the valid lower-case Unicode codepoints that are also valid
identifiers according to `Lean.isLetterLike`.

This should really be replaced with a Unicode-aware `toLowerCase` once such a thing exists in Lean.
-/
private def isLetterLikeLower (c : Char) : Bool :=
  c.isLower ||
  (0x0df ≤ c.val && c.val ≤ 0x0ff && c.val ≠ 0x0f7) ||     -- Latin-1 supplement letters but ÷
  (0x3b1 ≤ c.val && c.val ≤ 0x3c9 && c.val ≠ 0x3bb) ||     -- Lower greek, but lambda
  (0x3ca ≤ c.val && c.val ≤ 0x3d1 && c.val ≠ 0x3cf) ||     -- Lower greek
  (0x3d5 ≤ c.val && c.val ≤ 0x3f5 && (c.val &&& 1) = 1) || -- Lower greek and coptic (most of them)
  (0x3d6 = c.val || 0x3f0 = c.val || 0x3f2 = c.val) ||     -- ϖ, ϰ, ϲ
  (0x3f8 = c.val || 0x3fb = c.val || 0x3fc = c.val)        -- ϸ, ϻ, ϼ


/--
Checks whether a string is a name that can be auto-bound when the `relaxedAutoImplicit` option is
set to `false`.

In "strict" auto implicit mode, a identifier can only be auto-bound if it is one or more lower-case
characters (`α` or `xss` or `size`), optionally followed by an arbitrary sequence of numbers,
subscripts, and underscores. Therefore, both `αᵣₒₛₑ₂₁₁'''` and `num123_45` can be auto-bound even
with `relaxedAutoBound` set to `false`.
-/
public def isStrictAutoBoundIdentifier : Name → Bool
  | .str .anonymous s =>
    let varPrefix := s.toRawSubstring.dropRightWhile
      (fun c => c.isDigit || isSubScriptAlnum c || c == '_' || c == '\'')
    varPrefix.bsize > 0 && varPrefix.all isLetterLikeLower
  | _ => false

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

def checkValidAutoBoundImplicitName (n : Name) (allowed : Bool): Except MessageData Bool :=
  match n with
  | .str .anonymous s =>
    if s.length = 0 then
      .ok false
    else if allowed then
      .ok true
    else
      .error <| .note m!"It is not possible to treat `{.ofConstName n}` as an implicitly bound variable here because the `autoImplicit` option is set to `{.ofConstName ``false}`."
  | _ => .ok false

def isValidAutoBoundLevelName (n : Name) (relaxed : Bool) : Bool :=
  match n with
  | .str .anonymous s => s.length > 0 && (relaxed || isStrictAutoBoundIdentifier n)
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
