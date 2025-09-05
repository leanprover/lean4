/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich
-/
module

prelude
public import Init.Meta
import Init.Data.String.Extra

public section

namespace Lean.Name

/-
Creates a round-trippable string name component if possible, otherwise returns `none`.
Names that are valid identifiers are not escaped, and otherwise, if they do not contain `»`, they are escaped.
- If `force` is `true`, then even valid identifiers are escaped.
-/
@[inline]
def escapePart (s : String) (force : Bool := false) : Option String :=
  if s.length > 0 && !force && isIdFirst (s.get 0) && (s.toSubstring.drop 1).all isIdRest then some s
  else if s.any isIdEndEscape then none
  else some <| idBeginEscape.toString ++ s ++ idEndEscape.toString

@[export lean_name_escapepart]
def Internal.escapePartImpl (s : String) (force : Bool) : Option String :=
  Name.escapePart s force

variable (sep : String) (escape : Bool) in
/--
Uses the separator `sep` (usually `"."`) to combine the components of the `Name` into a string.
See the documentation for `Name.toStringWithToken` for an explanation of `escape` and `isToken`.
-/
@[specialize isToken] -- explicit annotation because isToken is overridden in recursive call
def toStringWithSep (n : Name) (isToken : String → Bool := fun _ => false) : String :=
  match n with
  | anonymous       => "[anonymous]"
  | str anonymous s => maybeEscape s (isToken s)
  | num anonymous v => toString v
  | str n s         =>
    -- Escape the last component if the identifier would otherwise be a token
    let r := toStringWithSep n isToken
    let r' := r ++ sep ++ (maybeEscape s false)
    if escape && isToken r' then r ++ sep ++ (maybeEscape s true) else r'
  | num n v         => toStringWithSep n (isToken := fun _ => false) ++ sep ++ Nat.repr v
where
  maybeEscape s force := if escape then escapePart s force |>.getD s else s

/--
Converts a name to a string.

- If `escape` is `true`, then escapes name components using `«` and `»` to ensure that
  those names that can appear in source files round trip.
  Names with number components, anonymous names, and names containing `»` might not round trip.
  Furthermore, "pseudo-syntax" produced by the delaborator, such as `_`, `#0` or `?u`, is not escaped.
- The optional `isToken` function is used when `escape` is `true` to determine whether more
  escaping is necessary to avoid parser tokens.
  The insertion algorithm works so long as parser tokens do not themselves contain `«` or `»`.
-/
@[specialize]
def toStringWithToken (n : Name) (escape := true) (isToken : String → Bool) : String :=
  -- never escape "prettified" inaccessible names or macro scopes or pseudo-syntax introduced by the delaborator
  toStringWithSep "." (escape && !n.isInaccessibleUserName && !n.hasMacroScopes && !maybePseudoSyntax) n isToken
where
  maybePseudoSyntax :=
    if n == `_ then
      -- output hole as is
      true
    else if let .str _ s := n.getRoot then
      -- could be pseudo-syntax for loose bvar or universe mvar, output as is
      "#".isPrefixOf s || "?".isPrefixOf s
    else
      false

/--
Converts a name to a string.

- If `escape` is `true`, then escapes name components using `«` and `»` to ensure that
  those names that can appear in source files round trip.
  Names with number components, anonymous names, and names containing `»` might not round trip.
  Furthermore, "pseudo-syntax" produced by the delaborator, such as `_`, `#0` or `?u`, is not escaped.
-/
protected def toString (n : Name) (escape := true) : String :=
  Name.toStringWithToken n escape (fun _ => false)

@[export lean_name_tostring]
def Internal.toStringImpl (n : Name) (escape : Bool) : String :=
  Name.toString n escape

instance : ToString Name where
  toString n := n.toString

end Lean.Name
