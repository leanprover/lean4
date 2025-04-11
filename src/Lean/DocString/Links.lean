/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

prelude
import Lean.Syntax

set_option linter.missingDocs true

namespace Lean

@[extern "lean_manual_get_root"]
private opaque getManualRoot : Unit → String

private def fallbackManualRoot := "https://lean-lang.org/doc/reference/latest/"

/--
Computes the root of the Lean reference manual that should be used for targets.

If the environment variable `LEAN_MANUAL_ROOT` is set, it is used as the root. If not, but a manual
root is pre-configured for the current Lean executable (typically true for releases), then it is
used. If neither are true, then `https://lean-lang.org/doc/reference/latest/` is used.
-/
def manualRoot : BaseIO String := do
  let r ←
    if let some root := (← IO.getEnv "LEAN_MANUAL_ROOT") then
      pure root
    else
      let root := getManualRoot ()
      if root.isEmpty then
        pure fallbackManualRoot
      else
        pure root
  return if r.endsWith "/" then r else r ++ "/"

/--
Rewrites links from the internal Lean manual syntax to the correct URL. This rewriting is an
overapproximation: any parentheses containing the internal syntax of a Lean manual URL is rewritten.

The internal syntax is the URL scheme `lean-manual` followed by the path `/KIND/MORE...`, where
`KIND` is a kind of content being linked to. Presently, the only valid kind is `section`, and it
requires that the remainder of the path consists of one element, which is a section or part identifier.

The correct URL is based on a manual root URL, which is determined by the `LEAN_MANUAL_ROOT`
environment variable. If this environment variable is not set, a manual root provided when Lean was
built is used (typically this is the version corresponding to the current release). If no such root
is available, the latest version of the manual is used.
-/
def rewriteManualLinksCore (s : String) : BaseIO (Array (String.Range × String) × String) := do
  let scheme := "lean-manual://"
  let mut out := ""
  let mut errors := #[]
  let mut iter := s.iter
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h

    if !lookingAt scheme iter.prev then
      out := out.push c
      continue

    let start := iter.prev.forward scheme.length
    let mut iter' := start
    while h' : iter'.hasNext do
      let c' := iter'.curr' h'
      iter' := iter'.next' h'
      if urlChar c' && !iter'.atEnd then
        continue
      match rw (start.extract iter'.prev) with
      | .error err =>
        errors := errors.push (⟨iter.prev.i, iter'.prev.i⟩, err)
        out := out.push c
        break
      | .ok path =>
        out := out ++ (← manualRoot) ++ path
        out := out.push c'
        iter := iter'
        break

  pure (errors, out)

where
  /--
  Returns `true` if the character is one of those allowed in RFC 3986 sections 2.2 and 2.3. other
  than '(' or')'.
  -/
  urlChar (c : Char) : Bool :=
    -- unreserved
    c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~' ||
    -- gen-delims
    c == ':' || c == '/' || c == '?' || c == '#' || c == '[' || c == ']' || c == '@' ||
    -- sub-delims
    -- ( and ) are excluded due to Markdown's link syntax
    c == '!' || c == '$' || c == '&' || c == '\'' || /- c == '(' || c == ')' || -/ c == '*' ||
    c == '+' || c == ',' || c == ';' || c == '='

  /--
  Returns `true` if `goal` is a prefix of the string at the position pointed to by `iter`.
  -/
  lookingAt (goal : String) (iter : String.Iterator) : Bool :=
    iter.s.substrEq iter.i goal 0 goal.endPos.byteIdx

  rw (path : String) : Except String String := do
    match path.splitOn "/" with
    | "section" :: args =>
      if let [s] := args then
        if s.isEmpty then
          throw s!"Empty section ID"
        return s!"find/?domain=Verso.Genre.Manual.section&name={s}"
      else
        throw s!"Expected one item after 'section', but got {args}"
    | [] | [""] =>
      throw "Missing documentation type"
    | other :: _ =>
      throw s!"Unknown documentation type '{other}'. Expected 'section'."


/--
Rewrites Lean reference manual links in `docstring` to point at the reference manual.

This assumes that all such links have already been validated by `validateDocComment`.
-/
def rewriteManualLinks (docString : String) : BaseIO String := do
  let (errs, str) ← rewriteManualLinksCore docString
  if !errs.isEmpty then
    let errReport :=
      r#"**❌ Syntax Errors in Lean Language Reference Links**

The `lean-manual` URL scheme is used to link to the version of the Lean reference manual that
corresponds to this version of Lean. Errors occurred while processing the links in this documentation
comment:
"# ++
      String.join (errs.toList.map (fun (⟨s, e⟩, msg) => s!" * ```{docString.extract s e}```: {msg}\n\n"))
    return str ++ "\n\n" ++ errReport
  return str


/--
Validates all links to the Lean reference manual in `docstring`, printing an error message if any
are invalid. Returns `true` if all links are valid.

This is intended to be used before saving a docstring that is later subject to rewriting with
`rewriteManualLinks`, in contexts where the imports needed to produce better error messages in
`validateDocComment` are not yet available.
-/
def validateBuiltinDocString (docString : String) : IO Unit := do
  let (errs, _) ← rewriteManualLinksCore docString
  if !errs.isEmpty then
    throw <| IO.userError <|
      s!"Errors in builtin documentation comment:\n" ++
      String.join (errs.toList.map fun (⟨s, e⟩, msg) => s!" * {repr <| docString.extract s e}:\n    {msg}\n")
