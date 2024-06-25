/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
prelude
import Lean.Data.Lsp.Utf16
import Lean.Elab.InfoTree
import Lean.Message
import Lean.Util.EditDistance

set_option linter.missingDocs true

open Lean.EditDistance

namespace Lean.Elab

/-- A set of spelling suggestions for a name -/
structure NameSuggestions where
  /--
  Suggestions from the local context.

  Each suggestion is a string replacement, a score, and the local variable's FVarId during
  elaboration.
  -/
  localSuggestions : List (String × Nat × FVarId) := []
  /--
  Suggestions from the global environment.

  Each suggestion is a string replacement, a score, the constant's name, and a list of universe
  parameters that it would need to be instantiated with (used e.g. for constructing an `Expr` for
  the name to show in rich-text error messages).
  -/

  constSuggestions : List (String × Nat × Name × List Name) := []

/-- A custom info node with suggested names, for use in the code action. -/
structure NameSuggestionInfo where
  /-- The range of the document that the suggestions are for -/
  range : String.Range
  /--
  The replacements to be shown.

  This is a thunk because the code that computes the spelling suggestions can be expensive, with its
  results being used both in error messages and here. It should not be run if not necessary, but it
  should also not be run twice. Use this thunk together with `MessageData.lazy` for the error
  message.
 -/
  replacements : Thunk (Array String)
deriving TypeName

/--
Checks whether the set of suggestions is empty.
-/
def NameSuggestions.isEmpty (suggestions : NameSuggestions) : Bool :=
  suggestions.localSuggestions == [] && suggestions.constSuggestions == []

/--
Checks whether the set of suggestions is a singleton.

This can be useful when deciding whether to use a plural form in a message.
-/
def Suggestions.isSingleton (suggestions : NameSuggestions) : Bool :=
  match suggestions.localSuggestions, suggestions.constSuggestions with
  | [], [_] => true
  | [_], [] => true
  | _, _ => false

/--
Adds a constant to the suggested corrections.

The universe parameters can be found in `ConstantVal` values inside of `ConstantInfo` in the
environment. They're needed to construct expressions that are used in error messages to enable hover
support for the suggested names.
-/
def NameSuggestions.addConstant
    (toShow : String) (score : Nat) (name : Name) (universeParams : List Name)
    (suggestions : NameSuggestions) : NameSuggestions :=
  {suggestions with
    constSuggestions := (toShow, score, name, universeParams) :: suggestions.constSuggestions}

/--
Adds a constant to the suggested corrections.
-/
def NameSuggestions.addFVar
    (toShow : String) (score : Nat) (fvarId : FVarId)
    (suggestions : NameSuggestions) : NameSuggestions :=
  {suggestions with localSuggestions := (toShow, score, fvarId) :: suggestions.localSuggestions}

/--
Converts a set of name suggestions to `MessageData`, showing the top 10 suggestions if there's too
many.

This should typically be used as part of a lazy message (see `MessageData.lazy`).
-/
def NameSuggestions.toMessageData (suggestions : NameSuggestions) : MessageData :=
  if suggestions.isEmpty then .nil
  else m!"\n\n" ++
    let locals := suggestions.localSuggestions.map fun (str, score, fv) =>
      (str, score, m!"'{Expr.fvar fv}'")
    let consts := suggestions.constSuggestions.map fun (str, score, c, lvls) =>
      let params := lvls.map Level.param
      (str, score, MessageData.ofFormatWithInfos {
        fmt := "'" ++ Std.Format.tag 0 str ++ "'",
        infos :=
          .fromList [(0, Info.ofTermInfo {
            lctx := .empty,
            expr := .const c params,
            stx := .ident .none str.toSubstring c [],
            elaborator := `Delab,
            expectedType? := none
          })] _
      })
    let all := locals ++ consts |>.toArray |>.qsort lt
    let howMany : Nat := all.size
    let diff :=
        if howMany > 10 then [m!" (or {all.size - 10} others)"]
        else []
    let toShow := (all.extract 0 10 |>.toList |>.map (fun (_, _, msg) => msg)) ++ diff
    match toShow with
    | [s] => m!"Suggestion: {s}"
    | _ =>
      let comma : MessageData := "," ++ Format.line
      m!"Suggestions:{MessageData.nestD (.group (Format.line ++ MessageData.joinSep toShow comma))}"
where
  lt
    | (str1, score1, _), (str2, score2, _) =>
      if score1 == score2 then str1 < str2 else score1 < score2

/--
Get replacement strings for a set of suggestions, to be used in code actions.
-/
def NameSuggestions.getReplacements (suggestions : NameSuggestions) (max := 10) : Array String :=
  let locals := suggestions.localSuggestions.map fun (str, score, _) => (str, score)
  let consts := suggestions.constSuggestions.map fun (str, score, _, _) => (str, score)
  let all := locals ++ consts |>.toArray |>.qsort lt
  all.extract 0 max |>.map fun (x, _) => x
where
  lt
    | (str1, score1), (str2, score2) =>
      if score1 == score2 then str1 < str2 else score1 < score2

/--
Save a set of suggestions for a name. `ref` should be a piece of canonical syntax at which the
suggestions should be shown.

The thunk used here should share computational work with the lazy error message that lists
suggestions.

If `ref` is not canonical (that is, the user didn't write it) then no suggestions are saved.
-/
def saveNameSuggestions [Monad m] [MonadInfoTree m]
    (ref : Syntax) (suggestions : Thunk NameSuggestions) : m Unit := do
  if let some range := ref.getRange? (canonicalOnly := true) then
    pushInfoLeaf <| .ofCustomInfo {
      stx := ref
      value := Dynamic.mk
        { range, replacements := suggestions.map (·.getReplacements) : NameSuggestionInfo }
    }

/--
Suggests replacements for an unknown name `n`.

Suggestions are based on the Levenshtein distance between the name as it was written and the string
representations of the various forms of each in-scope name that are available, taking `open`
declarations and the current namespace into account. The local context is optional: if it is
omitted, then suggestions will only be for global constants.

Suggestions are only provided up to a threshold, based on the length of the name being corrected:
 * Single-character names: no suggestions provided
 * 2-3 character names: 1
 * 4-5 character names: 2
 * 6+ character names: 3

In practice, this is quite lenient.

All provided suggestions have the same Levenshtein distance from the unknown name. Potential
suggestions with a higher distance are discarded.

Note that the distance is computed between *string representations* of names. This is because the
feature is intended to catch typos, so `Lean.ElabTerm.elabTerm` should be corrected to
`Lean.Elab.Term.elabTerm`, even though their representation as the `Name` datatype is quite
different.
-/
def findSuggestions
    (n : Name)
    (env : Environment) (lctx : Option LocalContext) (currNamespace : Name) (openDecls : List OpenDecl)
    : Thunk NameSuggestions :=
  .mk fun () => Id.run do
    if skip n then return {}
    let nameString := n.toString
    if nameString.length < 2 then return {}
    let mut best :=
      if nameString.length < 4 then 1
      else if nameString.length < 6 then 2
      else 3
    let mut lsuggestions := []
    if let some lctx := lctx then
      for ldecl in lctx do
        if skip ldecl.userName then continue
        let lNameString := ldecl.userName.toString
        if let some d := levenshtein nameString lNameString best then
          if d < best then
            best := d
            lsuggestions := [(lNameString, d, ldecl.fvarId)]
          else if d == best then
            lsuggestions := lsuggestions.cons (lNameString, d, ldecl.fvarId)
    let mut gsuggestions := []
    for (c, info) in env.constants do
      if skip c then continue
      let mut nameStrings := []
      if isProtected env c then
        nameStrings := [c.toString]
      else
        nameStrings := inNs currNamespace.components c.components |>.map (·.toString)
        for decl in openDecls do
          if let some other := seenAs decl c then
            nameStrings := nameStrings.cons other.toString
      for cNameString in nameStrings do
        if let some d := levenshtein nameString cNameString best then
          if d < best then
            best := d
            lsuggestions := []
            gsuggestions := [(cNameString, d, c, info.levelParams)]
          else if d == best then
            gsuggestions := gsuggestions.cons (cNameString, d, c, info.levelParams)
    return {localSuggestions := lsuggestions, constSuggestions := gsuggestions}
where
  skip (n : Name) : Bool :=
    n.hasMacroScopes || n.isInaccessibleUserName || n.isImplementationDetail
  assemble (acc : Name) : List Name → Name
    | [] => acc
    | .str _ s :: ns => assemble (.str acc s) ns
    | .num _ n :: ns => assemble (.num acc n) ns
    | .anonymous :: ns => assemble acc ns
  seenAs : OpenDecl → Name → Option Name
    | .simple ns except, n =>
      let ns' := ns.components
      let n' := n.components
      if let some x := ns'.isPrefixOf? n' then
        let x := assemble .anonymous x
        if x ∈ except then none else some x
      else none
    | .explicit src tgt, n => if n == tgt then some src else none
  prefixes {α} : List α → List (List α)
  | [] => [[]]
  | x :: xs => [] :: (prefixes xs).map (x :: ·)
  inNs (ns : List Name) (n : List Name) :=
    prefixes ns |>.bind fun pre =>
      if let some x := pre.isPrefixOf? n then
        [assemble .anonymous x]
      else []
