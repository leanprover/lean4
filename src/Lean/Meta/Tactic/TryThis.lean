/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro, Thomas Murrills
-/
prelude
import Lean.Server.CodeActions
import Lean.Widget.UserWidget
import Lean.Data.Json.Elab
import Lean.Data.Lsp.Utf16
import Lean.Meta.CollectFVars
import Lean.Meta.Tactic.ExposeNames
import Lean.Meta.TryThis
import Lean.Meta.Hint

/-!
# "Try this" code action and tactic suggestions

This implements a mechanism for tactics to print a message saying `Try this: <suggestion>`,
where `<suggestion>` is a link to a replacement tactic. Users can either click on the link
in the suggestion (provided by a widget), or use a code action which applies the suggestion.
-/
namespace Lean.Meta.Tactic.TryThis

open Lean Elab Tactic PrettyPrinter Meta Server RequestM

/-! # Raw widget -/

/--
This is a widget which is placed by `TryThis.addSuggestion` and `TryThis.addSuggestions`.

When placed by `addSuggestion`, it says `Try this: <replacement>`
where `<replacement>` is a link which will perform the replacement.

When placed by `addSuggestions`, it says:
```
Try these:
```
* `<replacement1>`
* `<replacement2>`
* `<replacement3>`
* ...

where `<replacement*>` is a link which will perform the replacement.
-/
@[builtin_widget_module] def tryThisWidget : Widget.Module where
  javascript := "
import * as React from 'react';
import { EditorContext, EnvPosContext } from '@leanprover/infoview';
const e = React.createElement;
export default function ({ suggestions, range, header, isInline, style }) {
  const pos = React.useContext(EnvPosContext)
  const editorConnection = React.useContext(EditorContext)
  const defStyle = style || {
    className: 'link pointer dim',
    style: { color: 'var(--vscode-textLink-foreground)' }
  }

  // Construct the children of the HTML element for a given suggestion.
  function makeSuggestion({ suggestion, preInfo, postInfo, style }) {
    function onClick() {
      editorConnection.api.applyEdit({
        changes: { [pos.uri]: [{ range, newText: suggestion }] }
      })
    }
    return [
      preInfo,
      e('span', { onClick, title: 'Apply suggestion', ...style || defStyle }, suggestion),
      postInfo
    ]
  }

  // Choose between an inline 'Try this'-like display and a list-based 'Try these'-like display.
  let inner = null
  if (isInline) {
    inner = e('div', { className: 'ml1' },
      e('pre', { className: 'font-code pre-wrap' }, header, makeSuggestion(suggestions[0])))
  } else {
    inner = e('div', { className: 'ml1' },
      e('pre', { className: 'font-code pre-wrap' }, header),
      e('ul', { style: { paddingInlineStart: '20px' } }, suggestions.map(s =>
        e('li', { className: 'font-code pre-wrap' }, makeSuggestion(s)))))
  }
  return e('details', { open: true },
    e('summary', { className: 'mv2 pointer' }, 'Suggestions'),
    inner)
}"

-- Because we can't use `builtin_widget_module` in `Lean.Meta.Hint`, we add the attribute here
attribute [builtin_widget_module] Hint.tryThisDiffWidget

/-! # Code action -/

/--
This is a code action provider that looks for `TryThisInfo` nodes and supplies a code action to
apply the replacement.
-/
@[builtin_code_action_provider] def tryThisProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  pure <| snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
    let .ofCustomInfo { stx, value } := info | result
    let some { range, suggestionTexts, codeActionPrefix? } :=
      value.get? TryThisInfo | result
    let some stxRange := stx.getRange? | result
    let stxRange := doc.meta.text.utf8RangeToLspRange stxRange
    unless stxRange.start.line ≤ params.range.end.line do return result
    unless params.range.start.line ≤ stxRange.end.line do return result
    let mut result := result
    for h : i in [:suggestionTexts.size] do
      let (newText, title?) := suggestionTexts[i]
      let title := title?.getD <| (codeActionPrefix?.getD "Try this: ") ++ newText
      result := result.push {
        eager.title := title
        eager.kind? := "quickfix"
        -- Only make the first option preferred
        eager.isPreferred? := if i = 0 then true else none
        eager.edit? := some <| .ofTextEdit doc.versionedIdentifier { range, newText }
      }
    result

/-! # Formatting -/

/-- Delaborate `e` into syntax suitable for use by `refine`. -/
def delabToRefinableSyntax (e : Expr) : MetaM Term :=
  withOptions (pp.mvars.anonymous.set · false) do delab e

/-- Delaborate `e` into a suggestion suitable for use by `refine`. -/
def delabToRefinableSuggestion (e : Expr) : MetaM Suggestion :=
  return { suggestion := ← delabToRefinableSyntax e, messageData? := e }

/-- Core of `addSuggestion` and `addSuggestions`. Whether we use an inline display for a single
element or a list display is controlled by `isInline`. -/
private def addSuggestionCore (ref : Syntax) (suggestions : Array Suggestion)
    (header : String) (isInline : Bool) (origSpan? : Option Syntax := none)
    (style? : Option SuggestionStyle := none)
    (codeActionPrefix? : Option String := none) : CoreM Unit := do
  if let some range := (origSpan?.getD ref).getRange? then
    let { suggestions, info, range } ← processSuggestions ref range suggestions codeActionPrefix?
    let suggestions := suggestions.map (·.1)
    let json := json% {
      suggestions: $suggestions,
      range: $range,
      header: $header,
      isInline: $isInline,
      style: $style?
    }
    pushInfoLeaf info
    Widget.savePanelWidgetInfo tryThisWidget.javascriptHash ref (props := return json)

/-- Add a "try this" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try this: <suggestion>`
* A widget is registered, saying `Try this: <suggestion>` with a link on `<suggestion>` to apply
  the suggestion
* A code action is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `s`: a `Suggestion`, which contains
  * `suggestion`: the replacement text;
  * `preInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
  * `postInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
  * `style?`: an optional `Json` object used as the value of the `style` attribute of the
    suggestion text's element (not the whole suggestion element).
  * `messageData?`: an optional message to display in place of `suggestion` in the info diagnostic
    (only). The widget message uses only `suggestion`. If `messageData?` is `none`, we simply use
    `suggestion` instead.
  * `toCodeActionTitle?`: an optional function `String → String` describing how to transform the
    pretty-printed suggestion text into the code action text which appears in the lightbulb menu.
    If `none`, we simply prepend `"Try This: "` to the suggestion text.
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string that begins the display. By default, it is `"Try this: "`.
* `codeActionPrefix?`: an optional string to be used as the prefix of the replacement text if the
  suggestion does not have a custom `toCodeActionTitle?`. If not provided, `"Try this: "` is used.
-/
def addSuggestion (ref : Syntax) (s : Suggestion) (origSpan? : Option Syntax := none)
    (header : String := "Try this: ") (codeActionPrefix? : Option String := none) : MetaM Unit := do
  logInfoAt ref m!"{header}{s}"
  addSuggestionCore ref #[s] header (isInline := true) origSpan?
    (codeActionPrefix? := codeActionPrefix?)

/-- Add a list of "try this" suggestions as a single "try these" suggestion. This has three effects:

* An info diagnostic is displayed saying `Try these: <list of suggestions>`
* A widget is registered, saying `Try these: <list of suggestions>` with a link on each
  `<suggestion>` to apply the suggestion
* A code action for each suggestion is added, which will apply the suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `suggestions`: an array of `Suggestion`s, which each contain
  * `suggestion`: the replacement text;
  * `preInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
  * `postInfo?`: an optional string shown immediately after the replacement text in the widget
    message (only)
  * `style?`: an optional `Json` object used as the value of the `style` attribute of the
    suggestion text's element (not the whole suggestion element).
  * `messageData?`: an optional message to display in place of `suggestion` in the info diagnostic
    (only). The widget message uses only `suggestion`. If `messageData?` is `none`, we simply use
    `suggestion` instead.
  * `toCodeActionTitle?`: an optional function `String → String` describing how to transform the
    pretty-printed suggestion text into the code action text which appears in the lightbulb menu.
    If `none`, we simply prepend `"Try This: "` to the suggestion text.
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string that precedes the list. By default, it is `"Try these:"`.
* `style?`: a default style for all suggestions which do not have a custom `style?` set.
* `codeActionPrefix?`: an optional string to be used as the prefix of the replacement text for all
  suggestions which do not have a custom `toCodeActionTitle?`. If not provided, `"Try this: "` is
  used.
-/
def addSuggestions (ref : Syntax) (suggestions : Array Suggestion)
    (origSpan? : Option Syntax := none) (header : String := "Try these:")
    (style? : Option SuggestionStyle := none)
    (codeActionPrefix? : Option String := none) : MetaM Unit := do
  if suggestions.isEmpty then throwErrorAt ref "no suggestions available"
  let msgs := suggestions.map toMessageData
  let msgs := msgs.foldl (init := MessageData.nil) (fun msg m => msg ++ m!"\n• " ++ .nest 2 m)
  logInfoAt ref m!"{header}{msgs}"
  addSuggestionCore ref suggestions header (isInline := false) origSpan? style? codeActionPrefix?

/-! # Tactic-specific widget hooks -/
/--
Evaluates `tac` in `initialState` without recovery or sorrying on elaboration failure. If
`expectedType?` is non-`none`, an error is thrown if the resulting goal type is not equal to the
provided type (up to `Expr` equality modulo metavariable instantiation).
-/
private def evalTacticWithState (initialState : Tactic.SavedState) (tac : TSyntax `tactic)
    (expectedType? : Option Expr := none) : TacticM Unit := do
  let currState ← saveState
  initialState.restore
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic tac
    if let some expectedType := expectedType? then
      let type ← (← getMainGoal).getType
      let type ← instantiateMVars type
      let expectedType ← instantiateMVars expectedType
      if type != expectedType then
        throwError "tactic did not produce expected goal"
  finally
    currState.restore

/--
Returns a possibly modified version of `tac` and `msg` that succeeds in `initialState`, prepending
`expose_names` if necessary. If `expectedType?` is non-`none`, the tactic is only considered to have
"succeeded" if the resulting goal is equal (up to `Expr` equality modulo metavariable instantiation)
to the provided type. Returns `none` if the tactic fails even with `expose_names`.

Remark: We cannot determine if a tactic requires `expose_names` merely by inspecting its syntax
(shadowed variables are delaborated without daggers) nor the underlying `Expr` used to produce it
(some inaccessible names may be implicit arguments that do not appear in the delaborated syntax).
-/
private def mkValidatedTactic (tac : TSyntax `tactic) (msg : MessageData)
    (initialState : Tactic.SavedState) (expectedType? : Option Expr := none) :
    TacticM (Option (TSyntax `tactic × MessageData)) := do
  try
    evalTacticWithState initialState tac expectedType?
    return some (tac, msg)
  catch _ =>
    -- Note: we must use `(expose_names; _)` and not `· expose_names; _` to avoid generating
    -- spurious tactic-abort exceptions, since these tactics may not close the goal
    let tac ← `(tactic| (expose_names; $tac))
    try
      evalTacticWithState initialState tac expectedType?
      return some (tac, m!"(expose_names; {msg})")
    catch _ =>
      return none

private def mkFailedToMakeTacticMsg (targetKind : MessageData) (invalidTactic : MessageData) : MessageData :=
  m!"found {targetKind}, but the corresponding tactic failed:{indentD invalidTactic}\n\n\
     It may be possible to correct this proof by adding type annotations, explicitly specifying \
     implicit arguments, or eliminating unnecessary function abstractions."

/--
Returns the syntax for an `exact` or `refine` (as indicated by `useRefine`) tactic corresponding to
`e` as well as a `MessageData` representation with hover information.
If `exposeNames` is `true`, prepends the tactic with `expose_names.` Note that the tactic is
always generated within `withExposedNames` to avoid generating unprintable characters.
-/
private def mkExactSuggestionSyntax (e : Expr) (useRefine : Bool) :
    MetaM (TSyntax `tactic × MessageData) :=
  withOptions (pp.mvars.set · false) <| withExposedNames do
  let exprStx ← delabToRefinableSyntax e
  let tac ← if useRefine then `(tactic| refine $exprStx) else `(tactic| exact $exprStx)
  -- We must add the message context here to account for exposed names
  let exprMessage ← addMessageContext <| MessageData.ofExpr e
  let tacMessage := if useRefine then m!"refine {exprMessage}" else m!"exact {exprMessage}"
  return (tac, tacMessage)

private def addExactSuggestionCore (addSubgoalsMsg : Bool) (checkState? : Option Tactic.SavedState) (e : Expr) :
    TacticM (Suggestion ⊕ MessageData) :=
  withOptions (pp.mvars.set · false) do
  let mvars ← getMVars e
  let hasMVars := !mvars.isEmpty
  let (suggestion, messageData) ← mkExactSuggestionSyntax e (useRefine := hasMVars)
  let some checkState := checkState? | return .inl suggestion
  let some (suggestion, messageData) ← mkValidatedTactic suggestion messageData checkState
    | let messageData := m!"(expose_names; {messageData})"
      return .inr <| mkFailedToMakeTacticMsg m!"a {if hasMVars then "partial " else ""}proof" messageData
  let postInfo? ← if !addSubgoalsMsg || mvars.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in mvars do
      -- TODO: use a MessageData.ofExpr instead of rendering to string
      let e ← withExposedNames <| PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure str
  return .inl { suggestion := suggestion, postInfo?, messageData? := messageData }

/-- Add an `exact e` or `refine e` suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `e`: the replacement expression
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `addSubgoalsMsg`: if true (default false), any remaining subgoals will be shown after
  `Remaining subgoals:`
* `codeActionPrefix?`: an optional string to be used as the prefix of the replacement text if the
  suggestion does not have a custom `toCodeActionTitle?`. If not provided, `"Try this: "` is used.
* `checkState?`: if passed, the tactic state in which the generated tactic will be validated,
  inserting `expose_names` if necessary.
* `tacticErrorAsInfo`: if true (default false), if a generated tactic is invalid (e.g., due to a
   pretty-printing issue), the resulting error message will be logged as an info message instead of
   being thrown as an error. Has no effect if `checkState?` is `none`.
-/
def addExactSuggestion (ref : Syntax) (e : Expr)
    (origSpan? : Option Syntax := none)
    (addSubgoalsMsg := false)
    (codeActionPrefix? : Option String := none)
    (checkState? : Option Tactic.SavedState := none)
    (tacticErrorAsInfo := false) : TacticM Unit := do
  match (← addExactSuggestionCore addSubgoalsMsg checkState? e) with
  | .inl suggestion =>
    addSuggestion ref suggestion
      (origSpan? := origSpan?) (codeActionPrefix? := codeActionPrefix?)
  | .inr message =>
    if tacticErrorAsInfo then logInfo message else throwError message

/-- Add `exact e` or `refine e` suggestions if they can be successfully generated; for those that
cannot, display messages indicating the invalid generated tactics.

The parameters are:
* `ref`: the span of the info diagnostic
* `es`: the array of replacement expressions
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `addSubgoalsMsg`: if true (default false), any remaining subgoals will be shown after
  `Remaining subgoals:`
* `codeActionPrefix?`: an optional string to be used as the prefix of the replacement text for all
  suggestions which do not have a custom `toCodeActionTitle?`. If not provided, `"Try this: "` is
  used.
* `checkState?`: if passed, the tactic state in which the generated tactics will be validated,
  inserting `expose_names` if necessary.
* `tacticErrorAsInfo`: if true (default true), invalid generated tactics will log info messages
  instead of throwing an error. The default behavior differs from `addExactSuggestion` because
  throwing an error means that any subsequent suggestions will not be displayed. Has no effect if
  `checkState?` is `none`.
-/
def addExactSuggestions (ref : Syntax) (es : Array Expr)
    (origSpan? : Option Syntax := none) (addSubgoalsMsg := false)
    (codeActionPrefix? : Option String := none)
    (checkState? : Option Tactic.SavedState := none)
    (tacticErrorAsInfo := true) : TacticM Unit := do
  let suggestionOrMessages ← es.mapM <| addExactSuggestionCore addSubgoalsMsg checkState?
  let mut suggestions : Array Suggestion := #[]
  let mut messages : Array MessageData := #[]
  for suggestionOrMessage in suggestionOrMessages do
    match suggestionOrMessage with
    | .inl suggestion => suggestions := suggestions.push suggestion
    | .inr message =>
      unless tacticErrorAsInfo do throwError message
      messages := messages.push message
  addSuggestions ref suggestions (origSpan? := origSpan?) (codeActionPrefix? := codeActionPrefix?)
  for message in messages do
    logInfo message

/-- Add a term suggestion.

The parameters are:
* `ref`: the span of the info diagnostic
* `e`: the replacement expression
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string which precedes the suggestion. By default, it's `"Try this: "`.
* `codeActionPrefix?`: an optional string to be used as the prefix of the replacement text if the
  suggestion does not have a custom `toCodeActionTitle?`. If not provided, `"Try this: "` is used.
-/
def addTermSuggestion (ref : Syntax) (e : Expr)
    (origSpan? : Option Syntax := none) (header : String := "Try this: ")
    (codeActionPrefix? : Option String := none) : MetaM Unit := do
  addSuggestion ref (← delabToRefinableSuggestion e) (origSpan? := origSpan?) (header := header)
    (codeActionPrefix? := codeActionPrefix?)

/-- Add term suggestions.

The parameters are:
* `ref`: the span of the info diagnostic
* `es`: an array of the replacement expressions
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `header`: a string which precedes the list of suggestions. By default, it's `"Try these:"`.
* `codeActionPrefix?`: an optional string to be used as the prefix of the replacement text for all
  suggestions which do not have a custom `toCodeActionTitle?`. If not provided, `"Try this: "` is
  used.
-/
def addTermSuggestions (ref : Syntax) (es : Array Expr)
    (origSpan? : Option Syntax := none) (header : String := "Try these:")
    (codeActionPrefix? : Option String := none) : MetaM Unit := do
  addSuggestions ref (← es.mapM delabToRefinableSuggestion)
    (origSpan? := origSpan?) (header := header) (codeActionPrefix? := codeActionPrefix?)

open Lean Elab Elab.Tactic PrettyPrinter Meta

/-- Add a suggestion for `have h : t := e`. -/
def addHaveSuggestion (ref : Syntax) (h? : Option Name) (t? : Option Expr) (e : Expr)
    (origSpan? : Option Syntax := none) (checkState? : Option Tactic.SavedState := none) : TacticM Unit := do
  let prop ← isProp (← inferType e)
  -- We construct the tactic and message data separately to facilitate hover info
  let mut (tac, msg) ← withExposedNames do
    let estx ← delabToRefinableSyntax e
    let (tac, msg) ← if let some t := t? then
      let tstx ← delabToRefinableSyntax t
      if prop then
        match h? with
        | some h => pure (← `(tactic| have $(mkIdent h):ident : $tstx := $estx), m!"have {h} : {t} := {e}")
        | none => pure (← `(tactic| have : $tstx := $estx), m!"have : {t} := {e}")
      else
        let h := h?.getD `_
        pure (← `(tactic| let $(mkIdent h):ident : $tstx := $estx), m!"let {h} : {t} := {e}")
    else
      if prop then
        match h? with
        | some h => pure (← `(tactic| have $(mkIdent h):ident := $estx), m!"have {h} := {e}")
        | none => pure (← `(tactic| have := $estx), m!"have := {e}")
      else
        let h := h?.getD `_
        pure (← `(tactic| let $(mkIdent h):ident := $estx), m!"let {h} := {e}")
    pure (tac, ← addMessageContext msg)
  if let some checkState := checkState? then
    let some (tac', msg') ← mkValidatedTactic tac msg checkState
      | logInfo <| mkFailedToMakeTacticMsg "a proof" msg
        return
    tac := tac'
    msg := msg'
  addSuggestion ref (s := { suggestion := tac, messageData? := msg }) origSpan?

open Lean.Parser.Tactic
open Lean.Syntax

/-- Add a suggestion for `rw [h₁, ← h₂] at loc`.

Parameters:
* `ref`: the span of the info diagnostic
* `rules`: a list of arguments to `rw`, with the second component `true` if the rewrite is reversed
* `type?`: the goal after the suggested rewrite, `.none` if the rewrite closes the goal, or `.undef`
  if the resulting goal is unknown
* `loc?`: the hypothesis at which the rewrite is performed, or `none` if the goal is targeted
* `origSpan?`: a syntax object whose span is the actual text to be replaced by `suggestion`.
  If not provided it defaults to `ref`.
* `checkState?`: if passed, the tactic state in which the generated tactic will be validated,
  inserting `expose_names` if necessary
-/
def addRewriteSuggestion (ref : Syntax) (rules : List (Expr × Bool))
  (type? : LOption Expr := .undef) (loc? : Option Expr := none)
  (origSpan? : Option Syntax := none) (checkState? : Option Tactic.SavedState := none) :
    TacticM Unit := do
  let mut (tac, tacMsg, extraMsg, extraStr) ← withExposedNames do
    let rulesStx := TSepArray.ofElems <| ← rules.toArray.mapM fun ⟨e, symm⟩ => do
      let t ← delabToRefinableSyntax e
      if symm then `(rwRule| ← $t:term) else `(rwRule| $t:term)
    -- The seemingly superfluous `:=` below is a workaround for issue #2663
    let mut tac := ← do
      let loc ← loc?.mapM fun loc => do `(location| at $(← delab loc):term)
      `(tactic| rw [$rulesStx,*] $(loc)?)

    -- We don't simply write `let mut tacMsg := m!"{tac}"` here
    -- but instead rebuild it, so that there are embedded `Expr`s in the message,
    -- thus giving more information in the hovers.
    -- Perhaps in future we will have a better way to attach elaboration information to
    -- `Syntax` embedded in a `MessageData`.
    let toMessageData (e : Expr) : MessageData := if e.isConst then .ofConst e else .ofExpr e
    let rulesMsg := MessageData.sbracket <| MessageData.joinSep
      (rules.map fun ⟨e, symm⟩ => (if symm then "← " else "") ++ toMessageData e) ", "
    let mut tacMsg ← addMessageContext <|
      if let some loc := loc? then
        m!"rw {rulesMsg} at {loc}"
      else
        m!"rw {rulesMsg}"

    let (extraMsg, extraStr) ←
      match type? with
      | .some type =>
        pure (← addMessageContext m!"\n-- {type}", s!"\n-- {← PrettyPrinter.ppExpr type}")
      | .none => pure (m!"\n-- no goals", "\n-- no goals")
      | .undef => pure (m!"", "")
    return (tac, tacMsg, extraMsg, extraStr)

  if let some checkState := checkState? then
    let type? := match type? with
      | .some type => some type
      | _ => none
    let some (tac', tacMsg') ← mkValidatedTactic tac tacMsg checkState type?
      | tacMsg := m!"(expose_names; {tacMsg})"
        logInfo <| mkFailedToMakeTacticMsg "an applicable rewrite lemma" (tacMsg ++ extraMsg)
        return
    tac := tac'
    tacMsg := tacMsg'
  addSuggestion ref (s := { suggestion := tac, postInfo? := extraStr, messageData? := tacMsg ++ extraMsg })
    origSpan?
