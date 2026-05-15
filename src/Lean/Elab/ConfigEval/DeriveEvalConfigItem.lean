/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Elab.ConfigEval.DeriveEvalTerm
public import Lean.Elab.ConfigEval.DeriveEvalExpr
import Lean.Elab.ConfigEval.Util
public import Lean.Elab.ConfigEval.Basic
public import Lean.Elab.ConfigEval.Instances

/-!
# Derivation of `EvalConfigItem`

This module defines `defEvalConfigItem`, which derives an `EvalConfigItem` object for structures.
Its main interface are the command syntaxes defined in `Lean.Elab.ConfigEval.Commands`.

-/

public section

namespace Lean.Elab.ConfigEval

open Meta Term Command

inductive EvalConfigItemHandlerKind
  /-- Handler is called when its key matches the configuration key exactly.
  The matched key is not allowed to be `Name.anonymous`. -/
  | exact
  /-- Handler is called when its key is a strict prefix of the configuration key.
  The matched key may be `Name.anonymous`. -/
  | wildcard
  deriving BEq

structure EvalConfigItemHandler where
  /-- Ref for the key. -/
  ref : Syntax
  /-- The key that's handled. May be anonymous for certain kinds. -/
  key : Name
  /-- The kind of match this handler is looking for. -/
  kind : EvalConfigItemHandlerKind
  /-- A function `fun cfg item => ...`. -/
  body : Term
  /-- Constant to use for terminfo. This is added to the `HandlerTrie`. -/
  projFn? : Option Name := none
  /-- Constant to use for field completion terminfo. -/
  struct? : Option Name := none

structure EvalConfigItemView where
  /-- Fields to not automatically synthesize handlers for, in addition to those keys
  already appearing in `handlers`. -/
  omitFields : Array (Ident × Name)
  /-- Explicitly provided handlers. -/
  handlers : Array EvalConfigItemHandler

/--
Trie used to organize those handlers provided in `EvalConfigItemView` and those
handlers that are synthesized.

The fields in this `structure` are given in the order they are applied.
Conceptually, searching for handlers is done recursively (however the algorithm is compiled
into non-recursive code via metaprogramming). At each step of the search the state
consists of a trie key `tkey`, a trie node `trie`, and a configuration key `ckey`.
Once any handler is applied, matching is complete (handlers can't decide not to apply at run time).
1. If `exact?` is present and `tkey == ckey`, then it is applied.
2. If `ckey` is of the form `root.ckey'` and there's a `(root, trie')` entry in `children`,
   then we recursively search for a handler using `tkey.root`, `trie'`, `ckey'`.
   If one is found, it is applied.
3. If `wildcard?` is present and `ckey'` is nonempty, then that handler is applied.
4. Otherwise, the search failed. If this is recursive, we return and continue.
-/
private structure HandlerTrie where
  /-- The `EvalConfigItemHandlerKind.exact` handler for this trie position's key. -/
  exact? : Option EvalConfigItemHandler := none
  /-- Handlers for which this trie position's key is a strict prefix. -/
  children : Array (String × HandlerTrie) := #[]
  /-- The `EvalConfigItemHandlerKind.wildcard` handler for this trie position's key. -/
  wildcard? : Option EvalConfigItemHandler := none
  /-- Constant to use for terminfo. The root of the trie does not have this set.
  Collected from `EvalConfigItemHandler.projFn?`. -/
  projFn? : Option Name := none
  /-- Constant to use for field completion terminfo. The root of the trie has this set.
  Collected from `EvalConfigItemHandler.struct?`. -/
  struct? : Option Name := none
  deriving Inhabited

/--
Finds a handler that applies to this key.
Returns the trie key and the handler.

If `kind` is `exact` then it returns the handler that would actually apply,
and if it is `wildcard` then it returns the wildcard handler corresponding to that
key if an `exact` handler would also apply.
-/
private partial def HandlerTrie.find? (trie : HandlerTrie) (key : Name) (kind : EvalConfigItemHandlerKind) :
    Option (Name × EvalConfigItemHandler) := do
  let root := key.getRoot
  if root.isAnonymous then
    match kind with
    | .exact => return (.anonymous, ← trie.exact?)
    | .wildcard => return (.anonymous, ← trie.wildcard?)
  else
    let s := root.getString!
    try
      let (_, child) ← trie.children.find? (·.1 == s)
      let (key', h) ← child.find? (key.replacePrefix root .anonymous) kind
      pure (root.appendCore key', h)
    catch _ =>
      let h ← trie.wildcard?
      return (key, h)

/--
Inserts the handler into the trie. The expectation is that a handler is not already
installed at a given key (use `HandlerTrie.find?` to verify this ahead of time),
but it is implemented to replace handlers.

`EvalConfigItemHandler.key` is modified
-/
private partial def HandlerTrie.insert (trie : HandlerTrie) (h : EvalConfigItemHandler) (key : Name := h.key) :
    HandlerTrie :=
  let root := key.getRoot
  if root.isAnonymous then
    let projFn? := trie.projFn? <|> h.projFn?
    let struct? := trie.struct? <|> h.struct?
    match h.kind with
    | .exact    => { trie with projFn?, struct?, exact? := some h }
    | .wildcard => { trie with projFn?, struct?, wildcard? := some h }
  else
    let s := root.getString!
    let key' := key.replacePrefix root .anonymous
    if let some idx := trie.children.findIdx? (·.1 == s) then
      let children := trie.children.modify idx fun (s, child) => (s, child.insert h key')
      { trie with children }
    else
      let child := HandlerTrie.insert {} h key'
      { trie with children := trie.children.push (s, child)}

private partial def HandlerTrie.insertStruct (trie : HandlerTrie) (key : Name) (struct : Name) :
    HandlerTrie :=
  let root := key.getRoot
  if root.isAnonymous then
    let struct := trie.struct?.getD struct
    { trie with struct? := some struct }
  else
    let s := root.getString!
    let key' := key.replacePrefix root .anonymous
    if let some idx := trie.children.findIdx? (·.1 == s) then
      let children := trie.children.modify idx fun (s, child) => (s, child.insertStruct key' struct)
      { trie with children }
    else
      let child := HandlerTrie.insertStruct {} key' struct
      { trie with children := trie.children.push (s, child)}

/--
Precompiled version of `evalTermOrExprWithElab (α := Bool)` that
also makes use of the cached `item.bool?` value.
-/
def evalBoolItem (item : ConfigItem) : TermElabM Bool := do
  if let some b := item.bool? then
    if (← getInfoState).enabled then
      addTermInfo' item.value (if b then toExpr true else toExpr false)
    return b
  else
    evalTermOrExprWithElab ⟨item.value⟩

def addConstInfo' (ref : Syntax) (projFn : Name) : TermElabM Unit := do
  if (← getInfoState).enabled then
    if (← getEnv).contains projFn then -- in case we are in Lean prelude
      addConstInfo ref projFn

private structure State where
  toDerive : NameMap ExprSet := {}
  toOmit : Array (Ident × Name)

/-- Monad for collecting types that we should try deriving `EvalTerm` or `EvalExpr` instances for. -/
private abbrev M := StateRefT State TermElabM

private def addToDerive (cls : Name) (ty : Expr) : M Unit :=
  modify fun s => { s with toDerive := s.toDerive.insert cls (s.toDerive.getD cls {} |>.insert ty) }

private def hasToOmit (key : Name) (projFn : Name) : M Bool := do
  let s ← get
  if let some idx := s.toOmit.findIdx? (fun (_, name) => name == key) then
    let (ref, _) := s.toOmit[idx]!
    addConstInfo ref projFn
    set { s with toOmit := s.toOmit.eraseIdx! idx }
    return true
  else
    return false

/--
Makes an `EvalConfigItem` for the structure.
Supports structures with no parameters or universes.
-/
partial def defEvalConfigItem
    (doc? : Option (TSyntax ``Parser.Command.docComment))
    (vis? : Option (TSyntax ``Parser.Command.visibility))
    (kind : TSyntax ``Parser.Term.attrKind)
    (tk : Syntax)
    (struct : Ident)
    (fnIdent : Ident)
    (extraBinders : TSyntaxArray ``Parser.Term.bracketedBinder)
    (view : EvalConfigItemView) :
    CommandElabM Unit := do
  let structName ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo struct
  -- Pass one: make the trie to collect the missing instances
  let (_, { toOmit, toDerive }) ← liftTermElabM <| mkTrie structName true |>.run { toOmit := view.omitFields }
  for (ref, name) in toOmit do
    logErrorAt ref m!"No such field `{name}` of `{.ofConstName structName}`"
  -- Now that we're back in CommandElabM, derive instances
  for ty in toDerive.getD ``EvalTerm {} do
    try
      ensureEvalTerm vis? kind tk struct ty
    catch ex =>
      trace[Elab.ConfigEval] "Deriving EvalTerm instance for `{ty}` failed: {ex.toMessageData}"
  for ty in toDerive.getD ``EvalExpr {} do
    try
      ensureEvalExpr vis? kind tk struct ty
    catch ex =>
      trace[Elab.ConfigEval] "Deriving EvalEval instance for `{ty}` failed: {ex.toMessageData}"
  -- Pass two: rebuild the trie in the presense of these instances, and build the command
  let cmd ← liftTermElabM <| withFreshMacroScope <| mkCmd structName
  elabCommand cmd
where
  hasInstance (cls : Name) (ty : Expr) : M Bool := do
    try
      discard <| synthInstance (← mkAppM cls #[ty])
      return true
    catch _ =>
      unless ty.hasFVar do
        addToDerive cls ty
      return false
  checkStruct (structName : Name) : MetaM Unit := do
    let env ← getEnv
    unless isStructure env structName do
      throwErrorAt struct "`{.ofConstName structName}` is not a structure"
    let .inductInfo val ← getConstInfo structName
      | throwErrorAt struct "`{.ofConstName structName}` is not a structure"
    unless val.levelParams.isEmpty && val.numIndices == 0 && val.numParams == 0 do
      throwErrorAt struct "`{.ofConstName structName}` must not have parameters, indices, or universe parameters"
  visitStruct (trie : HandlerTrie) (keyPrefix : Name) (structName : Name) (allowFailure : Bool) : M HandlerTrie := do
    withTraceNode `Elab.ConfigEval (fun _ => return m!"adding handlers for fields of `{.ofConstName structName}` with prefix `{keyPrefix}`, allowFailure: {allowFailure}") do
    checkStruct structName
    let fields := getStructureFieldsFlattened (← getEnv) structName (includeSubobjectFields := false)
    withLocalDeclD `self (Expr.const structName []) fun self => do
      let mut trie := trie
      for field in fields do
        let key := keyPrefix ++ field
        let proj ← mkProjection self field
        let some projFn := proj.getAppFn.constName? | panic! "(Internal error) Invalid projection {inlineExpr proj}"
        if (← hasToOmit key projFn) then
          trace[Elab.ConfigEval] "key `{key}` was excluded, skipping"
          continue
        let fieldTy ← inferType proj
        let exactHandler? := trie.find? key .exact
        let mut hasExact := exactHandler?.any fun (key', _) => key == key'
        let hasWildcard := (trie.find? key .wildcard).isSome
        trace[Elab.ConfigEval] m!"key `{key}` hasExact: {hasExact}, hasWildcard: {hasWildcard}"
        let mut synthesizedHandler := false
        -- If there's no exact key for this field yet, synthesize a handler
        if !hasExact then
          let mut body ← `(pure { config with $(mkIdent key):ident := value })
          if ← withReducible <| isDefEq fieldTy (mkConst ``Bool) then
            trace[Elab.ConfigEval] "field `{.ofConstName projFn}`, using {.ofConstName ``evalBoolItem}"
            body ← `(fun config item => evalBoolItem item >>= fun value => $body:term)
            trie := trie.insert { ref := struct, key, kind := .exact, body, projFn? := projFn }
            hasExact := true
            synthesizedHandler := true
          else
            let hasEvalTerm ← hasInstance ``EvalTerm fieldTy
            let hasEvalExpr ← hasInstance ``EvalExpr fieldTy
            trace[Elab.ConfigEval] "field `{.ofConstName projFn}`, hasEvalTerm: {hasEvalTerm}, hasEvalExpr: {hasEvalExpr}"
            hasExact := hasEvalTerm || hasEvalExpr
            synthesizedHandler := synthesizedHandler || hasEvalTerm || hasEvalExpr
            let mkHandler (eval : Term) : M Term :=
              `(item.checkNotBool >>= fun _ => $eval:term >>= fun value => $body)
            body ←
              match hasEvalTerm, hasEvalExpr with
              | true,  true  => `(evalTermOrExprWithElab ⟨item.value⟩) >>= mkHandler
              | false, true  => `(evalExprWithElab ⟨item.value⟩) >>= mkHandler
              | true,  false => `(evalTermWithRef ⟨item.value⟩) >>= mkHandler
              | false, false => `(item.throwCannotSetOption $(quote structName))
            body ← `(fun _ item => $body)
            trie := trie.insert { ref := struct, key, kind := .exact, body, projFn? := projFn }
        if let some structName' := (← whnfR fieldTy).constName? then
          if isStructure (← getEnv) structName' then
            trie := trie.insertStruct key structName'
            if ← try checkStruct structName'; pure true catch _ => pure false then
              /-
              Heuristic: if there is already a handler for an exact match, we shouldn't report errors
              if sub-keys can't be used. In Mathlib for example, the `linarith` tactic has configuration
              options that are `structure`s wrapping monadic and functional values. Users are only
              meant to set the entire `structure`, not the fields within them. We are imagining here
              that `structure` configuration values are not common, so we shouldn't rigidly expect
              handlers for sub-keys (saving metaprogram authors the hassle of writing complete `except`
              clauses). We may consider `(allowFailure := true)` in the future, and/or `except foo.*` clauses.
              -/
              trie ← visitStruct trie key structName' (allowFailure := allowFailure || hasExact || exactHandler?.isSome)
        unless allowFailure || hasExact || hasWildcard || synthesizedHandler do
          throwErrorAt struct (m!"Field `{key}` of type{inlineExpr fieldTy}is missing both `{.ofConstName ``EvalTerm}` and `{.ofConstName ``EvalExpr}` instances."
              ++ .note m!"The scoped `ensure_eval_term_instance` and `ensure_eval_expr_instance` commands in `Lean.Elab.ConfigEval` were not able to derive instances.")
      return trie
  mkTrie (structName : Name) (allowFailure : Bool) : M HandlerTrie := do
    let mut trie : HandlerTrie := {}
    trie := trie.insertStruct Name.anonymous structName
    for handler in view.handlers do
      if handler.key.isAnonymous && handler.kind matches .exact then
        throwErrorAt handler.ref "Unexpected empty key for handler"
      if let some (key, _) := trie.find? handler.key handler.kind then
        throwErrorAt handler.ref "Duplicate handler for key `{key}`"
      trie := trie.insert handler
    trie ← visitStruct trie .anonymous structName allowFailure
    unless (← hasToOmit `config structName) || (trie.find? `config .exact).isSome do
      if ← hasInstance ``EvalExpr (mkConst structName) then
        -- Only use an `EvalExpr` instance; we don't have plans to support structure instance notation with `EvalTerm`.
        let cfgBody ← `(fun _ item => (evalExprWithElab ⟨item.value⟩ : TermElabM $struct))
        trie := trie.insert { ref := tk, key := `config, kind := .exact, body := cfgBody }
    return trie
  /--
  Assembles the full key matcher from the trie. Makes use of `item` in the current macro scope.
  -/
  assemble (trie : HandlerTrie) (onFail : Term) : TermElabM Term := do
    let { exact?, children, wildcard?, projFn?, struct? } := trie
    let bodyApplied (handler : EvalConfigItemHandler) : TermElabM Term := do
      `(($handler.body : $struct → ConfigItem → TermElabM $struct) config item')
    let handleChildren (onFail : Term) : TermElabM Term := do
      if children.isEmpty then
        return onFail
      else
        let children ← children.mapM fun (s, trie') => return (s, ← assemble trie' onFail)
        let body ← makeStringMatcher (← `(ident| root)) children onFail
        `(have root := item.getRootStr
          have item' := item
          have item := item.shift
          $body)
    let handleWildcard : TermElabM Term := do
      if let some h := wildcard? then
        let body ← bodyApplied h
        if children.isEmpty then
          return body
        else
          let jp ← withFreshMacroScope `(ident| doWildcard)
          let body' ← handleChildren (← `($jp ()))
          `(have $jp (_ : Unit) := $body; $body')
      else
        handleChildren onFail
    let handleExact : TermElabM Term := do
      let body ← handleWildcard
      let onAnon ← if let some h := exact? then bodyApplied h else pure onFail
      `(if item.isAnonymous then $onAnon else $body)
    let mut body ← handleExact
    if let some projFn := projFn? then
      body ← `(item'.addConstInfo $(quote projFn) >>= fun _ => $body)
    if let some struct := struct? then
      body ← `(item.addCompletionInfo $(quote struct) >>= fun _ => $body)
    return body
  mkCmd (structName : Name) : TermElabM Command := do
    let trie ← mkTrie structName false |>.run' { toOmit := view.omitFields }
    let body ← assemble trie (← `(invalidOption item))
    `($[$doc?:docComment]?
      $[$vis?:visibility]?
      def $fnIdent $[$extraBinders]* : EvalConfigItem $struct where
        set (config : $struct) (item : ConfigItem) : TermElabM $struct := do
          have invalidOption (item : ConfigItem) : TermElabM $struct := item.throwInvalidOption (some $(quote structName))
          let item' := item
          $body:term)

end Lean.Elab.ConfigEval
