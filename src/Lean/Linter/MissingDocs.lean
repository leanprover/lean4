/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Lean.Parser.Syntax
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.Elab.Command
import Lean.Elab.SetOption
import Lean.Linter.Util

namespace Lean.Linter
open Elab.Command Parser Command
open Parser.Term hiding «set_option»

register_builtin_option linter.missingDocs : Bool := {
  defValue := false
  descr := "enable the 'missing documentation' linter"
}

def getLinterMissingDocs (o : LinterOptions) : Bool := getLinterValue linter.missingDocs o


namespace MissingDocs

abbrev SimpleHandler := Syntax → CommandElabM Unit
abbrev Handler := Bool → SimpleHandler

def SimpleHandler.toHandler (h : SimpleHandler) : Handler :=
  fun enabled stx => if enabled then h stx else pure ()

unsafe def mkHandlerUnsafe (constName : Name) : ImportM Handler := do
  let env  := (← read).env
  let opts := (← read).opts
  match env.find? constName with
  | none      => throw ↑s!"unknown constant '{constName}'"
  | some info => match info.type with
    | Expr.const ``SimpleHandler _ => do
      let h ← IO.ofExcept $ env.evalConst SimpleHandler opts constName
      pure h.toHandler
    | Expr.const ``Handler _ =>
      IO.ofExcept $ env.evalConst Handler opts constName
    | _ => throw ↑s!"unexpected missing docs handler at '{constName}', `MissingDocs.Handler` or `MissingDocs.SimpleHandler` expected"

@[implemented_by mkHandlerUnsafe]
opaque mkHandler (constName : Name) : ImportM Handler

builtin_initialize builtinHandlersRef : IO.Ref (NameMap Handler) ← IO.mkRef {}

builtin_initialize missingDocsExt :
  PersistentEnvExtension (Name × Name) (Name × Name × Handler) (List (Name × Name) × NameMap Handler) ←
  registerPersistentEnvExtension {
    mkInitial       := return ([], ← builtinHandlersRef.get)
    addImportedFn   := fun as => do
      ([], ·) <$> as.foldlM (init := ← builtinHandlersRef.get) fun s as =>
        as.foldlM (init := s) fun s (n, k) => s.insert k <$> mkHandler n
    addEntryFn      := fun (entries, s) (n, k, h) => ((n, k)::entries, s.insert k h)
    exportEntriesFn := fun s => s.1.reverse.toArray
    statsFn := fun s => format "number of local entries: " ++ format s.1.length
  }

def addHandler (env : Environment) (declName key : Name) (h : Handler) : Environment :=
  missingDocsExt.addEntry env (declName, key, h)

def getHandlers (env : Environment) : NameMap Handler := (missingDocsExt.getState env).2

partial def missingDocs : Linter where
  run stx := do
    if let some h := (getHandlers (← getEnv)).find? stx.getKind then
      h (getLinterMissingDocs (← getLinterOptions)) stx

builtin_initialize addLinter missingDocs

def addBuiltinHandler (key : Name) (h : Handler) : IO Unit :=
  builtinHandlersRef.modify (·.insert key h)

builtin_initialize
  let mkAttr (builtin : Bool) (name : Name) := registerBuiltinAttribute {
    name
    descr           := (if builtin then "(builtin) " else "") ++
      "adds a syntax traversal for the missing docs linter"
    applicationTime := .afterCompilation
    add             := fun declName stx kind => do
      unless kind == AttributeKind.global do throwError "invalid attribute '{name}', must be global"
      let env ← getEnv
      unless builtin || (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute '{name}', declaration is in an imported module"
      let decl ← getConstInfo declName
      let fnNameStx ← Attribute.Builtin.getIdent stx
      let key ← Elab.realizeGlobalConstNoOverloadWithInfo fnNameStx
      unless decl.levelParams.isEmpty && (decl.type == .const ``Handler [] || decl.type == .const ``SimpleHandler []) do
        throwError "unexpected missing docs handler at '{declName}', `MissingDocs.Handler` or `MissingDocs.SimpleHandler` expected"
      if builtin then
        let h := if decl.type == .const ``SimpleHandler [] then
          mkApp (mkConst ``SimpleHandler.toHandler) (mkConst declName)
        else mkConst declName
        declareBuiltin declName <| mkApp2 (mkConst ``addBuiltinHandler) (toExpr key) h
      else
        setEnv <| missingDocsExt.addEntry env (declName, key, ← mkHandler declName)
  }
  mkAttr true `builtin_missing_docs_handler
  mkAttr false `missing_docs_handler

def lint (stx : Syntax) (msg : String) : CommandElabM Unit :=
  logLint linter.missingDocs stx m!"missing doc string for {msg}"

def lintNamed (stx : Syntax) (msg : String) : CommandElabM Unit :=
  lint stx s!"{msg} {stx.getId}"

def lintField (parent stx : Syntax) (msg : String) : CommandElabM Unit :=
  lint stx s!"{msg} {parent.getId}.{stx.getId}"

def lintStructField (parent stx : Syntax) (msg : String) : CommandElabM Unit :=
  lint stx s!"{msg} {parent.getId}.{stx.getId}"

def hasInheritDoc (attrs : Syntax) : Bool :=
  attrs[0][1].getSepArgs.any fun attr =>
    attr[1].isOfKind ``Parser.Attr.simple &&
    attr[1][0].getId.eraseMacroScopes == `inherit_doc

def declModifiersPubNoDoc (mods : Syntax) : Bool :=
  mods[2][0].getKind != ``Command.private && mods[0].isNone && !hasInheritDoc mods[1]

def lintDeclHead (k : SyntaxNodeKind) (id : Syntax) : CommandElabM Unit := do
  if k == ``«abbrev» then lintNamed id "public abbrev"
  else if k == ``definition then lintNamed id "public def"
  else if k == ``«opaque» then lintNamed id "public opaque"
  else if k == ``«axiom» then lintNamed id "public axiom"
  else if k == ``«inductive» then lintNamed id "public inductive"
  else if k == ``classInductive then lintNamed id "public inductive"
  else if k == ``«structure» then lintNamed id "public structure"

@[builtin_missing_docs_handler declaration]
def checkDecl : SimpleHandler := fun stx => do
  let head := stx[0]; let rest := stx[1]
  if head[2][0].getKind == ``Command.private then return -- not private
  let k := rest.getKind
  if declModifiersPubNoDoc head then -- no doc string
    lintDeclHead k rest[1][0]
  if k == ``«inductive» || k == ``classInductive then
    for stx in rest[4].getArgs do
      let head := stx[2]
      if stx[0].isNone && declModifiersPubNoDoc head then
        lintField rest[1][0] stx[3] "public constructor"
    unless rest[5].isNone do
      for stx in rest[5][0][1].getArgs do
        let head := stx[0]
        if declModifiersPubNoDoc head then -- no doc string
          lintField rest[1][0] stx[1] "computed field"
  else if rest.getKind == ``«structure» then
    unless rest[4][2].isNone do
      let redecls : Std.HashSet String.Pos :=
        (← get).infoState.trees.foldl (init := {}) fun s tree =>
          tree.foldInfo (init := s) fun _ info s =>
            if let .ofFieldRedeclInfo info := info then
              if let some range := info.stx.getRange? then
                s.insert range.start
              else s
            else s
      let parent := rest[1][0]
      let lint1 stx := do
        if let some range := stx.getRange? then
          if redecls.contains range.start then return
        lintField parent stx "public field"
      for stx in rest[4][2][0].getArgs do
        let head := stx[0]
        if declModifiersPubNoDoc head then
          if stx.getKind == ``structSimpleBinder then
            lint1 stx[1]
          else
            for stx in stx[2].getArgs do
              lint1 stx

@[builtin_missing_docs_handler «initialize»]
def checkInit : SimpleHandler := fun stx => do
  if !stx[2].isNone && declModifiersPubNoDoc stx[0] then
    lintNamed stx[2][0] "initializer"

@[builtin_missing_docs_handler «notation»]
def checkNotation : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» && !hasInheritDoc stx[1] then
    if stx[5].isNone then lint stx[3] "notation"
    else lintNamed stx[5][0][3] "notation"

@[builtin_missing_docs_handler «mixfix»]
def checkMixfix : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» && !hasInheritDoc stx[1] then
    if stx[5].isNone then lint stx[3] stx[3][0].getAtomVal
    else lintNamed stx[5][0][3] stx[3][0].getAtomVal

@[builtin_missing_docs_handler «syntax»]
def checkSyntax : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» && !hasInheritDoc stx[1] then
    if stx[5].isNone then lint stx[3] "syntax"
    else lintNamed stx[5][0][3] "syntax"

def mkSimpleHandler (name : String) : SimpleHandler := fun stx => do
  if stx[0].isNone then
    lintNamed stx[2] name

@[builtin_missing_docs_handler syntaxAbbrev]
def checkSyntaxAbbrev : SimpleHandler := mkSimpleHandler "syntax"

@[builtin_missing_docs_handler syntaxCat]
def checkSyntaxCat : SimpleHandler := mkSimpleHandler "syntax category"

@[builtin_missing_docs_handler «macro»]
def checkMacro : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» && !hasInheritDoc stx[1] then
    if stx[5].isNone then lint stx[3] "macro"
    else lintNamed stx[5][0][3] "macro"

@[builtin_missing_docs_handler «elab»]
def checkElab : SimpleHandler := fun stx => do
  if stx[0].isNone && stx[2][0][0].getKind != ``«local» && !hasInheritDoc stx[1] then
    if stx[5].isNone then lint stx[3] "elab"
    else lintNamed stx[5][0][3] "elab"

@[builtin_missing_docs_handler classAbbrev]
def checkClassAbbrev : SimpleHandler := fun stx => do
  if declModifiersPubNoDoc stx[0] then
    lintNamed stx[3] "class abbrev"

@[builtin_missing_docs_handler Parser.Tactic.declareSimpLikeTactic]
def checkSimpLike : SimpleHandler := mkSimpleHandler "simp-like tactic"

@[builtin_missing_docs_handler Option.registerBuiltinOption]
def checkRegisterBuiltinOption : SimpleHandler := mkSimpleHandler "option"

@[builtin_missing_docs_handler Option.registerOption]
def checkRegisterOption : SimpleHandler := mkSimpleHandler "option"

@[builtin_missing_docs_handler registerSimpAttr]
def checkRegisterSimpAttr : SimpleHandler := mkSimpleHandler "simp attr"

@[builtin_missing_docs_handler «in»]
def handleIn : Handler := fun _ stx => do
  if stx[0].getKind == ``«set_option» then
    let opts ← Elab.elabSetOption stx[0][1] stx[0][3]
    withScope (fun scope => { scope with opts }) do
      missingDocs.run stx[2]
  else
    missingDocs.run stx[2]

@[builtin_missing_docs_handler «mutual»]
def handleMutual : Handler := fun _ stx => do
  stx[1].getArgs.forM missingDocs.run
