/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Trace
import Lean.Parser.Syntax
import Lean.Parser.Extension
import Lean.KeyedDeclsAttribute
import Lean.Elab.Exception

namespace Lean

def Syntax.prettyPrint (stx : Syntax) : Format :=
  match stx.unsetTrailing.reprint with -- TODO use syntax pretty printer
  | some str => format str.toFormat
  | none     => format stx

def MacroScopesView.format (view : MacroScopesView) (mainModule : Name) : Format :=
  Std.format $
    if view.scopes.isEmpty then
      view.name
    else if view.mainModule == mainModule then
      view.scopes.foldl Name.mkNum (view.name ++ view.imported)
    else
      view.scopes.foldl Name.mkNum (view.name ++ view.imported ++ view.mainModule)

namespace Elab

def expandOptNamedPrio (stx : Syntax) : MacroM Nat :=
  if stx.isNone then
    return eval_prio default
  else match stx[0] with
    | `(Parser.Command.namedPrio| (priority := $prio)) => evalPrio prio
    | _ => Macro.throwUnsupported

structure MacroStackElem where
  before : Syntax
  after : Syntax

abbrev MacroStack := List MacroStackElem

/- If `ref` does not have position information, then try to use macroStack -/
def getBetterRef (ref : Syntax) (macroStack : MacroStack) : Syntax :=
  match ref.getPos? with
  | some _ => ref
  | none   =>
    match macroStack.find? (·.before.getPos? != none) with
    | some elem => elem.before
    | none      => ref

register_builtin_option pp.macroStack : Bool := {
  defValue := false
  group    := "pp"
  descr    := "dispaly macro expansion stack"
}

def addMacroStack {m} [Monad m] [MonadOptions m] (msgData : MessageData) (macroStack : MacroStack) : m MessageData := do
  if !pp.macroStack.get (← getOptions) then pure msgData else
  match macroStack with
  | []             => pure msgData
  | stack@(top::_) =>
    let msgData := msgData ++ Format.line ++ "with resulting expansion" ++ indentD top.after
    pure $ stack.foldl
      (fun (msgData : MessageData) (elem : MacroStackElem) =>
        msgData ++ Format.line ++ "while expanding" ++ indentD elem.before)
      msgData

def checkSyntaxNodeKind [Monad m] [MonadEnv m] [MonadError m] (k : Name) : m Name := do
  if Parser.isValidSyntaxNodeKind (← getEnv) k then pure k
  else throwError "failed"

def checkSyntaxNodeKindAtNamespaces [Monad m] [MonadEnv m] [MonadError m] (k : Name) : Name → m Name
  | n@(Name.str p _ _) => checkSyntaxNodeKind (n ++ k) <|> checkSyntaxNodeKindAtNamespaces k p
  | Name.anonymous     => checkSyntaxNodeKind k
  | _ => throwError "failed"

def checkSyntaxNodeKindAtCurrentNamespaces (k : Name) : AttrM Name := do
  let ctx ← read
  checkSyntaxNodeKindAtNamespaces k ctx.currNamespace

def syntaxNodeKindOfAttrParam (defaultParserNamespace : Name) (stx : Syntax) : AttrM SyntaxNodeKind := do
  let k ← Attribute.Builtin.getId stx
  checkSyntaxNodeKindAtCurrentNamespaces k
  <|>
  checkSyntaxNodeKind (defaultParserNamespace ++ k)
  <|>
  throwError "invalid syntax node kind '{k}'"

private unsafe def evalSyntaxConstantUnsafe (env : Environment) (opts : Options) (constName : Name) : ExceptT String Id Syntax :=
  env.evalConstCheck Syntax opts `Lean.Syntax constName

@[implementedBy evalSyntaxConstantUnsafe]
constant evalSyntaxConstant (env : Environment) (opts : Options) (constName : Name) : ExceptT String Id Syntax := throw ""

unsafe def mkElabAttribute (γ) (attrDeclName attrBuiltinName attrName : Name) (parserNamespace : Name) (typeName : Name) (kind : String)
    : IO (KeyedDeclsAttribute γ) :=
  KeyedDeclsAttribute.init {
    builtinName   := attrBuiltinName
    name          := attrName
    descr         := kind ++ " elaborator"
    valueTypeName := typeName
    evalKey       := fun _ stx => syntaxNodeKindOfAttrParam parserNamespace stx
  } attrDeclName

unsafe def mkMacroAttributeUnsafe : IO (KeyedDeclsAttribute Macro) :=
  mkElabAttribute Macro `Lean.Elab.macroAttribute `builtinMacro `macro Name.anonymous `Lean.Macro "macro"

@[implementedBy mkMacroAttributeUnsafe]
constant mkMacroAttribute : IO (KeyedDeclsAttribute Macro)

builtin_initialize macroAttribute : KeyedDeclsAttribute Macro ← mkMacroAttribute

/--
Try to expand macro at syntax tree root and return macro declaration name and new syntax if successful.
Return none if all macros threw `Macro.Exception.unsupportedSyntax`.
-/
def expandMacroImpl? (env : Environment) : Syntax → MacroM (Option (Name × Syntax)) := fun stx => do
  for e in macroAttribute.getEntries env stx.getKind do
    try
      let stx' ← e.value stx
      return (e.declName, stx')
    catch
      | Macro.Exception.unsupportedSyntax => pure ()
      | ex                                => throw ex
  return none

class MonadMacroAdapter (m : Type → Type) where
  getCurrMacroScope                  : m MacroScope
  getNextMacroScope                  : m MacroScope
  setNextMacroScope                  : MacroScope → m Unit

instance (m n) [MonadLift m n] [MonadMacroAdapter m] : MonadMacroAdapter n := {
  getCurrMacroScope := liftM (MonadMacroAdapter.getCurrMacroScope : m _),
  getNextMacroScope := liftM (MonadMacroAdapter.getNextMacroScope : m _),
  setNextMacroScope := fun s => liftM (MonadMacroAdapter.setNextMacroScope s : m _)
}

def liftMacroM {α} {m : Type → Type} [Monad m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m] [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (x : MacroM α) : m α := do
  let env  ← getEnv
  let currNamespace ← getCurrNamespace
  let openDecls ← getOpenDecls
  let methods := Macro.mkMethods {
    -- TODO: record recursive expansions in info tree?
    expandMacro?     := fun stx => do
      match (← expandMacroImpl? env stx) with
      | some (_, stx) => some stx
      | none          => none
    hasDecl          := fun declName => return env.contains declName
    getCurrNamespace := return currNamespace
    resolveNamespace? := fun n => return ResolveName.resolveNamespace? env currNamespace openDecls n
    resolveGlobalName := fun n => return ResolveName.resolveGlobalName env currNamespace openDecls n
  }
  match x { methods        := methods
            ref            := ← getRef
            currMacroScope := ← MonadMacroAdapter.getCurrMacroScope
            mainModule     := env.mainModule
            currRecDepth   := ← MonadRecDepth.getRecDepth
            maxRecDepth    := ← MonadRecDepth.getMaxRecDepth
          } { macroScope := (← MonadMacroAdapter.getNextMacroScope) } with
  | EStateM.Result.error Macro.Exception.unsupportedSyntax _ => throwUnsupportedSyntax
  | EStateM.Result.error (Macro.Exception.error ref msg) _   => throwErrorAt ref msg
  | EStateM.Result.ok a  s                                   =>
    MonadMacroAdapter.setNextMacroScope s.macroScope
    s.traceMsgs.reverse.forM fun (clsName, msg) => trace clsName fun _ => msg
    pure a

@[inline] def adaptMacro {m : Type → Type} [Monad m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m]  [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] (x : Macro) (stx : Syntax) : m Syntax :=
  liftMacroM (x stx)

partial def mkUnusedBaseName (baseName : Name) : MacroM Name := do
  let currNamespace ← Macro.getCurrNamespace
  if ← Macro.hasDecl (currNamespace ++ baseName) then
    let rec loop (idx : Nat) := do
       let name := baseName.appendIndexAfter idx
       if ← Macro.hasDecl (currNamespace ++ name) then
         loop (idx+1)
       else
         name
    loop 1
  else
    return baseName

builtin_initialize
  registerTraceClass `Elab
  registerTraceClass `Elab.step

end Lean.Elab
