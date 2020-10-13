/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Trace
import Lean.Parser.Extension
import Lean.KeyedDeclsAttribute
import Lean.Elab.Exception
new_frontend

namespace Lean

def Syntax.prettyPrint (stx : Syntax) : Format :=
match stx.unsetTrailing.reprint with -- TODO use syntax pretty printer
| some str => format str.toFormat
| none     => format stx

def MacroScopesView.format (view : MacroScopesView) (mainModule : Name) : Format :=
fmt $
  if view.scopes.isEmpty then
    view.name
  else if view.mainModule == mainModule then
    view.scopes.foldl mkNameNum (view.name ++ view.imported)
  else
    view.scopes.foldl mkNameNum (view.name ++ view.imported ++ view.mainModule)

namespace Elab

structure MacroStackElem :=
(before : Syntax) (after : Syntax)

abbrev MacroStack := List MacroStackElem

/- If `ref` does not have position information, then try to use macroStack -/
def getBetterRef (ref : Syntax) (macroStack : MacroStack) : Syntax :=
match ref.getPos with
| some _ => ref
| none   =>
  match macroStack.find? (·.before.getPos != none) with
  | some elem => elem.before
  | none      => ref

def ppMacroStackDefault := false
def getMacroStackOption (o : Options) : Bool:= o.get `pp.macroStack ppMacroStackDefault
def setMacroStackOption (o : Options) (flag : Bool) : Options := o.setBool `pp.macroStack flag
initialize
  registerOption `pp.macroStack { defValue := ppMacroStackDefault, group := "pp", descr := "dispaly macro expansion stack" }

def addMacroStack {m} [Monad m] [MonadOptions m] (msgData : MessageData) (macroStack : MacroStack) : m MessageData := do
if !getMacroStackOption (← getOptions) then pure msgData else
match macroStack with
| []             => pure msgData
| stack@(top::_) =>
  let msgData := msgData ++ Format.line ++ "with resulting expansion" ++ MessageData.nest 2 (Format.line ++ top.after)
  pure $ stack.foldl
    (fun (msgData : MessageData) (elem : MacroStackElem) =>
      msgData ++ Format.line ++ "while expanding" ++ MessageData.nest 2 (Format.line ++ elem.before))
    msgData

def checkSyntaxNodeKind (k : Name) : AttrM Name := do
if Parser.isValidSyntaxNodeKind (← getEnv) k then pure k
else throwError "failed"

namespace OldFrontend -- TODO: delete

private def checkSyntaxNodeKindAtNamespacesAux (k : Name) : List Name → AttrM Name
| []    => throwError "failed"
| n::ns => checkSyntaxNodeKind (n ++ k) <|> checkSyntaxNodeKindAtNamespacesAux k ns

def checkSyntaxNodeKindAtNamespaces (k : Name) : AttrM Name := do
let env ← getEnv
checkSyntaxNodeKindAtNamespacesAux k (Lean.TODELETE.getNamespaces env)

end OldFrontend

def checkSyntaxNodeKindAtNamespacesAux (k : Name) : Name → AttrM Name
| n@(Name.str p _ _) => checkSyntaxNodeKind (n ++ k) <|> checkSyntaxNodeKindAtNamespacesAux k p
| _ => throwError "failed"

def checkSyntaxNodeKindAtNamespaces (k : Name) : AttrM Name := do
let ctx ← read
checkSyntaxNodeKindAtNamespacesAux k ctx.currNamespace

def syntaxNodeKindOfAttrParam (defaultParserNamespace : Name) (arg : Syntax) : AttrM SyntaxNodeKind :=
match attrParamSyntaxToIdentifier arg with
| some k =>
  checkSyntaxNodeKind k
  <|>
  checkSyntaxNodeKindAtNamespaces k
  <|>
  OldFrontend.checkSyntaxNodeKindAtNamespaces k -- TODO: delete the following old frontend support code
  <|>
  checkSyntaxNodeKind (defaultParserNamespace ++ k)
  <|>
  throwError! "invalid syntax node kind '{k}'"
| none   => throwError "syntax node kind is missing"

private unsafe def evalSyntaxConstantUnsafe (env : Environment) (constName : Name) : ExceptT String Id Syntax :=
env.evalConstCheck Syntax `Lean.Syntax constName

@[implementedBy evalSyntaxConstantUnsafe]
constant evalSyntaxConstant (env : Environment) (constName : Name) : ExceptT String Id Syntax := throw ""

private constant evalConstant (γ : Type) (env : Environment) (typeName : Name) (constName : Name) : ExceptT String Id γ := throw ""

unsafe def mkElabAttribute (γ) (attrDeclName attrBuiltinName attrName : Name) (parserNamespace : Name) (typeName : Name) (kind : String)
    : IO (KeyedDeclsAttribute γ) :=
KeyedDeclsAttribute.init {
  builtinName   := attrBuiltinName,
  name          := attrName,
  descr         := kind ++ " elaborator",
  valueTypeName := typeName,
  evalKey       := fun _ arg => syntaxNodeKindOfAttrParam parserNamespace arg,
} attrDeclName

unsafe def mkMacroAttributeUnsafe : IO (KeyedDeclsAttribute Macro) :=
mkElabAttribute Macro `Lean.Elab.macroAttribute `builtinMacro `macro Name.anonymous `Lean.Macro "macro"

@[implementedBy mkMacroAttributeUnsafe]
constant mkMacroAttribute : IO (KeyedDeclsAttribute Macro) := arbitrary _

initialize macroAttribute : KeyedDeclsAttribute Macro ← mkMacroAttribute

private def expandMacroFns (stx : Syntax) : List Macro → MacroM Syntax
| []    => throw Macro.Exception.unsupportedSyntax
| m::ms => do
  try
    m stx
  catch
    | Macro.Exception.unsupportedSyntax => expandMacroFns stx ms
    | ex                                => throw ex

def getMacros (env : Environment) : Macro :=
fun stx =>
  let k := stx.getKind
  let table := (macroAttribute.ext.getState env).table
  match table.find? k with
  | some macroFns => expandMacroFns stx macroFns
  | none          => throw Macro.Exception.unsupportedSyntax

class MonadMacroAdapter (m : Type → Type) :=
(getCurrMacroScope                  : m MacroScope)
(getNextMacroScope                  : m MacroScope)
(setNextMacroScope                  : MacroScope → m Unit)

instance monadMacroAdapterTrans (m n) [MonadMacroAdapter m] [MonadLift m n] : MonadMacroAdapter n :=
{ getCurrMacroScope := liftM (MonadMacroAdapter.getCurrMacroScope : m _),
  getNextMacroScope := liftM (MonadMacroAdapter.getNextMacroScope : m _),
  setNextMacroScope := fun s => liftM (MonadMacroAdapter.setNextMacroScope s : m _) }

private def expandMacro? (env : Environment) (stx : Syntax) : MacroM (Option Syntax) := do
try
  let newStx ← getMacros env stx
  pure (some newStx)
catch
  | Macro.Exception.unsupportedSyntax => pure none
  | ex                                => throw ex

@[inline] def liftMacroM {α} {m : Type → Type} [Monad m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m]
    [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (x : MacroM α) : m α := do
let env  ← getEnv
match x { macroEnv       := Macro.mkMacroEnv (expandMacro? env),
          currMacroScope := ← MonadMacroAdapter.getCurrMacroScope,
          mainModule     := env.mainModule,
          currRecDepth   := ← MonadRecDepth.getRecDepth,
          maxRecDepth    := ← MonadRecDepth.getMaxRecDepth } (← MonadMacroAdapter.getNextMacroScope) with
| EStateM.Result.error Macro.Exception.unsupportedSyntax _ => throwUnsupportedSyntax
| EStateM.Result.error (Macro.Exception.error ref msg) _   => throwErrorAt ref msg
| EStateM.Result.ok a nextMacroScope                       => MonadMacroAdapter.setNextMacroScope nextMacroScope; pure a

@[inline] def adaptMacro {m : Type → Type} [Monad m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m]
    [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (x : Macro) (stx : Syntax) : m Syntax :=
liftMacroM (x stx)

initialize
  registerTraceClass `Elab
  registerTraceClass `Elab.step

end Lean.Elab
