/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Util.Trace
import Init.Lean.Parser
import Init.Lean.KeyedDeclsAttribute

namespace Lean

def Syntax.prettyPrint (stx : Syntax) : Format :=
match stx.truncateTrailing.reprint with -- TODO use syntax pretty printer
| some str => format str.toFormat
| none     => format stx

def MacroScopesView.format (view : MacroScopesView) (mainModule : Name) : Format :=
format $
  if view.scopes.isEmpty then view.name
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
  match macroStack.find? $ fun (elem : MacroStackElem) => elem.before.getPos != none with
  | some elem => elem.before
  | none      => ref

def addMacroStack (msgData : MessageData) (macroStack : MacroStack) : MessageData :=
match macroStack with
| []             => msgData
| stack@(top::_) =>
  let topFmt  := top.after.prettyPrint;
  let msgData := msgData ++ Format.line ++ "with resulting expansion" ++ MessageData.nest 2 (Format.line ++ topFmt);
  stack.foldl
    (fun (msgData : MessageData) (elem : MacroStackElem) =>
      let macroFmt := elem.before.prettyPrint;
      msgData ++ Format.line ++ "while expanding" ++ MessageData.nest 2 (Format.line ++ macroFmt))
    msgData

def checkSyntaxNodeKind (env : Environment) (k : Name) : ExceptT String Id Name :=
if Parser.isValidSyntaxNodeKind env k then pure k
else throw "failed"

def checkSyntaxNodeKindAtNamespaces (env : Environment) (k : Name) : List Name → ExceptT String Id Name
| []    => throw "failed"
| n::ns => checkSyntaxNodeKind env (n ++ k) <|> checkSyntaxNodeKindAtNamespaces ns

def syntaxNodeKindOfAttrParam (env : Environment) (defaultParserNamespace : Name) (arg : Syntax) : ExceptT String Id SyntaxNodeKind :=
match attrParamSyntaxToIdentifier arg with
| some k =>
  checkSyntaxNodeKind env k
  <|>
  checkSyntaxNodeKindAtNamespaces env k env.getNamespaces
  <|>
  checkSyntaxNodeKind env (defaultParserNamespace ++ k)
  <|>
  throw ("invalid syntax node kind '" ++ toString k ++ "'")
| none   => throw ("syntax node kind is missing")

private unsafe def evalSyntaxConstantUnsafe (env : Environment) (constName : Name) : ExceptT String Id Syntax :=
env.evalConstCheck Syntax `Lean.Syntax constName

@[implementedBy evalSyntaxConstantUnsafe]
constant evalSyntaxConstant (env : Environment) (constName : Name) : ExceptT String Id Syntax := throw ""

private constant evalConstant (γ : Type) (env : Environment) (typeName : Name) (constName : Name) : ExceptT String Id γ := throw ""

unsafe def mkElabAttribute (γ) (attrDeclName attrBuiltinName attrName : Name) (parserNamespace : Name) (typeName : Name) (kind : String)
    : IO (KeyedDeclsAttribute γ) :=
KeyedDeclsAttribute.init {
  builtinName := attrBuiltinName,
  name := attrName,
  descr := kind ++ " elaborator",
  valueTypeName := typeName,
  evalKey := fun env arg => syntaxNodeKindOfAttrParam env parserNamespace arg,
} attrDeclName

unsafe def mkMacroAttribute : IO (KeyedDeclsAttribute Macro) :=
mkElabAttribute Macro `Lean.Elab.macroAttribute `builtinMacro `macro Name.anonymous `Lean.Macro "macro"
@[init mkMacroAttribute] constant macroAttribute : KeyedDeclsAttribute Macro := arbitrary _

-- TODO: remove after bootstrap
def addBuiltinMacro (k : SyntaxNodeKind) (elab : Macro) : IO Unit := do
KeyedDeclsAttribute.addBuiltin macroAttribute k elab

private def expandMacroFns (stx : Syntax) : List Macro → MacroM Syntax
| []    => throw Macro.Exception.unsupportedSyntax
| m::ms => m stx <|> expandMacroFns ms

def getMacros (env : Environment) : Macro :=
fun stx =>
  let k := stx.getKind;
  let table := (macroAttribute.ext.getState env).table;
  match table.find? k with
  | some macroFns => expandMacroFns stx macroFns
  | none          => throw Macro.Exception.unsupportedSyntax

class MonadMacroAdapter (m : Type → Type) :=
(getEnv {}                            : m Environment)
(getCurrMacroScope {}                 : m MacroScope)
(getNextMacroScope {}                 : m MacroScope)
(setNextMacroScope {}                 : MacroScope → m Unit)
(throwError {} {α : Type}             : Syntax → MessageData → m α)
(throwUnsupportedSyntax {} {α : Type} : m α)

@[inline] def liftMacroM {α} {m : Type → Type} [Monad m] [MonadMacroAdapter m] (x : MacroM α) : m α := do
scp  ← MonadMacroAdapter.getCurrMacroScope;
env  ← MonadMacroAdapter.getEnv;
next ← MonadMacroAdapter.getNextMacroScope;
match x { currMacroScope := scp, mainModule := env.mainModule } next with
| EStateM.Result.error Macro.Exception.unsupportedSyntax _ => MonadMacroAdapter.throwUnsupportedSyntax
| EStateM.Result.error (Macro.Exception.error ref msg) _   => MonadMacroAdapter.throwError ref msg
| EStateM.Result.ok a nextMacroScope                       => do MonadMacroAdapter.setNextMacroScope nextMacroScope; pure a

@[inline] def adaptMacro {m : Type → Type} [Monad m] [MonadMacroAdapter m] (x : Macro) (stx : Syntax) : m Syntax :=
liftMacroM (x stx)

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab;
registerTraceClass `Elab.step

end Elab
end Lean
