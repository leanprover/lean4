/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Util.Trace
import Init.Lean.Parser

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

structure ElabAttributeOLeanEntry :=
(kind      : SyntaxNodeKind)
(constName : Name)

structure ElabAttributeEntry (γ : Type) extends ElabAttributeOLeanEntry :=
(elabFn   : γ)

abbrev ElabFnTable (γ : Type) := SMap SyntaxNodeKind (List γ)

def ElabFnTable.insert {γ} (table : ElabFnTable γ) (k : SyntaxNodeKind) (f : γ) : ElabFnTable γ :=
match table.find? k with
| some fs => table.insert k (f::fs)
| none    => table.insert k [f]

structure ElabAttributeExtensionState (γ : Type) :=
(newEntries : List ElabAttributeOLeanEntry := [])
(table      : ElabFnTable γ                := {})

instance ElabAttributeExtensionState.inhabited (γ) : Inhabited (ElabAttributeExtensionState γ) :=
⟨{}⟩

abbrev ElabAttributeExtension (γ) := PersistentEnvExtension ElabAttributeOLeanEntry (ElabAttributeEntry γ) (ElabAttributeExtensionState γ)

structure ElabAttribute (γ : Type) :=
(attr : AttributeImpl)
(ext  : ElabAttributeExtension γ)
(kind : String)

instance ElabAttribute.inhabited {γ} : Inhabited (ElabAttribute γ) := ⟨{ attr := arbitrary _, ext := arbitrary _, kind := "" }⟩

private def ElabAttribute.mkInitial {γ} (builtinTableRef : IO.Ref (ElabFnTable γ)) : IO (ElabAttributeExtensionState γ) := do
table ← builtinTableRef.get;
pure { table := table }

private def throwUnexpectedElabType {γ} (typeName : Name) (constName : Name) : ExceptT String Id γ :=
throw ("unexpected elaborator type at '" ++ toString constName ++ "', `" ++ toString typeName ++ "` expected")

private unsafe def mkElabFnOfConstantUnsafe (γ) (env : Environment) (typeName : Name) (constName : Name) : ExceptT String Id γ :=
match env.find? constName with
| none      => throw ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  match info.type with
  | Expr.const c _ _ =>
    if c != typeName then throwUnexpectedElabType typeName constName
    else env.evalConst γ constName
  | _ => throwUnexpectedElabType typeName constName

@[implementedBy mkElabFnOfConstantUnsafe]
constant mkElabFnOfConstant (γ : Type) (env : Environment) (typeName : Name) (constName : Name) : ExceptT String Id γ := throw ""

private def ElabAttribute.addImportedParsers {γ} (typeName : Name) (builtinTableRef : IO.Ref (ElabFnTable γ))
    (env : Environment) (es : Array (Array ElabAttributeOLeanEntry)) : IO (ElabAttributeExtensionState γ) := do
table ← builtinTableRef.get;
table ← es.foldlM
  (fun table entries =>
    entries.foldlM
      (fun (table : ElabFnTable γ) entry =>
        match mkElabFnOfConstant γ env typeName entry.constName with
        | Except.ok f     => pure $ table.insert entry.kind f
        | Except.error ex => throw (IO.userError ex))
      table)
  table;
pure { table := table }

private def ElabAttribute.addExtensionEntry {γ} (s : ElabAttributeExtensionState γ) (e : ElabAttributeEntry γ) : ElabAttributeExtensionState γ :=
{ table := s.table.insert e.kind e.elabFn, newEntries := e.toElabAttributeOLeanEntry :: s.newEntries }

private def ElabAttribute.add {γ} (parserNamespace : Name) (typeName : Name) (ext : ElabAttributeExtension γ)
    (env : Environment) (constName : Name) (arg : Syntax) (persistent : Bool) : IO Environment := do
match mkElabFnOfConstant γ env typeName constName with
| Except.error ex => throw (IO.userError ex)
| Except.ok f     => do
  kind ← IO.ofExcept $ syntaxNodeKindOfAttrParam env parserNamespace arg;
  pure $ ext.addEntry env { kind := kind, elabFn := f, constName := constName }

/- TODO: add support for scoped attributes -/
def mkElabAttributeAux (γ) (attrName : Name) (parserNamespace : Name) (typeName : Name) (descr : String) (kind : String) (builtinTableRef : IO.Ref (ElabFnTable γ))
    : IO (ElabAttribute γ) := do
ext : ElabAttributeExtension γ ← registerPersistentEnvExtension {
  name            := attrName,
  mkInitial       := ElabAttribute.mkInitial builtinTableRef,
  addImportedFn   := ElabAttribute.addImportedParsers typeName builtinTableRef,
  addEntryFn      := ElabAttribute.addExtensionEntry,
  exportEntriesFn := fun s => s.newEntries.reverse.toArray,
  statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
};
let attrImpl : AttributeImpl := {
  name            := attrName,
  descr           := kind ++ " elaborator",
  add             := ElabAttribute.add parserNamespace typeName ext,
  applicationTime := AttributeApplicationTime.afterCompilation
};
registerBuiltinAttribute attrImpl;
pure { ext := ext, attr := attrImpl, kind := kind }

def mkElabAttribute (γ) (attrName : Name) (parserNamespace : Name) (typeName : Name) (kind : String) (builtinTableRef : IO.Ref (ElabFnTable γ))
    : IO (ElabAttribute γ) :=
mkElabAttributeAux γ attrName parserNamespace typeName (kind ++ " elaborator") kind builtinTableRef

abbrev MacroAttribute               := ElabAttribute Macro
abbrev MacroFnTable                 := ElabFnTable Macro

def mkBuiltinMacroFnTable : IO (IO.Ref MacroFnTable) :=  IO.mkRef {}
@[init mkBuiltinMacroFnTable] constant builtinMacroFnTable : IO.Ref MacroFnTable := arbitrary _

def addBuiltinMacro (k : SyntaxNodeKind) (macro : Macro) : IO Unit := do
m ← builtinMacroFnTable.get;
builtinMacroFnTable.modify $ fun m => m.insert k macro

def declareBuiltinMacro (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
let name := `_regBuiltinMacro ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst `Lean.Elab.addBuiltinMacro) #[toExpr kind, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin macro '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

@[init] def registerBuiltinMacroAttr : IO Unit :=
registerBuiltinAttribute {
 name  := `builtinMacro,
 descr := "Builtin macro",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinMacro', must be persistent"));
   kind ← IO.ofExcept $ syntaxNodeKindOfAttrParam env `Lean.Parser.Term arg;
   match env.find? declName with
   | none  => throw $ IO.userError "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.Macro _ _ => declareBuiltinMacro env kind declName
     | _ => throw (IO.userError ("unexpected macro type at '" ++ toString declName ++ "' `Macro` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

def mkMacroAttribute : IO MacroAttribute :=
mkElabAttributeAux Macro `macro Name.anonymous `Lean.Macro "macros" "macro" builtinMacroFnTable

@[init mkMacroAttribute] constant macroAttribute : MacroAttribute := arbitrary _

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

@[inline] def adaptMacro {m : Type → Type} [Monad m] [MonadMacroAdapter m] (x : Macro) (stx : Syntax) : m Syntax := do
scp  ← MonadMacroAdapter.getCurrMacroScope;
env  ← MonadMacroAdapter.getEnv;
next ← MonadMacroAdapter.getNextMacroScope;
match x stx { currMacroScope := scp, mainModule := env.mainModule } next with
| EStateM.Result.error Macro.Exception.unsupportedSyntax _ => MonadMacroAdapter.throwUnsupportedSyntax
| EStateM.Result.error (Macro.Exception.error msg) _       => MonadMacroAdapter.throwError stx msg
| EStateM.Result.ok stx nextMacroScope                     => do MonadMacroAdapter.setNextMacroScope nextMacroScope; pure stx

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab;
registerTraceClass `Elab.step

end Elab
end Lean
