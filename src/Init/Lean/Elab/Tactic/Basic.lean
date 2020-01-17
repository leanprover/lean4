/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Util
import Init.Lean.Elab.Term

namespace Lean
namespace Elab
namespace Tactic

structure Context extends toTermCtx : Term.Context :=
(main : Expr)
(ref  : Syntax)

structure State extends toTermState : Term.State :=
(goals : List Expr)

instance State.inhabited : Inhabited State := ⟨{ goals := [], toTermState := arbitrary _ }⟩

abbrev Exception := Elab.Exception

abbrev TacticElabM := ReaderT Context (EStateM Exception State)

abbrev TacticElab := Syntax → TacticElabM Unit

def liftTermElabM {α} (x : TermElabM α) : TacticElabM α :=
fun ctx s => match x ctx.toTermCtx s.toTermState with
 | EStateM.Result.ok a newS                         => EStateM.Result.ok a { toTermState := newS, .. s }
 | EStateM.Result.error (Term.Exception.ex ex) newS => EStateM.Result.error ex { toTermState := newS, .. s }
 | EStateM.Result.error Term.Exception.postpone _   => unreachable!

def getEnv : TacticElabM Environment := do s ← get; pure s.env
def getMCtx : TacticElabM MetavarContext := do s ← get; pure s.mctx
def getLCtx : TacticElabM LocalContext := do ctx ← read; pure ctx.lctx
def getLocalInsts : TacticElabM LocalInstances := do ctx ← read; pure ctx.localInstances
def getOptions : TacticElabM Options := do ctx ← read; pure ctx.config.opts

def addContext (msg : MessageData) : TacticElabM MessageData := liftTermElabM $ Term.addContext msg

instance monadLog : MonadLog TacticElabM :=
{ getCmdPos   := do ctx ← read; pure ctx.cmdPos,
  getFileMap  := do ctx ← read; pure ctx.fileMap,
  getFileName := do ctx ← read; pure ctx.fileName,
  addContext  := addContext,
  logMessage  := fun msg => modify $ fun s => { messages := s.messages.add msg, .. s } }

def throwError {α} (ref : Syntax) (msgData : MessageData) : TacticElabM α := do
ref ← if ref.getPos.isNone then do ctx ← read; pure ctx.ref else pure ref;
liftTermElabM $ Term.throwError ref msgData

def throwUnsupportedSyntax {α} : TacticElabM α := liftTermElabM $ Term.throwUnsupportedSyntax

@[inline] def withIncRecDepth {α} (ref : Syntax) (x : TacticElabM α) : TacticElabM α := do
ctx ← read;
when (ctx.currRecDepth == ctx.maxRecDepth) $ throwError ref maxRecDepthErrorMessage;
adaptReader (fun (ctx : Context) => { currRecDepth := ctx.currRecDepth + 1, .. ctx }) x

protected def getCurrMacroScope : TacticElabM MacroScope := do ctx ← read; pure ctx.currMacroScope

@[inline] protected def withFreshMacroScope {α} (x : TacticElabM α) : TacticElabM α := do
fresh ← modifyGet (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }));
adaptReader (fun (ctx : Context) => { ctx with currMacroScope := fresh }) x

instance monadQuotation : MonadQuotation TacticElabM := {
  getCurrMacroScope   := Tactic.getCurrMacroScope,
  withFreshMacroScope := @Tactic.withFreshMacroScope
}

abbrev TacticElabTable := ElabFnTable TacticElab
def mkBuiltinTacticElabTable : IO (IO.Ref TacticElabTable) :=  IO.mkRef {}
@[init mkBuiltinTacticElabTable] constant builtinTacticElabTable : IO.Ref TacticElabTable := arbitrary _

def addBuiltinTacticElab (k : SyntaxNodeKind) (declName : Name) (elab : TacticElab) : IO Unit := do
m ← builtinTacticElabTable.get;
when (m.contains k) $
  throw (IO.userError ("invalid builtin tactic elaborator, elaborator for '" ++ toString k ++ "' has already been defined"));
builtinTacticElabTable.modify $ fun m => m.insert k elab

def declareBuiltinTacticElab (env : Environment) (kind : SyntaxNodeKind) (declName : Name) : IO Environment :=
let name := `_regBuiltinTacticElab ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst `Lean.Elab.Tactic.addBuiltinTacticElab) #[toExpr kind, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin tactic elaborator '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

@[init] def registerBuiltinTacticElabAttr : IO Unit :=
registerBuiltinAttribute {
 name  := `builtinTacticElab,
 descr := "Builtin tactic elaborator",
 add   := fun env declName arg persistent => do {
   unless persistent $ throw (IO.userError ("invalid attribute 'builtinTacticElab', must be persistent"));
   kind ← IO.ofExcept $ syntaxNodeKindOfAttrParam env `Lean.Parser.Tactic arg;
   match env.find? declName with
   | none  => throw $ IO.userError "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.Elab.Tactic.TacticElab _ _ => declareBuiltinTacticElab env kind declName
     | _ => throw (IO.userError ("unexpected tactic elaborator type at '" ++ toString declName ++ "' `TacticElab` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

abbrev TacticElabAttribute := ElabAttribute TacticElab
def mkTacticElabAttribute : IO TacticElabAttribute :=
mkElabAttribute TacticElab `tacticElab `Lean.Parser.Tactic `Lean.Elab.Tactic.TacticElab "tactic" builtinTacticElabTable
@[init mkTacticElabAttribute] constant tacticElabAttribute : TacticElabAttribute := arbitrary _

def logTrace (cls : Name) (ref : Syntax) (msg : MessageData) : TacticElabM Unit := liftTermElabM $ Term.logTrace cls ref msg
@[inline] def trace (cls : Name) (ref : Syntax) (msg : Unit → MessageData) : TacticElabM Unit := liftTermElabM $ Term.trace cls ref msg
@[inline] def traceAtCmdPos (cls : Name) (msg : Unit → MessageData) : TacticElabM Unit := liftTermElabM $ Term.traceAtCmdPos cls msg
def dbgTrace {α} [HasToString α] (a : α) : TacticElabM Unit :=_root_.dbgTrace (toString a) $ fun _ => pure ()

private def elabTacticUsing (s : State) (stx : Syntax) : List TacticElab → TacticElabM Unit
| []                => do
  let refFmt := stx.prettyPrint;
  throwError stx ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ refFmt))
| (elabFn::elabFns) => catch (elabFn stx)
  (fun ex => match ex with
    | Exception.error _           => throw ex
    | Exception.unsupportedSyntax => do set s; elabTacticUsing elabFns)

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (stx : Syntax) (x : TacticElabM α) : TacticElabM α :=
adaptReader (fun (ctx : Context) => { macroStack := stx :: ctx.macroStack, .. ctx }) x

partial def elabTactic : Syntax → TacticElabM Unit
| stx => withIncRecDepth stx $ withFreshMacroScope $ match stx with
  | Syntax.node k args => do
    trace `Elab.step stx $ fun _ => stx;
    s ← get;
    let table := (tacticElabAttribute.ext.getState s.env).table;
    let k := stx.getKind;
    match table.find? k with
    | some elabFns => elabTacticUsing s stx elabFns
      | none         => do
        scp ← getCurrMacroScope;
        env ← getEnv;
        match expandMacro env stx scp with
        | some stx' => withMacroExpansion stx $ elabTactic stx'
        | none      => throwError stx ("tactic '" ++ toString k ++ "' has not been implemented")
  | _ => throwError stx "unexpected command"


end Tactic

end Elab
end Lean
