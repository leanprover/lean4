/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FoldConsts
import Lean.Elab.Command

namespace Lean
namespace Elab
namespace Command

private def throwUnknownId (id : Name) : CommandElabM Unit :=
throwError ("unknown identifier '" ++ toString id ++ "'")

private def lparamsToMessageData (lparams : List Name) : MessageData :=
match lparams with
| []    => ""
| u::us =>
  let m : MessageData := ".{" ++ u;
  let m := us.foldl (fun (s : MessageData) u => s ++ ", " ++ u) m;
  m ++ "}"

private def mkHeader (kind : String) (id : Name) (lparams : List Name) (type : Expr) (isUnsafe : Bool) : CommandElabM MessageData := do
let m : MessageData := if isUnsafe then "unsafe " else "";
env ← getEnv;
let m := if isProtected env id then m ++ "protected " else m;
let (m, id) := match privateToUserName? id : _ → MessageData × Name with
  | some id => (m ++ "private ", id)
  | none    => (m, id);
let m := m ++ kind ++ " " ++ id ++ lparamsToMessageData lparams ++ " : " ++ type;
pure m

private def printDefLike (kind : String) (id : Name) (lparams : List Name) (type : Expr) (value : Expr) (isUnsafe := false) : CommandElabM Unit := do
m ← mkHeader kind id lparams type isUnsafe;
let m := m ++ " :=" ++ Format.line ++ value;
logInfo m

private def printAxiomLike (kind : String) (id : Name) (lparams : List Name) (type : Expr) (isUnsafe := false) : CommandElabM Unit := do
m ← mkHeader kind id lparams type isUnsafe;
logInfo m

private def printQuot (kind : QuotKind) (id : Name) (lparams : List Name) (type : Expr) : CommandElabM Unit := do
printAxiomLike "Quotient primitive" id lparams type

private def printInduct (id : Name) (lparams : List Name) (nparams : Nat) (nindices : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) : CommandElabM Unit := do
env ← getEnv;
m ← mkHeader "inductive" id lparams type isUnsafe;
let m := m ++ Format.line ++ "constructors:";
m ← ctors.foldlM
  (fun (m : MessageData) ctor => do
    cinfo ← getConstInfo ctor;
    pure $ m ++ Format.line ++ ctor ++ " : " ++ cinfo.type)
  m;
logInfo m

private def printIdCore (id : Name) : CommandElabM Unit := do
env ← getEnv;
match env.find? id with
| ConstantInfo.axiomInfo { lparams := us, type := t, isUnsafe := u, .. } => printAxiomLike "axiom" id us t u
| ConstantInfo.defnInfo  { lparams := us, type := t, value := v, isUnsafe := u, .. } => printDefLike "def" id us t v u
| ConstantInfo.thmInfo  { lparams := us, type := t, value := v, .. } => printDefLike "theorem" id us t v
| ConstantInfo.opaqueInfo  { lparams := us, type := t, isUnsafe := u, .. } => printAxiomLike "constant" id us t u
| ConstantInfo.quotInfo  { kind := kind, lparams := us, type := t, .. } => printQuot kind id us t
| ConstantInfo.ctorInfo { lparams := us, type := t, isUnsafe := u, .. } => printAxiomLike "constructor" id us t u
| ConstantInfo.recInfo { lparams := us, type := t, isUnsafe := u, .. } => printAxiomLike "recursor" id us t u
| ConstantInfo.inductInfo { lparams := us, nparams := nparams, nindices := nindices, type := t, ctors := ctors, isUnsafe := u, .. } =>
  printInduct id us nparams nindices t ctors u
| none => throwUnknownId id

def resolveId (id : Name) : CommandElabM (List Name) := do
cs ← liftTermElabM none $ Term.resolveGlobalName id;
let cs := cs.filter fun ⟨_, ps⟩ => ps.isEmpty;
let cs := cs.map fun ⟨c, _⟩ => c;
when cs.isEmpty $ throwUnknownId id;
pure cs

private def printId (id : Name) : CommandElabM Unit := do
cs ← resolveId id;
cs.forM printIdCore

@[builtinCommandElab «print»] def elabPrint : CommandElab :=
fun stx =>
  let numArgs := stx.getNumArgs;
  if numArgs == 2 then
    let arg := stx.getArg 1;
    if arg.isIdent then
      printId arg.getId
    else match arg.isStrLit? with
      | some val => logInfo val
      | none     => throwError "WIP"
  else
    throwError "invalid #print command"

namespace CollectAxioms

structure State :=
(visited : NameSet := {})
(axioms  : Array Name := #[])

abbrev M := ReaderT Environment $ StateM State

partial def collect : Name → M Unit
| c => do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM collect;
  s ← get;
  unless (s.visited.contains c) do
    modify fun s => { s with visited := s.visited.insert c };
    env ← read;
    match env.find? c with
    | some (ConstantInfo.axiomInfo _)  => modify fun s => { s with axioms := s.axioms.push c }
    | some (ConstantInfo.defnInfo v)   => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.thmInfo v)    => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.quotInfo _)   => pure ()
    | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
    | some (ConstantInfo.recInfo v)    => collectExpr v.type
    | some (ConstantInfo.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
    | none                             => pure ()

end CollectAxioms

private def printAxiomsOf (constName : Name) : CommandElabM Unit := do
env ← getEnv;
let (_, s) := ((CollectAxioms.collect constName).run env).run {};
if s.axioms.isEmpty then
  logInfo ("'" ++ constName ++ "' does not depend on any axioms")
else
  logInfo ("'" ++ constName ++ "' depends on axioms: " ++ toString s.axioms.toList)

@[builtinCommandElab «printAxioms»] def elabPrintAxioms : CommandElab :=
fun stx => do
  let id := (stx.getArg 2).getId;
  cs ← resolveId id;
  cs.forM printAxiomsOf

end Command
end Elab
end Lean
