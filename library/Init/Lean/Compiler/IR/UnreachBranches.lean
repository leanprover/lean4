/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Data.Option
import Init.Lean.Compiler.IR.Format
import Init.Lean.Compiler.IR.Basic

namespace Lean
namespace IR
namespace UnreachableBranches

/-- Value used in the abstract interpreter -/
inductive Value
| bot -- undefined
| top -- any value
| ctor (i : CtorInfo) (vs : Array Value)
| choice (vs : List Value)

namespace Value

instance : Inhabited Value := ⟨top⟩

protected partial def beq : Value → Value → Bool
| bot, bot => true
| top, top => true
| ctor i₁ vs₁, ctor i₂ vs₂ => i₁ == i₂ && Array.isEqv vs₁ vs₂ beq
| choice vs₁, choice vs₂ =>
  vs₁.all (fun v₁ => vs₂.any $ fun v₂ => beq v₁ v₂)
  &&
  vs₂.all (fun v₂ => vs₁.any $ fun v₁ => beq v₁ v₂)
| _, _ => false

instance : HasBeq Value := ⟨Value.beq⟩

partial def addChoice (merge : Value → Value → Value) : List Value → Value → List Value
| [], v => [v]
| v₁@(ctor i₁ vs₁) :: cs, v₂@(ctor i₂ vs₂) =>
  if i₁ == i₂ then merge v₁ v₂ :: cs
  else v₁ :: addChoice cs v₂
| _, _ => panic! "invalid addChoice"

partial def merge : Value → Value → Value
| bot, v => v
| v, bot => v
| top, _ => top
| _, top => top
| v₁@(ctor i₁ vs₁), v₂@(ctor i₂ vs₂) =>
  if i₁ == i₂ then ctor i₁ $ vs₁.size.fold (fun i r => r.push (merge (vs₁.get! i) (vs₂.get! i))) Array.empty
  else choice [v₁, v₂]
| choice vs₁, choice vs₂ => choice $ vs₁.foldl (addChoice merge) vs₂
| choice vs, v => choice $ addChoice merge vs v
| v, choice vs => choice $ addChoice merge vs v

protected partial def format : Value → Format
| top => "top"
| bot => "bot"
| choice vs => fmt "@" ++ @List.format _ ⟨format⟩ vs
| ctor i vs => fmt "#" ++ fmt i.name ++ @formatArray _ ⟨format⟩ vs

instance : HasFormat Value := ⟨Value.format⟩
instance : HasToString Value := ⟨Format.pretty ∘ Value.format⟩

end Value

abbrev FunctionSummaries := SMap FunId Value

def mkFunctionSummariesExtension : IO (SimplePersistentEnvExtension (FunId × Value) FunctionSummaries) :=
registerSimplePersistentEnvExtension {
  name       := `unreachBranchesFunSummary,
  addImportedFn := fun as =>
    let cache : FunctionSummaries := mkStateFromImportedEntries (fun s (p : FunId × Value) => s.insert p.1 p.2) {} as;
    cache.switch,
  addEntryFn := fun s ⟨e, n⟩ => s.insert e n
}

@[init mkFunctionSummariesExtension]
constant functionSummariesExt : SimplePersistentEnvExtension (FunId × Value) FunctionSummaries := default _

def addFunctionSummary (env : Environment) (fid : FunId) (v : Value) : Environment :=
functionSummariesExt.addEntry env (fid, v)

def getFunctionSummary (env : Environment) (fid : FunId) : Option Value :=
(functionSummariesExt.getState env).find fid

abbrev Assignment := HashMap VarId Value

structure InterpContext :=
(currFnIdx : Nat := 0)
(decls     : Array Decl)
(env       : Environment)
(lctx      : LocalContext := {})

structure InterpState :=
(assignments : Array Assignment)
(funVals     : PArray Value) -- we take snapshots during fixpoint computations

abbrev M := ReaderT InterpContext (State InterpState)

open Value

def findVarValue (x : VarId) : M Value :=
do ctx ← read;
   s ← get;
   match (s.assignments.get! ctx.currFnIdx).find x with
   | some v => pure v
   | none   => pure bot

def findArgValue (arg : Arg) : M Value :=
match arg with
| Arg.var x => findVarValue x
| _         => pure top

def updateVarAssignment (x : VarId) (v : Value) : M Unit :=
do v' ← findVarValue x;
   ctx ← read;
   modify $ fun s => { assignments := s.assignments.modify ctx.currFnIdx $ fun a => a.insert x (merge v v'), .. s }

partial def projValue : Value → Nat → Value
| ctor _ vs, i => vs.getD i bot
| choice vs, i => vs.foldl (fun r v => merge r (projValue v i)) bot
| v, _         => v

def interpExpr : Expr → M Value
| Expr.ctor i ys => ctor i <$> ys.mmap (fun y => findArgValue y)
| Expr.proj i x  => do v ← findVarValue x; pure $ projValue v i
| Expr.fap fid ys => do
  ctx ← read;
  match getFunctionSummary ctx.env fid with
  | some v => pure v
  | none   => do
    s ← get;
    match ctx.decls.findIdx? (fun decl => decl.name == fid) with
    | some idx => pure $ s.funVals.get! idx
    | none     => pure top
| _ => pure top

partial def containsCtor : Value → CtorInfo → Bool
| top,       _ => true
| ctor i _,  j => i == j
| choice vs, j => vs.any $ fun v => containsCtor v j
| _,         _ => false

def updateCurrFnSummary (v : Value) : M Unit :=
do ctx ← read;
   let currFnIdx := ctx.currFnIdx;
   s ← get;
   modify $ fun s => { funVals := s.funVals.modify currFnIdx (fun v' => merge v v'), .. s }


/-- Return true if the assignment of at least one parameter has been updated. -/
def updateJPParamsAssignment (ys : Array Param) (xs : Array Arg) : M Bool :=
do ctx ← read;
   let currFnIdx := ctx.currFnIdx;
   ys.size.mfold (fun i r => do
     let y := ys.get! i;
     let x := xs.get! i;
     yVal ← findVarValue y.x;
     xVal ← findArgValue x;
     let newVal := merge yVal xVal;
     if newVal == yVal then pure r
     else do
       modify $ fun s => { assignments := s.assignments.modify currFnIdx $ fun a => a.insert y.x newVal, .. s };
       pure true)
     false

partial def interpFnBody : FnBody → M Unit
| FnBody.vdecl x _ e b => do
  v ← interpExpr e;
  updateVarAssignment x v;
  interpFnBody b
| FnBody.jdecl j ys v b =>
  adaptReader (fun (ctx : InterpContext) => { lctx := ctx.lctx.addJP j ys v, .. ctx }) $
    interpFnBody b
| FnBody.case _ x _ alts => do
  v ← findVarValue x;
  alts.mfor $ fun alt =>
    match alt with
    | Alt.ctor i b  => when (containsCtor v i) $ interpFnBody b
    | Alt.default b => interpFnBody b
| FnBody.ret x => do
  v ← findArgValue x;
  updateCurrFnSummary v
| FnBody.jmp j xs => do
  ctx ← read;
  let ys := (ctx.lctx.getJPParams j).get!;
  updated ← updateJPParamsAssignment ys xs;
  when updated $
    interpFnBody $ (ctx.lctx.getJPBody j).get!
| e => unless (e.isTerminal) $ interpFnBody e.body

def inferStep : M Bool :=
do ctx ← read;
   ctx.decls.size.mfold (fun idx modified => do
     match ctx.decls.get! idx with
     | Decl.fdecl _ ys _ b => do
       s ← get;
       let currVals := s.funVals.get! idx;
       adaptReader (fun (ctx : InterpContext) => { currFnIdx := idx, .. ctx }) $ do
         ys.mfor $ fun y => updateVarAssignment y.x top;
         interpFnBody b;
       s ← get;
       let newVals := s.funVals.get! idx;
       -- TODO: apply widening
       pure (modified || currVals != newVals)
     | Decl.extern _ _ _ _ => pure modified)
     false

partial def inferMain : Unit → M Unit
| _ => do
  modified ← inferStep;
  if modified then inferMain () else pure ()

def infer (env : Environment) (decls : Array Decl) : Environment :=
let assignments : Array Assignment := decls.map $ fun _ => {};
let funVals := mkPArray decls.size bot;
let ctx : InterpContext := { decls := decls, env := env };
let s : InterpState := { assignments := assignments, funVals := funVals };
let (_, s) := (inferMain () ctx).run s;
let funVals := s.funVals;
decls.size.fold (fun i env => addFunctionSummary env (decls.get! i).name (funVals.get! i)) env

end UnreachableBranches
end IR
end Lean
