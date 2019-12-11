/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Control.Reader
import Init.Data.Option
import Init.Data.Nat
import Init.Lean.Compiler.IR.Format
import Init.Lean.Compiler.IR.Basic
import Init.Lean.Compiler.IR.CompilerM

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
  if i₁ == i₂ then ctor i₁ $ vs₁.size.fold (fun i r => r.push (merge (vs₁.get! i) (vs₂.get! i))) #[]
  else choice [v₁, v₂]
| choice vs₁, choice vs₂ => choice $ vs₁.foldl (addChoice merge) vs₂
| choice vs, v => choice $ addChoice merge vs v
| v, choice vs => choice $ addChoice merge vs v

protected partial def format : Value → Format
| top => "top"
| bot => "bot"
| choice vs => fmt "@" ++ @List.format _ ⟨format⟩ vs
| ctor i vs => fmt "#" ++ if vs.isEmpty then fmt i.name else Format.paren (fmt i.name ++ @formatArray _ ⟨format⟩ vs)

instance : HasFormat Value := ⟨Value.format⟩
instance : HasToString Value := ⟨Format.pretty ∘ Value.format⟩

/- Make sure constructors of recursive inductive datatypes can only occur once in each path.
   We use this function this function to implement a simple widening operation for our abstract
   interpreter. -/
partial def truncate (env : Environment) : Value → NameSet → Value
| ctor i vs, found =>
  let I := i.name.getPrefix;
  if found.contains I then
    top
  else
    let cont (found' : NameSet) : Value :=
      ctor i (vs.map $ fun v => truncate v found');
    match env.find I with
    | some (ConstantInfo.inductInfo d) =>
      if d.isRec then cont (found.insert I)
      else cont found
    | _ => cont found
| choice vs, found =>
  let newVs := vs.map $ fun v => truncate v found;
  if newVs.elem top then top
  else choice newVs
| v, _ => v

/- Widening operator that guarantees termination in our abstract interpreter. -/
def widening (env : Environment) (v₁ v₂ : Value) : Value :=
truncate env (merge v₁ v₂) {}

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
constant functionSummariesExt : SimplePersistentEnvExtension (FunId × Value) FunctionSummaries := arbitrary _

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

abbrev M := ReaderT InterpContext (StateM InterpState)

open Value

def findVarValue (x : VarId) : M Value := do
ctx ← read;
s ← get;
let assignment := s.assignments.get! ctx.currFnIdx;
pure $ assignment.findD x bot

def findArgValue (arg : Arg) : M Value :=
match arg with
| Arg.var x => findVarValue x
| _         => pure top

def updateVarAssignment (x : VarId) (v : Value) : M Unit := do
v' ← findVarValue x;
ctx ← read;
modify $ fun s => { assignments := s.assignments.modify ctx.currFnIdx $ fun a => a.insert x (merge v v'), .. s }

partial def projValue : Value → Nat → Value
| ctor _ vs, i => vs.getD i bot
| choice vs, i => vs.foldl (fun r v => merge r (projValue v i)) bot
| v, _         => v

def interpExpr : Expr → M Value
| Expr.ctor i ys => ctor i <$> ys.mapM (fun y => findArgValue y)
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

def updateCurrFnSummary (v : Value) : M Unit := do
ctx ← read;
let currFnIdx := ctx.currFnIdx;
modify $ fun s => { funVals := s.funVals.modify currFnIdx (fun v' => widening ctx.env v v'), .. s }

/-- Return true if the assignment of at least one parameter has been updated. -/
def updateJPParamsAssignment (ys : Array Param) (xs : Array Arg) : M Bool := do
ctx ← read;
let currFnIdx := ctx.currFnIdx;
ys.size.foldM
  (fun i r => do
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
  alts.forM $ fun alt =>
    match alt with
    | Alt.ctor i b  => when (containsCtor v i) $ interpFnBody b
    | Alt.default b => interpFnBody b
| FnBody.ret x => do
  v ← findArgValue x;
  -- dbgTrace ("ret " ++ toString v) $ fun _ =>
  updateCurrFnSummary v
| FnBody.jmp j xs => do
  ctx ← read;
  let ys := (ctx.lctx.getJPParams j).get!;
  updated ← updateJPParamsAssignment ys xs;
  when updated $
    interpFnBody $ (ctx.lctx.getJPBody j).get!
| e => unless (e.isTerminal) $ interpFnBody e.body

def inferStep : M Bool := do
ctx ← read;
modify $ fun s => { assignments := ctx.decls.map $ fun _ => {}, .. s };
ctx.decls.size.foldM (fun idx modified => do
  match ctx.decls.get! idx with
  | Decl.fdecl fid ys _ b => do
    s ← get;
    -- dbgTrace (">> " ++ toString fid) $ fun _ =>
    let currVals := s.funVals.get! idx;
    adaptReader (fun (ctx : InterpContext) => { currFnIdx := idx, .. ctx }) $ do
      ys.forM $ fun y => updateVarAssignment y.x top;
      interpFnBody b;
    s ← get;
    let newVals := s.funVals.get! idx;
    pure (modified || currVals != newVals)
  | Decl.extern _ _ _ _ => pure modified)
  false

partial def inferMain : Unit → M Unit
| _ => do
  modified ← inferStep;
  if modified then inferMain () else pure ()

partial def elimDeadAux (assignment : Assignment) : FnBody → FnBody
| FnBody.vdecl x t e b  => FnBody.vdecl x t e (elimDeadAux b)
| FnBody.jdecl j ys v b => FnBody.jdecl j ys (elimDeadAux v) (elimDeadAux b)
| FnBody.case tid x xType alts =>
  let v := assignment.findD x bot;
  let alts := alts.map $ fun alt =>
    match alt with
    | Alt.ctor i b  => Alt.ctor i $ if containsCtor v i then elimDeadAux b else FnBody.unreachable
    | Alt.default b => Alt.default (elimDeadAux b);
  FnBody.case tid x xType alts
| e =>
  if e.isTerminal then e
  else
    let (instr, b) := e.split;
    let b := elimDeadAux b;
    instr.setBody b

partial def elimDead (assignment : Assignment) : Decl → Decl
| Decl.fdecl fid ys t b => Decl.fdecl fid ys t $ elimDeadAux assignment b
| other => other

end UnreachableBranches

open UnreachableBranches

def elimDeadBranches (decls : Array Decl) : CompilerM (Array Decl) := do
s ← get;
let env := s.env;
let assignments : Array Assignment := decls.map $ fun _ => {};
let funVals := mkPArray decls.size Value.bot;
let ctx : InterpContext := { decls := decls, env := env };
let s : InterpState := { assignments := assignments, funVals := funVals };
let (_, s) := (inferMain () ctx).run s;
let funVals := s.funVals;
let assignments := s.assignments;
modify $ fun s =>
  let env := decls.size.fold (fun i env =>
    -- dbgTrace (">> " ++ toString (decls.get! i).name ++ " " ++ toString (funVals.get! i)) $ fun _ =>
    addFunctionSummary env (decls.get! i).name (funVals.get! i))
    s.env;
  { env := env, .. s };
pure $ decls.mapIdx $ fun i decl => elimDead (assignments.get! i) decl

end IR
end Lean
