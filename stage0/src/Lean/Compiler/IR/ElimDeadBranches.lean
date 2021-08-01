/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.IR.Format
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.CompilerM

namespace Lean.IR.UnreachableBranches

/-- Value used in the abstract interpreter -/
inductive Value where
  | bot -- undefined
  | top -- any value
  | ctor (i : CtorInfo) (vs : Array Value)
  | choice (vs : List Value)
  deriving Inhabited

namespace Value

protected partial def beq : Value → Value → Bool
  | bot, bot => true
  | top, top => true
  | ctor i₁ vs₁, ctor i₂ vs₂ => i₁ == i₂ && Array.isEqv vs₁ vs₂ Value.beq
  | choice vs₁, choice vs₂ =>
    vs₁.all (fun v₁ => vs₂.any fun v₂ => Value.beq v₁ v₂)
    &&
    vs₂.all (fun v₂ => vs₁.any fun v₁ => Value.beq v₁ v₂)
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

partial def addChoice (merge : Value → Value → Value) : List Value → Value → List Value
  | [], v => [v]
  | v₁@(ctor i₁ vs₁) :: cs, v₂@(ctor i₂ vs₂) =>
    if i₁ == i₂ then merge v₁ v₂ :: cs
    else v₁ :: addChoice merge cs v₂
  | _, _ => panic! "invalid addChoice"

partial def merge : Value → Value → Value
  | bot, v => v
  | v, bot => v
  | top, _ => top
  | _, top => top
  | v₁@(ctor i₁ vs₁), v₂@(ctor i₂ vs₂) =>
    if i₁ == i₂ then ctor i₁ $ vs₁.size.fold (init := #[]) fun i r => r.push (merge vs₁[i] vs₂[i])
    else choice [v₁, v₂]
  | choice vs₁, choice vs₂ => choice $ vs₁.foldl (addChoice merge) vs₂
  | choice vs, v => choice $ addChoice merge vs v
  | v, choice vs => choice $ addChoice merge vs v

protected partial def format : Value → Format
  | top => "top"
  | bot => "bot"
  | choice vs => format "@" ++ @List.format _ ⟨Value.format⟩ vs
  | ctor i vs => format "#" ++ if vs.isEmpty then format i.name else Format.paren (format i.name ++ @formatArray _ ⟨Value.format⟩ vs)

instance : ToFormat Value := ⟨Value.format⟩
instance : ToString Value := ⟨Format.pretty ∘ Value.format⟩

/- Make sure constructors of recursive inductive datatypes can only occur once in each path.
   We use this function this function to implement a simple widening operation for our abstract
   interpreter. -/
partial def truncate (env : Environment) : Value → NameSet → Value
  | ctor i vs, found =>
    let I := i.name.getPrefix
    if found.contains I then
      top
    else
      let cont (found' : NameSet) : Value :=
        ctor i (vs.map fun v => truncate env v found')
      match env.find? I with
      | some (ConstantInfo.inductInfo d) =>
        if d.isRec then cont (found.insert I)
        else cont found
      | _ => cont found
  | choice vs, found =>
    let newVs := vs.map fun v => truncate env v found
    if newVs.elem top then top
    else choice newVs
  | v, _ => v

/- Widening operator that guarantees termination in our abstract interpreter. -/
def widening (env : Environment) (v₁ v₂ : Value) : Value :=
  truncate env (merge v₁ v₂) {}

end Value

abbrev FunctionSummaries := SMap FunId Value

builtin_initialize functionSummariesExt : SimplePersistentEnvExtension (FunId × Value) FunctionSummaries ←
  registerSimplePersistentEnvExtension {
    name       := `unreachBranchesFunSummary,
    addImportedFn := fun as =>
      let cache : FunctionSummaries := mkStateFromImportedEntries (fun s (p : FunId × Value) => s.insert p.1 p.2) {} as
      cache.switch,
    addEntryFn := fun s ⟨e, n⟩ => s.insert e n
  }

def addFunctionSummary (env : Environment) (fid : FunId) (v : Value) : Environment :=
  functionSummariesExt.addEntry env (fid, v)

def getFunctionSummary? (env : Environment) (fid : FunId) : Option Value :=
  (functionSummariesExt.getState env).find? fid

abbrev Assignment := Std.HashMap VarId Value

structure InterpContext where
  currFnIdx : Nat := 0
  decls     : Array Decl
  env       : Environment
  lctx      : LocalContext := {}

structure InterpState where
  assignments : Array Assignment
  funVals     : Std.PArray Value -- we take snapshots during fixpoint computations

abbrev M := ReaderT InterpContext (StateM InterpState)

open Value

def findVarValue (x : VarId) : M Value := do
  let ctx ← read
  let s ← get
  let assignment := s.assignments[ctx.currFnIdx]
  pure $ assignment.findD x bot

def findArgValue (arg : Arg) : M Value :=
  match arg with
  | Arg.var x => findVarValue x
  | _         => pure top

def updateVarAssignment (x : VarId) (v : Value) : M Unit := do
  let v' ← findVarValue x
  let ctx ← read
  modify fun s => { s with assignments := s.assignments.modify ctx.currFnIdx fun a => a.insert x (merge v v') }

def resetVarAssignment (x : VarId) : M Unit := do
  let ctx ← read
  modify fun s => { s with assignments := s.assignments.modify ctx.currFnIdx fun a => a.insert x Value.bot }

def resetParamAssignment (y : Param) : M Unit :=
  resetVarAssignment y.x

partial def projValue : Value → Nat → Value
  | ctor _ vs, i => vs.getD i bot
  | choice vs, i => vs.foldl (fun r v => merge r (projValue v i)) bot
  | v, _         => v

def interpExpr : Expr → M Value
  | Expr.ctor i ys => return ctor i (← ys.mapM fun y => findArgValue y)
  | Expr.proj i x  => return projValue (← findVarValue x) i
  | Expr.fap fid ys => do
    let ctx ← read
    match getFunctionSummary? ctx.env fid with
    | some v => pure v
    | none   => do
      let s ← get
      match ctx.decls.findIdx? (fun decl => decl.name == fid) with
      | some idx => pure s.funVals[idx]
      | none     => pure top
  | _ => pure top

partial def containsCtor : Value → CtorInfo → Bool
  | top,       _ => true
  | ctor i _,  j => i == j
  | choice vs, j => vs.any $ fun v => containsCtor v j
  | _,         _ => false

def updateCurrFnSummary (v : Value) : M Unit := do
  let ctx ← read
  let currFnIdx := ctx.currFnIdx
  modify fun s => { s with funVals := s.funVals.modify currFnIdx (fun v' => widening ctx.env v v') }

/-- Return true if the assignment of at least one parameter has been updated. -/
def updateJPParamsAssignment (ys : Array Param) (xs : Array Arg) : M Bool := do
  let ctx ← read
  let currFnIdx := ctx.currFnIdx
  ys.size.foldM (init := false) fun i r => do
    let y := ys[i]
    let x := xs[i]
    let yVal ← findVarValue y.x
    let xVal ← findArgValue x
    let newVal := merge yVal xVal
    if newVal == yVal then
      pure r
    else
      modify fun s => { s with assignments := s.assignments.modify currFnIdx fun a => a.insert y.x newVal }
      pure true

private partial def resetNestedJPParams : FnBody → M Unit
  | FnBody.jdecl _ ys b k => do
    let ctx ← read
    let currFnIdx := ctx.currFnIdx
    ys.forM resetParamAssignment
    /- Remark we don't need to reset the parameters of joint-points
      nested in `b` since they will be reset if this JP is used. -/
    resetNestedJPParams k
  | FnBody.case _ _ _ alts =>
    alts.forM fun alt => match alt with
      | Alt.ctor _ b  => resetNestedJPParams b
      | Alt.default b => resetNestedJPParams b
  | e => do unless e.isTerminal do resetNestedJPParams e.body

partial def interpFnBody : FnBody → M Unit
  | FnBody.vdecl x _ e b => do
    let v ← interpExpr e
    updateVarAssignment x v
    interpFnBody b
  | FnBody.jdecl j ys v b =>
    withReader (fun ctx => { ctx with lctx := ctx.lctx.addJP j ys v }) do
      interpFnBody b
  | FnBody.case _ x _ alts => do
    let v ← findVarValue x
    alts.forM fun alt => do
      match alt with
      | Alt.ctor i b  => if containsCtor v i then interpFnBody b
      | Alt.default b => interpFnBody b
  | FnBody.ret x => do
    let v ← findArgValue x
    -- dbgTrace ("ret " ++ toString v) $ fun _ =>
    updateCurrFnSummary v
  | FnBody.jmp j xs => do
    let ctx ← read
    let ys := (ctx.lctx.getJPParams j).get!
    let b  := (ctx.lctx.getJPBody j).get!
    let updated ← updateJPParamsAssignment ys xs
    if updated then
      -- We must reset the value of nested join-point parameters since they depend on `ys` values
      resetNestedJPParams b
      interpFnBody b
  | e => do
    unless e.isTerminal do
      interpFnBody e.body

def inferStep : M Bool := do
  let ctx ← read
  modify fun s => { s with assignments := ctx.decls.map fun _ => {} }
  ctx.decls.size.foldM (init := false) fun idx modified => do
    match ctx.decls[idx] with
    | Decl.fdecl (xs := ys) (body := b) .. => do
      let s ← get
      let currVals := s.funVals[idx]
      withReader (fun ctx => { ctx with currFnIdx := idx }) do
        ys.forM fun y => updateVarAssignment y.x top
        interpFnBody b
        let s ← get
        let newVals := s.funVals[idx]
        pure (modified || currVals != newVals)
    | Decl.extern _ _ _ _ => pure modified

partial def inferMain : M Unit := do
  let modified ← inferStep
  if modified then inferMain else pure ()

partial def elimDeadAux (assignment : Assignment) : FnBody → FnBody
  | FnBody.vdecl x t e b  => FnBody.vdecl x t e (elimDeadAux assignment b)
  | FnBody.jdecl j ys v b => FnBody.jdecl j ys (elimDeadAux assignment v) (elimDeadAux assignment b)
  | FnBody.case tid x xType alts =>
    let v := assignment.findD x bot
    let alts := alts.map fun alt =>
      match alt with
      | Alt.ctor i b  => Alt.ctor i $ if containsCtor v i then elimDeadAux assignment b else FnBody.unreachable
      | Alt.default b => Alt.default (elimDeadAux assignment b)
    FnBody.case tid x xType alts
  | e =>
    if e.isTerminal then e
    else
      let (instr, b) := e.split
      let b := elimDeadAux assignment b
      instr.setBody b

partial def elimDead (assignment : Assignment) (d : Decl) : Decl :=
  match d with
  | Decl.fdecl (body := b) .. => d.updateBody! <| elimDeadAux assignment b
  | other => other

end UnreachableBranches

open UnreachableBranches

def elimDeadBranches (decls : Array Decl) : CompilerM (Array Decl) := do
  let s ← get
  let env := s.env
  let assignments : Array Assignment := decls.map fun _ => {}
  let funVals := Std.mkPArray decls.size Value.bot
  let ctx : InterpContext := { decls := decls, env := env }
  let s : InterpState := { assignments := assignments, funVals := funVals }
  let (_, s) := (inferMain ctx).run s
  let funVals := s.funVals
  let assignments := s.assignments
  modify fun s =>
    let env := decls.size.fold (init := s.env) fun i env =>
      addFunctionSummary env decls[i].name funVals[i]
    { s with env := env }
  pure $ decls.mapIdx fun i decl => elimDead assignments[i] decl

end Lean.IR
