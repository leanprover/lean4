/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
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
  deriving Inhabited, Repr

protected partial def Value.toFormat : Value → Format
  | Value.bot => "⊥"
  | Value.top => "⊤"
  | Value.ctor info vs =>
    if vs.isEmpty then
      format info.name
    else
      Format.paren <| format info.name ++ Std.Format.join (vs.toList.map fun v => " " ++ Value.toFormat v)
  | Value.choice vs =>
    Format.paren <| Std.Format.joinSep (vs.map Value.toFormat) " | "

instance : ToFormat Value where
  format := Value.toFormat

instance : ToString Value where
  toString v := toString (format v)

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
  | v₁@(ctor i₁ _) :: cs, v₂@(ctor i₂ _) =>
    if i₁ == i₂ then merge v₁ v₂ :: cs
    else v₁ :: addChoice merge cs v₂
  | _, _ => panic! "invalid addChoice"

partial def merge (v₁ v₂ : Value) : Value :=
  match v₁, v₂ with
  | bot, v => v
  | v, bot => v
  | top, _ => top
  | _, top => top
  | v₁@(ctor i₁ vs₁), v₂@(ctor i₂ vs₂) =>
    if i₁ == i₂ then ctor i₁ <| vs₁.size.fold (init := #[]) fun i _ r => r.push (merge vs₁[i] vs₂[i]!)
    else choice [v₁, v₂]
  | choice vs₁, choice vs₂ => choice <| vs₁.foldl (addChoice merge) vs₂
  | choice vs, v => choice <| addChoice merge vs v
  | v, choice vs => choice <| addChoice merge vs v

protected partial def format : Value → Format
  | top => "top"
  | bot => "bot"
  | choice vs => format "@" ++ @List.format _ ⟨Value.format⟩ vs
  | ctor i vs => format "#" ++ if vs.isEmpty then format i.name else Format.paren (format i.name ++ @formatArray _ ⟨Value.format⟩ vs)

instance : ToFormat Value := ⟨Value.format⟩
instance : ToString Value := ⟨Format.pretty ∘ Value.format⟩

/--
  In `truncate`, we approximate a value as `top` if depth > `truncateMaxDepth`.
  TODO: add option to control this parameter.
-/
def truncateMaxDepth := 8

/--
  Make sure constructors of recursive inductive datatypes can only occur once in each path.
  Values at depth > truncateMaxDepth are also approximated at `top`.
  We use this function this function to implement a simple widening operation for our abstract
  interpreter.
  Recall the widening functions is used to ensure termination in abstract interpreters.
-/
partial def truncate (env : Environment) (v : Value) (s : NameSet) : Value :=
  go v s truncateMaxDepth
where
  go (v : Value) (s : NameSet) (depth : Nat) : Value :=
    match depth with
    | 0 => top
    | depth+1 =>
      match v, s with
      | ctor i vs, found =>
        let I := i.name.getPrefix
        if found.contains I then
          top
        else
          let cont (found' : NameSet) : Value :=
            ctor i (vs.map fun v => go v found' depth)
          match env.find? I with
          | some (ConstantInfo.inductInfo d) =>
            if d.isRec then cont (found.insert I)
            else cont found
          | _ => cont found
      | choice vs, found =>
        let newVs := vs.map fun v => go v found depth
        if newVs.elem top then top
        else choice newVs
      | v, _ => v

/-- Widening operator that guarantees termination in our abstract interpreter. -/
def widening (env : Environment) (v₁ v₂ : Value) : Value :=
  truncate env (merge v₁ v₂) {}

end Value

abbrev FunctionSummaries := PHashMap FunId Value

private abbrev declLt (a b : FunId × Value) :=
  Name.quickLt a.1 b.1

private abbrev sortEntries (entries : Array (FunId × Value)) : Array (FunId × Value) :=
  entries.qsort declLt

private abbrev findAtSorted? (entries : Array (FunId × Value)) (fid : FunId) : Option Value :=
  if let some (_, value) := entries.binSearch (fid, default) declLt then
    some value
  else
    none

builtin_initialize functionSummariesExt : SimplePersistentEnvExtension (FunId × Value) FunctionSummaries ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn := fun s ⟨e, n⟩ => s.insert e n
    toArrayFn := fun s => sortEntries s.toArray
    asyncMode := .sync  -- compilation is non-parallel anyway
    replay? := some <| SimplePersistentEnvExtension.replayOfFilter (!·.contains ·.1) (fun s ⟨e, n⟩ => s.insert e n)
  }

def addFunctionSummary (env : Environment) (fid : FunId) (v : Value) : Environment :=
  functionSummariesExt.addEntry (env.addExtraName fid) (fid, v)

def getFunctionSummary? (env : Environment) (fid : FunId) : Option Value :=
  match env.getModuleIdxFor? fid with
  | some modIdx => findAtSorted? (functionSummariesExt.getModuleEntries env modIdx) fid
  | none        => functionSummariesExt.getState env |>.find? fid

abbrev Assignment := Std.HashMap VarId Value

structure InterpContext where
  currFnIdx : Nat := 0
  decls     : Array Decl
  env       : Environment
  lctx      : LocalContext := {}

structure InterpState where
  assignments : Array Assignment
  funVals     : PArray Value -- we take snapshots during fixpoint computations

abbrev M := ReaderT InterpContext (StateM InterpState)

open Value

def findVarValue (x : VarId) : M Value := do
  let ctx ← read
  let s ← get
  let assignment := s.assignments[ctx.currFnIdx]!
  return assignment.getD x bot

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
  | Expr.fap fid _  => do
    let ctx ← read
    match getFunctionSummary? ctx.env fid with
    | some v => pure v
    | none   => do
      let s ← get
      match ctx.decls.findIdx? (fun decl => decl.name == fid) with
      | some idx => pure s.funVals[idx]!
      | none     => pure top
  | _ => pure top

partial def containsCtor : Value → CtorInfo → Bool
  | top,       _ => true
  | ctor i _,  j => i == j
  | choice vs, j => vs.any fun v => containsCtor v j
  | _,         _ => false

def updateCurrFnSummary (v : Value) : M Unit := do
  let ctx ← read
  let currFnIdx := ctx.currFnIdx
  modify fun s => { s with funVals := s.funVals.modify currFnIdx (fun v' => widening ctx.env v v') }

/-- Return true if the assignment of at least one parameter has been updated. -/
def updateJPParamsAssignment (ys : Array Param) (xs : Array Arg) : M Bool := do
  let ctx ← read
  let currFnIdx := ctx.currFnIdx
  ys.size.foldM (init := false) fun i _ r => do
    let y := ys[i]
    let x := xs[i]!
    let yVal ← findVarValue y.x
    let xVal ← findArgValue x
    let newVal := merge yVal xVal
    if newVal == yVal then
      pure r
    else
      modify fun s => { s with assignments := s.assignments.modify currFnIdx fun a => a.insert y.x newVal }
      pure true

private partial def resetNestedJPParams : FnBody → M Unit
  | FnBody.jdecl _ ys _ k => do
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
  ctx.decls.size.foldM (init := false) fun idx _ modified => do
    match ctx.decls[idx] with
    | .fdecl (xs := ys) (body := b) .. => do
      let s ← get
      let currVals := s.funVals[idx]!
      withReader (fun ctx => { ctx with currFnIdx := idx }) do
        ys.forM fun y => updateVarAssignment y.x top
        interpFnBody b
        let s ← get
        let newVals := s.funVals[idx]!
        pure (modified || currVals != newVals)
    | .extern .. => pure modified

partial def inferMain : M Unit := do
  let modified ← inferStep
  if modified then inferMain else pure ()

partial def elimDeadAux (assignment : Assignment) : FnBody → FnBody
  | FnBody.vdecl x t e b  => FnBody.vdecl x t e (elimDeadAux assignment b)
  | FnBody.jdecl j ys v b => FnBody.jdecl j ys (elimDeadAux assignment v) (elimDeadAux assignment b)
  | FnBody.case tid x xType alts =>
    let v := assignment.getD x bot
    let alts := alts.map fun alt =>
      match alt with
      | Alt.ctor i b  => Alt.ctor i <| if containsCtor v i then elimDeadAux assignment b else FnBody.unreachable
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
  | .fdecl (body := b) .. => d.updateBody! <| elimDeadAux assignment b
  | other => other

end UnreachableBranches

open UnreachableBranches

def elimDeadBranches (decls : Array Decl) : CompilerM (Array Decl) := do
  let s ← get
  let env := s.env
  let assignments : Array Assignment := decls.map fun _ => {}
  let funVals := mkPArray decls.size Value.bot
  let ctx : InterpContext := { decls := decls, env := env }
  let s : InterpState := { assignments := assignments, funVals := funVals }
  let (_, s) := (inferMain ctx).run s
  let funVals := s.funVals
  let assignments := s.assignments
  modify fun s =>
    let env := decls.size.fold (init := s.env) fun i _ env =>
      addFunctionSummary env decls[i].name funVals[i]!
    { s with env := env }
  return decls.mapIdx fun i decl => elimDead assignments[i]! decl

end Lean.IR
