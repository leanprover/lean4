/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.ExportAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.NormIds

namespace Lean
namespace IR
namespace Borrow

namespace OwnedSet
abbrev Key := FunId × Index

def beq : Key → Key → Bool
  | (f₁, x₁), (f₂, x₂) => f₁ == f₂ && x₁ == x₂

instance : BEq Key := ⟨beq⟩

def getHash : Key → UInt64
  | (f, x) => mixHash (hash f) (hash x)
instance : Hashable Key := ⟨getHash⟩
end OwnedSet

open OwnedSet (Key) in
abbrev OwnedSet := Std.HashMap Key Unit
def OwnedSet.insert (s : OwnedSet) (k : OwnedSet.Key) : OwnedSet := Std.HashMap.insert s k ()
def OwnedSet.contains (s : OwnedSet) (k : OwnedSet.Key) : Bool   := Std.HashMap.contains s k

/-! We perform borrow inference in a block of mutually recursive functions.
   Join points are viewed as local functions, and are identified using
   their local id + the name of the surrounding function.
   We keep a mapping from function and joint points to parameters (`Array Param`).
   Recall that `Param` contains the field `borrow`. -/
namespace ParamMap
inductive Key where
  | decl (name : FunId)
  | jp   (name : FunId) (jpid : JoinPointId)
  deriving BEq

def getHash : Key → UInt64
  | Key.decl n  => hash n
  | Key.jp n id => mixHash (hash n) (hash id)

instance : Hashable Key := ⟨getHash⟩
end ParamMap

open ParamMap (Key)
abbrev ParamMap := Std.HashMap Key (Array Param)

def ParamMap.fmt (map : ParamMap) : Format :=
  let fmts := map.fold (fun fmt k ps =>
    let k := match k with
      | ParamMap.Key.decl n  => format n
      | ParamMap.Key.jp n id => format n ++ ":" ++ format id
    fmt ++ Format.line ++ k ++ " -> " ++ formatParams ps)
   Format.nil
  "{" ++ (Format.nest 1 fmts) ++ "}"

instance : ToFormat ParamMap := ⟨ParamMap.fmt⟩
instance : ToString ParamMap := ⟨fun m => Format.pretty (format m)⟩

namespace InitParamMap
/-- Mark parameters that take a reference as borrow -/
def initBorrow (ps : Array Param) : Array Param :=
  ps.map fun p => { p with borrow := p.ty.isObj }

/-- We do not perform borrow inference for constants marked as `export`.
   Reason: we current write wrappers in C++ for using exported functions.
   These wrappers use smart pointers such as `object_ref`.
   When writing a new wrapper we need to know whether an argument is a borrow
   inference or not.
   We can revise this decision when we implement code for generating
   the wrappers automatically. -/
def initBorrowIfNotExported (exported : Bool) (ps : Array Param) : Array Param :=
  if exported then ps else initBorrow ps

partial def visitFnBody (fnid : FunId) : FnBody → StateM ParamMap Unit
  | FnBody.jdecl j xs v b  => do
    modify fun m => m.insert (ParamMap.Key.jp fnid j) (initBorrow xs)
    visitFnBody fnid v
    visitFnBody fnid b
  | FnBody.case _ _ _ alts => alts.forM fun alt => visitFnBody fnid alt.body
  | e => do
    unless e.isTerminal do
      let (_, b) := e.split
      visitFnBody fnid b

def visitDecls (env : Environment) (decls : Array Decl) : StateM ParamMap Unit :=
  decls.forM fun decl => match decl with
    | .fdecl (f := f) (xs := xs) (body := b) .. => do
      let exported := isExport env f
      modify fun m => m.insert (ParamMap.Key.decl f) (initBorrowIfNotExported exported xs)
      visitFnBody f b
    | _ => pure ()
end InitParamMap

def mkInitParamMap (env : Environment) (decls : Array Decl) : ParamMap :=
(InitParamMap.visitDecls env decls *> get).run' {}

/-! Apply the inferred borrow annotations stored at `ParamMap` to a block of mutually
   recursive functions. -/
namespace ApplyParamMap

partial def visitFnBody (fn : FunId) (paramMap : ParamMap) : FnBody → FnBody
  | FnBody.jdecl j _  v b =>
    let v := visitFnBody fn paramMap v
    let b := visitFnBody fn paramMap b
    match paramMap[ParamMap.Key.jp fn j]? with
    | some ys => FnBody.jdecl j ys v b
    | none    => unreachable!
  | FnBody.case tid x xType alts =>
    FnBody.case tid x xType <| alts.map fun alt => alt.modifyBody (visitFnBody fn paramMap)
  | e =>
    if e.isTerminal then e
    else
      let (instr, b) := e.split
      let b := visitFnBody fn paramMap b
      instr.setBody b

def visitDecls (decls : Array Decl) (paramMap : ParamMap) : Array Decl :=
  decls.map fun decl => match decl with
    | Decl.fdecl f _  ty b info =>
      let b := visitFnBody f paramMap b
      match paramMap[ParamMap.Key.decl f]? with
      | some xs => Decl.fdecl f xs ty b info
      | none    => unreachable!
    | other => other

end ApplyParamMap

def applyParamMap (decls : Array Decl) (map : ParamMap) : Array Decl :=
  ApplyParamMap.visitDecls decls map

structure BorrowInfCtx where
  env      : Environment
  decls    : Array Decl  -- block of mutually recursive functions
  currFn   : FunId    := default -- Function being analyzed.
  paramSet : IndexSet := {} -- Set of all function parameters in scope. This is used to implement the heuristic at `ownArgsUsingParams`

structure BorrowInfState where
  /-- Set of variables that must be `owned`. -/
  owned    : OwnedSet := {}
  modified : Bool     := false
  paramMap : ParamMap

abbrev M := ReaderT BorrowInfCtx (StateM BorrowInfState)

def getCurrFn : M FunId := do
  let ctx ← read
  pure ctx.currFn

def markModified : M Unit :=
  modify fun s => { s with modified := true }

def ownVar (x : VarId) : M Unit := do
  let currFn ← getCurrFn
  modify fun s =>
    if s.owned.contains (currFn, x.idx) then s
    else { s with owned := s.owned.insert (currFn, x.idx), modified := true }

def ownArg (x : Arg) : M Unit :=
  match x with
  | Arg.var x => ownVar x
  | _         => pure ()

def ownArgs (xs : Array Arg) : M Unit :=
  xs.forM ownArg

def isOwned (x : VarId) : M Bool := do
  let currFn ← getCurrFn
  let s      ← get
  return s.owned.contains (currFn, x.idx)

/-- Updates `map[k]` using the current set of `owned` variables. -/
def updateParamMap (k : ParamMap.Key) : M Unit := do
  let s ← get
  match s.paramMap[k]? with
  | some ps => do
    let ps ← ps.mapM fun (p : Param) => do
      if !p.borrow then pure p
      else if (← isOwned p.x) then
        markModified
        pure { p with borrow := false }
      else
        pure p
    modify fun s => { s with paramMap := s.paramMap.insert k ps }
  | none    => pure ()

def getParamInfo (k : ParamMap.Key) : M (Array Param) := do
  let s ← get
  match s.paramMap[k]? with
  | some ps => pure ps
  | none    =>
    match k with
    | ParamMap.Key.decl fn => do
      let ctx ← read
      match findEnvDecl ctx.env fn with
      | some decl => pure decl.params
      | none      => unreachable!
    | _ => unreachable!

/-- For each ps[i], if ps[i] is owned, then mark xs[i] as owned. -/
def ownArgsUsingParams (xs : Array Arg) (ps : Array Param) : M Unit :=
  xs.size.forM fun i _ => do
    let x := xs[i]
    let p := ps[i]!
    unless p.borrow do ownArg x

/-- For each xs[i], if xs[i] is owned, then mark ps[i] as owned.
   We use this action to preserve tail calls. That is, if we have
   a tail call `f xs`, if the i-th parameter is borrowed, but `xs[i]` is owned
   we would have to insert a `dec xs[i]` after `f xs` and consequently
   "break" the tail call. -/
def ownParamsUsingArgs (xs : Array Arg) (ps : Array Param) : M Unit :=
  xs.size.forM fun i _ => do
    let x := xs[i]
    let p := ps[i]!
    match x with
    | Arg.var x => if (← isOwned x) then ownVar p.x
    | _         => pure ()

/-- Mark `xs[i]` as owned if it is one of the parameters `ps`.
   We use this action to mark function parameters that are being "packed" inside constructors.
   This is a heuristic, and is not related with the effectiveness of the reset/reuse optimization.
   It is useful for code such as
   ```
   def f (x y : obj) :=
   let z := ctor_1 x y;
   ret z
   ```
-/
def ownArgsIfParam (xs : Array Arg) : M Unit := do
  let ctx ← read
  xs.forM fun x => do
    match x with
    | Arg.var x => if ctx.paramSet.contains x.idx then ownVar x
    | _ => pure ()

def collectExpr (z : VarId) : Expr → M Unit
  | Expr.reset _ x      => ownVar z *> ownVar x
  | Expr.reuse x _ _ ys => ownVar z *> ownVar x *> ownArgsIfParam ys
  | Expr.ctor _ xs      => ownVar z *> ownArgsIfParam xs
  | Expr.proj _ x       => do
    if (← isOwned x) then ownVar z
    if (← isOwned z) then ownVar x
  | Expr.fap g xs       => do
    let ps ← getParamInfo (ParamMap.Key.decl g)
    ownVar z *> ownArgsUsingParams xs ps
  | Expr.ap x ys        => ownVar z *> ownVar x *> ownArgs ys
  | Expr.pap _ xs       => ownVar z *> ownArgs xs
  | _                   => pure ()

def preserveTailCall (x : VarId) (v : Expr) (b : FnBody) : M Unit := do
  let ctx ← read
  match v, b with
  | (Expr.fap g ys), (FnBody.ret (Arg.var z)) =>
    -- NOTE: we currently support TCO for self-calls only
    if ctx.currFn == g && x == z then
      let ps ← getParamInfo (ParamMap.Key.decl g)
      ownParamsUsingArgs ys ps
  | _, _ => pure ()

def updateParamSet (ctx : BorrowInfCtx) (ps : Array Param) : BorrowInfCtx :=
  { ctx with paramSet := ps.foldl (fun s p => s.insert p.x.idx) ctx.paramSet }

partial def collectFnBody : FnBody → M Unit
  | FnBody.jdecl j ys v b => do
    withReader (fun ctx => updateParamSet ctx ys) (collectFnBody v)
    let ctx ← read
    updateParamMap (ParamMap.Key.jp ctx.currFn j)
    collectFnBody b
  | FnBody.vdecl x _ v b => collectFnBody b *> collectExpr x v *> preserveTailCall x v b
  | FnBody.jmp j ys      => do
    let ctx ← read
    let ps ← getParamInfo (ParamMap.Key.jp ctx.currFn j)
    ownArgsUsingParams ys ps -- for making sure the join point can reuse
    ownParamsUsingArgs ys ps  -- for making sure the tail call is preserved
  | FnBody.case _ _ _ alts => alts.forM fun alt => collectFnBody alt.body
  | e                      => do unless e.isTerminal do collectFnBody e.body

partial def collectDecl : Decl → M Unit
  | .fdecl (f := f) (xs := ys) (body := b) .. =>
    withReader (fun ctx => let ctx := updateParamSet ctx ys; { ctx with currFn := f }) do
      collectFnBody b
      updateParamMap (ParamMap.Key.decl f)
  | _ => pure ()

/-- Keep executing `x` until it reaches a fixpoint -/
partial def whileModifing (x : M Unit) : M Unit := do
  modify fun s => { s with modified := false }
  x
  let s ← get
  if s.modified then
    whileModifing x
  else
    pure ()

def collectDecls : M ParamMap := do
  whileModifing ((← read).decls.forM collectDecl)
  let s ← get
  pure s.paramMap

def infer (env : Environment) (decls : Array Decl) : ParamMap :=
  collectDecls { env, decls } |>.run' { paramMap := mkInitParamMap env decls }

end Borrow

def inferBorrow (decls : Array Decl) : CompilerM (Array Decl) := do
  let env ← getEnv
  let paramMap := Borrow.infer env decls
  pure (Borrow.applyParamMap decls paramMap)

end IR
end Lean
