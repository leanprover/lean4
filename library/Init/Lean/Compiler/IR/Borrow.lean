/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Compiler.ExportAttr
import Init.Lean.Compiler.IR.CompilerM
import Init.Lean.Compiler.IR.NormIds

namespace Lean
namespace IR
namespace Borrow
/- We perform borrow inference in a block of mutually recursive functions.
   Join points are viewed as local functions, and are identified using
   their local id + the name of the surrounding function.

   We keep a mapping from function and joint points to parameters (`Array Param`).
   Recall that `Param` contains the field `borrow`.
   The type `Key` is the the key of this map. -/
inductive Key
| decl (name : FunId)
| jp   (name : FunId) (jpid : JoinPointId)

namespace Key
def beq : Key → Key → Bool
| decl n₁,   decl n₂   => n₁ == n₂
| jp n₁ id₁, jp n₂ id₂ => n₁ == n₂ && id₁ == id₂
| _,         _         => false

instance : HasBeq Key := ⟨beq⟩

def getHash : Key → USize
| decl n  => hash n
| jp n id => mixHash (hash n) (hash id)

instance : Hashable Key := ⟨getHash⟩
end Key

abbrev ParamMap := HashMap Key (Array Param)

def ParamMap.fmt (map : ParamMap) : Format :=
let fmts := map.fold (fun fmt k ps =>
  let k := match k with
    | Key.decl n  => format n
    | Key.jp n id => format n ++ ":" ++ format id;
  fmt ++ Format.line ++ k ++ " -> " ++ formatParams ps)
 Format.nil;
"{" ++ (Format.nest 1 fmts) ++ "}"

instance : HasFormat ParamMap := ⟨ParamMap.fmt⟩
instance : HasToString ParamMap := ⟨fun m => Format.pretty (format m)⟩

namespace InitParamMap

/- Mark parameters that take a reference as borrow -/
def initBorrow (ps : Array Param) : Array Param :=
ps.map $ fun p => { borrow := p.ty.isObj, .. p }

/- We do perform borrow inference for constants marked as `export`.
   Reason: we current write wrappers in C++ for using exported functions.
   These wrappers use smart pointers such as `object_ref`.
   When writing a new wrapper we need to know whether an argument is a borrow
   inference or not.

   We can revise this decision when we implement code for generating
   the wrappers automatically. -/
def initBorrowIfNotExported (exported : Bool) (ps : Array Param) : Array Param :=
if exported then ps else initBorrow ps

partial def visitFnBody (fnid : FunId) : FnBody → State ParamMap Unit
| FnBody.jdecl j xs v b   => do
  modify $ fun m => m.insert (Key.jp fnid j) (initBorrow xs);
  visitFnBody v;
  visitFnBody b
| e =>
  unless (e.isTerminal) $ do
    let (instr, b) := e.split;
    visitFnBody b

def visitDecls (env : Environment) (decls : Array Decl) : State ParamMap Unit :=
decls.mfor $ fun decl => match decl with
  | Decl.fdecl f xs _ b => do
    let exported := isExport env f;
    modify $ fun m => m.insert (Key.decl f) (initBorrowIfNotExported exported xs);
    visitFnBody f b
  | _ => pure ()
end InitParamMap

def mkInitParamMap (env : Environment) (decls : Array Decl) : ParamMap :=
(InitParamMap.visitDecls env decls *> get).run' {}

/- Apply the inferred borrow annotations stored at `ParamMap` to a block of mutually
   recursive functions. -/
namespace ApplyParamMap

partial def visitFnBody : FnBody → FunId → ParamMap → FnBody
| FnBody.jdecl j xs v b,   fnid, map =>
  let v := visitFnBody v fnid map;
  let b := visitFnBody b fnid map;
  match map.find (Key.jp fnid j) with
  | some ys => FnBody.jdecl j ys v b
  | none    => FnBody.jdecl j xs v b
| e, fnid, map =>
  if e.isTerminal then e
  else
    let (instr, b) := e.split;
    let b := visitFnBody b fnid map;
    instr.setBody b

def visitDecls (decls : Array Decl) (map : ParamMap) : Array Decl :=
decls.map $ fun decl => match decl with
  | Decl.fdecl f xs ty b =>
    let b := visitFnBody b f map;
    match map.find (Key.decl f) with
    | some xs => Decl.fdecl f xs ty b
    | none    => Decl.fdecl f xs ty b
  | other => other

end ApplyParamMap

def applyParamMap (decls : Array Decl) (map : ParamMap) : Array Decl :=
-- dbgTrace ("applyParamMap " ++ toString map) $ fun _ =>
ApplyParamMap.visitDecls decls map

structure BorrowInfCtx :=
(env : Environment)
(currFn : FunId := default _) -- Function being analyzed.
(paramSet : IndexSet := {}) -- Set of all function parameters in scope. This is used to implement the heuristic at `ownArgsUsingParams`

structure BorrowInfState :=
/- `map` is a mapping storing the inferred borrow annotations for all functions (and joint points) in a mutually recursive declaration. -/
(map : ParamMap)
/- Set of variables that must be `owned`. -/
(owned : IndexSet := {})
(modifiedOwned : Bool := false)
(modifiedParamMap : Bool := false)

abbrev M := ReaderT BorrowInfCtx (State BorrowInfState)

def markModifiedParamMap : M Unit :=
modify $ fun s => { modifiedParamMap := true, .. s }

def ownVar (x : VarId) : M Unit :=
-- dbgTrace ("ownVar " ++ toString x) $ fun _ =>
modify $ fun s =>
  if s.owned.contains x.idx then s
  else { owned := s.owned.insert x.idx, modifiedOwned := true, .. s }

def ownArg (x : Arg) : M Unit :=
match x with
| (Arg.var x) => ownVar x
| _           => pure ()

def ownArgs (xs : Array Arg) : M Unit :=
xs.mfor ownArg

def isOwned (x : VarId) : M Bool :=
do s ← get;
   pure $ s.owned.contains x.idx

/- Updates `map[k]` using the current set of `owned` variables. -/
def updateParamMap (k : Key) : M Unit :=
do s ← get;
   match s.map.find k with
   | some ps => do
     ps ← ps.mmap $ fun (p : Param) =>
      if p.borrow && s.owned.contains p.x.idx then do
        markModifiedParamMap; pure { borrow := false, .. p }
      else
        pure p;
     modify $ fun s => { map := s.map.insert k ps, .. s }
   | none    => pure ()

def getParamInfo (k : Key) : M (Array Param) :=
do s ← get;
   match s.map.find k with
   | some ps => pure ps
   | none    =>
     match k with
     | (Key.decl fn) => do
       ctx ← read;
       match findEnvDecl ctx.env fn with
       | some decl => pure decl.params
       | none      => pure #[]   -- unreachable if well-formed input
     | _ => pure #[] -- unreachable if well-formed input

/- For each ps[i], if ps[i] is owned, then mark xs[i] as owned. -/
def ownArgsUsingParams (xs : Array Arg) (ps : Array Param) : M Unit :=
xs.size.mfor $ fun i => do
  let x := xs.get! i;
  let p := ps.get! i;
  unless p.borrow $ ownArg x

/- For each xs[i], if xs[i] is owned, then mark ps[i] as owned.
   We use this action to preserve tail calls. That is, if we have
   a tail call `f xs`, if the i-th parameter is borrowed, but `xs[i]` is owned
   we would have to insert a `dec xs[i]` after `f xs` and consequently
   "break" the tail call. -/
def ownParamsUsingArgs (xs : Array Arg) (ps : Array Param) : M Unit :=
xs.size.mfor $ fun i => do
  let x := xs.get! i;
  let p := ps.get! i;
  match x with
  | Arg.var x => mwhen (isOwned x) $ ownVar p.x
  | _         => pure ()

/- Mark `xs[i]` as owned if it is one of the parameters `ps`.
   We use this action to mark function parameters that are being "packed" inside constructors.
   This is a heuristic, and is not related with the effectiveness of the reset/reuse optimization.
   It is useful for code such as
   ```
   def f (x y : obj) :=
   let z := ctor_1 x y;
   ret z
   ```
-/
def ownArgsIfParam (xs : Array Arg) : M Unit :=
do ctx ← read;
   xs.mfor $ fun x =>
     match x with
     | Arg.var x => when (ctx.paramSet.contains x.idx) $ ownVar x
     | _ => pure ()

def collectExpr (z : VarId) : Expr → M Unit
| Expr.reset _ x      => ownVar z *> ownVar x
| Expr.reuse x _ _ ys => ownVar z *> ownVar x *> ownArgsIfParam ys
| Expr.ctor _ xs      => ownVar z *> ownArgsIfParam xs
| Expr.proj _ x       => mwhen (isOwned z) $ ownVar x
| Expr.fap g xs       => do ps ← getParamInfo (Key.decl g);
  -- dbgTrace ("collectExpr: " ++ toString g ++ " " ++ toString (formatParams ps)) $ fun _ =>
  ownVar z *> ownArgsUsingParams xs ps
| Expr.ap x ys        => ownVar z *> ownVar x *> ownArgs ys
| Expr.pap _ xs       => ownVar z *> ownArgs xs
| other               => pure ()

def preserveTailCall (x : VarId) (v : Expr) (b : FnBody) : M Unit :=
do ctx ← read;
match v, b with
| (Expr.fap g ys), (FnBody.ret (Arg.var z)) =>
  when (ctx.currFn == g && x == z) $ do
    -- dbgTrace ("preserveTailCall " ++ toString b) $ fun _ => do
    ps ← getParamInfo (Key.decl g);
    ownParamsUsingArgs ys ps
| _, _ => pure ()

def updateParamSet (ctx : BorrowInfCtx) (ps : Array Param) : BorrowInfCtx :=
{ paramSet := ps.foldl (fun s p => s.insert p.x.idx) ctx.paramSet, .. ctx }

partial def collectFnBody : FnBody → M Unit
| FnBody.jdecl j ys v b => do
  adaptReader (fun ctx => updateParamSet ctx ys) (collectFnBody v);
  ctx ← read;
  updateParamMap (Key.jp ctx.currFn j);
  collectFnBody b
| FnBody.vdecl x _ v b => collectFnBody b *> collectExpr x v *> preserveTailCall x v b
| FnBody.jmp j ys      => do
  ctx ← read;
  ps ← getParamInfo (Key.jp ctx.currFn j);
  ownArgsUsingParams ys ps; -- for making sure the join point can reuse
  ownParamsUsingArgs ys ps  -- for making sure the tail call is preserved
| FnBody.case _ _ _ alts => alts.mfor $ fun alt => collectFnBody alt.body
| e                      => unless (e.isTerminal) $ collectFnBody e.body

@[specialize] partial def whileModifingOwnedAux (x : M Unit) : Unit → M Unit
| _ => do
  modify $ fun s => { modifiedOwned := false, .. s };
  x;
  s ← get;
  if s.modifiedOwned then whileModifingOwnedAux ()
  else pure ()

/- Keep executing `x` while it modifies ownedSet -/
@[inline] def whileModifingOwned (x : M Unit) : M Unit :=
whileModifingOwnedAux x ()

partial def collectDecl : Decl → M Unit
| Decl.fdecl f ys _ b   =>
  adaptReader (fun ctx => let ctx := updateParamSet ctx ys; { currFn := f, .. ctx }) $ do
   modify $ fun (s : BorrowInfState) => { owned := {}, .. s };
   whileModifingOwned (collectFnBody b);
   updateParamMap (Key.decl f)
| _ => pure ()

@[specialize] partial def whileModifingParamMapAux (x : M Unit) : Unit → M Unit
| _ => do
  modify $ fun s => { modifiedParamMap := false, .. s };
  s ← get;
  -- dbgTrace (toString s.map) $ fun _ => do
  x;
  s ← get;
  if s.modifiedParamMap then whileModifingParamMapAux ()
  else pure ()

/- Keep executing `x` while it modifies paramMap -/
@[inline] def whileModifingParamMap (x : M Unit) : M Unit :=
whileModifingParamMapAux x ()

def collectDecls (decls : Array Decl) : M ParamMap :=
do whileModifingParamMap (decls.mfor collectDecl);
   s ← get;
   pure s.map

def infer (env : Environment) (decls : Array Decl) : ParamMap :=
(collectDecls decls { env := env }).run' { map := mkInitParamMap env decls }

end Borrow

def inferBorrow (decls : Array Decl) : CompilerM (Array Decl) :=
do env ← getEnv;
   let paramMap := Borrow.infer env decls;
   pure (Borrow.applyParamMap decls paramMap)

end IR
end Lean
