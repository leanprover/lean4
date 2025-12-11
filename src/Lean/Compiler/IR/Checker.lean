/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.IR.CompilerM

public section

namespace Lean.IR.Checker

@[extern "lean_get_max_ctor_fields"]
opaque getMaxCtorFields : Unit → Nat
def maxCtorFields := getMaxCtorFields ()

@[extern "lean_get_max_ctor_scalars_size"]
opaque getMaxCtorScalarsSize : Unit → Nat
def maxCtorScalarsSize := getMaxCtorScalarsSize ()

@[extern "lean_get_max_ctor_tag"]
opaque getMaxCtorTag : Unit → Nat
def maxCtorTag := getMaxCtorTag ()

@[extern "lean_get_usize_size"]
opaque getUSizeSize : Unit → Nat
def usizeSize := getUSizeSize ()

structure CheckerContext where
  localCtx : LocalContext := {}
  currentDecl : Decl
  decls : Array Decl

structure CheckerState where
  foundVars : IndexSet := {}

abbrev M := ReaderT CheckerContext <| StateRefT CheckerState CompilerM

def throwCheckerError {α : Type} (msg : String) : M α := do
  let declName := (← read).currentDecl.name
  throwError "failed to compile definition, compiler IR check failed at `{.ofConstName declName}`. Error: {msg}"

def markIndex (i : Index) : M Unit := do
  let s ← get
  if s.foundVars.contains i then
    throwCheckerError s!"variable / join point index {i} has already been used"
  modify fun s => { s with foundVars := s.foundVars.insert i }

def markVar (x : VarId) : M Unit :=
  markIndex x.idx

def markJP (j : JoinPointId) : M Unit :=
  markIndex j.idx

def getDecl (c : Name) : M Decl := do
  let ctx ← read
  match findEnvDecl' (← getEnv) c ctx.decls with
  | none   => throwCheckerError s!"depends on declaration '{c}', which has no executable code; consider marking definition as 'noncomputable'"
  | some d => pure d

def checkVar (x : VarId) : M Unit := do
  let ctx ← read
  unless ctx.localCtx.isLocalVar x.idx || ctx.localCtx.isParam x.idx do
   throwCheckerError s!"unknown variable '{x}'"

def checkJP (j : JoinPointId) : M Unit := do
  let ctx ← read
  unless ctx.localCtx.isJP j.idx do
   throwCheckerError s!"unknown join point '{j}'"

def checkArg (a : Arg) : M Unit :=
  match a with
  | .var x => checkVar x
  | .erased => pure ()

def checkArgs (as : Array Arg) : M Unit :=
  as.forM checkArg

@[inline] def checkEqTypes (ty₁ ty₂ : IRType) : M Unit := do
  unless ty₁ == ty₂ do
    throwCheckerError "unexpected type '{ty₁}' != '{ty₂}'"

@[inline] def checkType (ty : IRType) (p : IRType → Bool) (suffix? : Option String := none): M Unit := do
  unless p ty do
   let mut msg := s!"unexpected type '{ty}'"
   if let some suffix := suffix? then
     msg := s!"{msg}, {suffix}"
   throwCheckerError msg

def checkObjType (ty : IRType) : M Unit := checkType ty IRType.isObj "object expected"

def checkScalarType (ty : IRType) : M Unit := checkType ty IRType.isScalar "scalar expected"

def getType (x : VarId) : M IRType := do
  let ctx ← read
  match ctx.localCtx.getType x with
  | some ty => pure ty
  | none    => throwCheckerError s!"unknown variable '{x}'"

@[inline] def checkVarType (x : VarId) (p : IRType → Bool) (suffix? : Option String := none) : M Unit := do
  let ty ← getType x; checkType ty p suffix?

def checkObjVar (x : VarId) : M Unit :=
  checkVarType x IRType.isObj "object expected"

def checkScalarVar (x : VarId) : M Unit :=
  checkVarType x IRType.isScalar "scalar expected"

def checkFullApp (c : FunId) (ys : Array Arg) : M Unit := do
  let decl ← getDecl c
  unless ys.size == decl.params.size do
    throwCheckerError s!"incorrect number of arguments to '{c}', {ys.size} provided, {decl.params.size} expected"
  checkArgs ys

def checkPartialApp (c : FunId) (ys : Array Arg) : M Unit := do
  let decl ← getDecl c
  unless ys.size < decl.params.size do
    throwCheckerError s!"too many arguments to partial application '{c}', num. args: {ys.size}, arity: {decl.params.size}"
  checkArgs ys

def checkExpr (ty : IRType) (e : Expr) : M Unit := do
  match e with
  | .pap f ys =>
    checkPartialApp f ys
    -- Partial applications should always produce a closure object.
    checkObjType ty
  | .ap x ys =>
    checkObjVar x
    checkArgs ys
    -- Applications of closures should always produce a boxed value.
    checkObjType ty
  | .fap f ys =>
    checkFullApp f ys
  | .ctor c ys =>
    if c.cidx > maxCtorTag && c.isRef then
      throwCheckerError s!"tag for constructor '{c.name}' is too big, this is a limitation of the current runtime"
    if c.size > maxCtorFields then
      throwCheckerError s!"constructor '{c.name}' has too many fields"
    if c.ssize + c.usize * usizeSize > maxCtorScalarsSize then
      throwCheckerError s!"constructor '{c.name}' has too many scalar fields"
    if c.isRef then
      checkObjType ty
      checkArgs ys
  | .reset _ x =>
    checkObjVar x
    checkObjType ty
  | .reuse x _ _ ys =>
    checkObjVar x
    checkArgs ys
    checkObjType ty
  | .box xty x =>
    checkObjType ty
    checkScalarVar x
    checkVarType x (· == xty)
  | .unbox x =>
    checkScalarType ty
    checkObjVar x
  | .proj i x =>
    let xType ← getType x;
    /-
    Projections are a valid operation on `tobject`. Thus they should also
    be a valid operation for both `object`, `tagged` and unboxed values
    as they are subtypes.
    -/
    match xType with
    | .object | .tobject =>
      checkObjType ty
    | .struct _ tys | .union _ tys =>
      if h : i < tys.size then
        checkEqTypes (tys[i]) ty
      else
        throwCheckerError "invalid proj index"
    | .tagged => pure ()
    | _ => throwCheckerError s!"unexpected IR type '{xType}'"
  | .uproj _ x =>
    checkObjVar x
    checkType ty (· == .usize)
  | .sproj _ _ x =>
    checkObjVar x
    checkScalarType ty
  | .isShared x =>
    checkObjVar x
    checkType ty (· == .uint8)
  | .lit (LitVal.str _) =>
    checkObjType ty
  | .lit _ => pure ()

@[inline] def withParams (ps : Array Param) (k : M Unit) : M Unit := do
  let ctx ← read
  let localCtx ← ps.foldlM (init := ctx.localCtx) fun (ctx : LocalContext) p => do
     markVar p.x
     pure <| ctx.addParam p
  withReader (fun _ => { ctx with localCtx }) k

partial def checkFnBody (fnBody : FnBody) : M Unit := do
  match fnBody with
  | .vdecl x t v b    => do
    checkExpr t v
    markVar x
    withReader (fun ctx => { ctx with localCtx := ctx.localCtx.addLocal x t v }) (checkFnBody b)
  | .jdecl j ys v b => do
    markJP j
    withParams ys (checkFnBody v)
    withReader (fun ctx => { ctx with localCtx := ctx.localCtx.addJP j ys v }) (checkFnBody b)
  | .set x _ y b =>
    checkVar x
    checkArg y
    checkFnBody b
  | .uset x _ y b =>
    checkVar x
    checkVar y
    checkFnBody b
  | .sset x _ _ y _ b =>
    checkVar x
    checkVar y
    checkFnBody b
  | .setTag x _ b =>
    checkVar x
    checkFnBody b
  | .inc x _ _ _ b =>
    checkVar x
    checkFnBody b
  | .dec x _ _ _ b =>
    checkVar x
    checkFnBody b
  | .del x b =>
    checkVar x
    checkFnBody b
  | .jmp j ys =>
    checkJP j
    checkArgs ys
  | .ret x =>
    checkArg x
  | .case _ x _ alts =>
    checkVar x
    alts.forM (checkFnBody ·.body)
  | .unreachable => pure ()

def checkDecl : Decl → M Unit
  | .fdecl (xs := xs) (body := b) .. => withParams xs (checkFnBody b)
  | .extern (xs := xs) .. => withParams xs (pure ())

end Checker

def checkDecl (decls : Array Decl) (decl : Decl) : CompilerM Unit := do
  Checker.checkDecl decl { decls, currentDecl := decl } |>.run' {}

def checkDecls (decls : Array Decl) : CompilerM Unit :=
  decls.forM (checkDecl decls)

end IR
end Lean
