/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.runtime
import init.lean.compiler.ir.compilerm
import init.lean.compiler.ir.livevars

namespace Lean
namespace IR
namespace ExplicitRC
/- Insert explicit RC instructions. So, it assumes the input code does not contain `inc` nor `dec` instructions.
   This transformation is applied before lower level optimizations
   that introduce the instructions `release` and `set`
-/

structure VarInfo :=
(ref        : Bool := true)  -- true if the variable may be a reference (aka pointer) at runtime
(persistent : Bool := false) -- true if the variable is statically known to be marked a Persistent at runtime
(consume    : Bool := false) -- true if the variable RC must be "consumed"

abbrev VarMap := RBMap VarId VarInfo (λ x y, x.idx < y.idx)

structure Context :=
(env            : Environment)
(decls          : Array Decl)
(varMap         : VarMap := {})
(jpLiveVarMap   : JPLiveVarMap := {}) -- map: join point => live variables
(localCtx       : LocalContext := {}) -- we use it to store the join point declarations

def getDecl (ctx : Context) (fid : FunId) : Decl :=
 match findEnvDecl' ctx.env fid ctx.decls with
| some decl := decl
| none      := default _ -- unreachable if well-formed

def getVarInfo (ctx : Context) (x : VarId) : VarInfo :=
match ctx.varMap.find x with
| some info := info
| none      := {} -- unreachable in well-formed code

def getJPParams (ctx : Context) (j : JoinPointId) : Array Param :=
match ctx.localCtx.getJPParams j with
| some ps := ps
| none    := Array.empty -- unreachable in well-formed code

def getJPLiveVars (ctx : Context) (j : JoinPointId) : LiveVarSet :=
match ctx.jpLiveVarMap.find j with
| some s := s
| none   := {}

def mustConsume (ctx : Context) (x : VarId) : Bool :=
let info := getVarInfo ctx x;
info.ref && !info.persistent && info.consume

@[inline] def addInc (x : VarId) (b : FnBody) (n := 1) : FnBody :=
if n == 0 then b else FnBody.inc x n true b

@[inline] def addDec (x : VarId) (b : FnBody) : FnBody :=
FnBody.dec x 1 true b

private def updateRefUsingCtorInfo (ctx : Context) (x : VarId) (c : CtorInfo) : Context :=
if c.isRef then ctx
else let m := ctx.varMap;
  { varMap := match m.find x with
    | some info := m.insert x { ref := false, .. info } -- I really want a Lenses library + notation
    | none      := m,
    .. ctx }

private def addDecForAlt (ctx : Context) (caseLiveVars altLiveVars : LiveVarSet) (b : FnBody) : FnBody :=
caseLiveVars.fold
  (λ b x, if !altLiveVars.contains x && mustConsume ctx x then addDec x b else b)
  b

/- `isFirstOcc xs x i = true` if `xs[i]` is the first occurrence of `xs[i]` in `xs` -/
private def isFirstOcc (xs : Array Arg) (i : Nat) : Bool :=
let x := xs.get i;
i.all $ λ j, xs.get j != x

/- Return true if `x` also occurs in `ys` in a position that is not consumed.
   That is, it is also passed as a borrow reference. -/
@[specialize]
private def isBorrowParamAux (x : VarId) (ys : Array Arg) (consumeParamPred : Nat → Bool) : Bool :=
ys.size.any $ λ i,
  let y := ys.get i;
  match y with
  | Arg.irrelevant := false
  | Arg.var y      := x == y && !consumeParamPred i

private def isBorrowParam (x : VarId) (ys : Array Arg) (ps : Array Param) : Bool :=
isBorrowParamAux x ys (λ i, !(ps.get i).borrow)

/-
Return `n`, the number of times `x` is consumed.
- `ys` is a sequence of instruction parameters where we search for `x`.
- `consumeParamPred i = true` if parameter `i` is consumed.
-/
@[specialize]
private def getNumConsumptions (x : VarId) (ys : Array Arg) (consumeParamPred : Nat → Bool) : Nat :=
ys.size.fold
  (λ i n,
    let y := ys.get i;
    match y with
    | Arg.irrelevant := n
    | Arg.var y      := if x == y && consumeParamPred i then n+1 else n)
  0

@[specialize]
private def addIncBeforeAux (ctx : Context) (xs : Array Arg) (consumeParamPred : Nat → Bool) (b : FnBody) (liveVarsAfter : LiveVarSet) : FnBody :=
xs.size.fold
  (λ i b,
    let x := xs.get i;
    match x with
    | Arg.irrelevant := b
    | Arg.var x :=
      let info := getVarInfo ctx x;
      if !info.ref || info.persistent || !isFirstOcc xs i then b
      else
        let numConsuptions := getNumConsumptions x xs consumeParamPred; -- number of times the argument is
        let numIncs :=
          if !info.consume ||                     -- `x` is not a variable that must be consumed by the current procedure
             liveVarsAfter.contains x ||          -- `x` is live after executing instruction
             isBorrowParamAux x xs consumeParamPred  -- `x` is used in a position that is passed as a borrow reference
          then numConsuptions
          else numConsuptions - 1;
        -- dbgTrace ("addInc " ++ toString x ++ " nconsumptions: " ++ toString numConsuptions ++ " incs: " ++ toString numIncs
        --         ++ " consume: " ++ toString info.consume ++ " live: " ++ toString (liveVarsAfter.contains x)
        --         ++ " borrowParam : " ++ toString (isBorrowParamAux x xs consumeParamPred)) $ λ _,
        addInc x b numIncs)
  b

private def addIncBefore (ctx : Context) (xs : Array Arg) (ps : Array Param) (b : FnBody) (liveVarsAfter : LiveVarSet) : FnBody :=
addIncBeforeAux ctx xs (λ i, !(ps.get i).borrow) b liveVarsAfter

/- See `addIncBeforeAux`/`addIncBefore` for the procedure that inserts `inc` operations before an application.  -/
private def addDecAfterFullApp (ctx : Context) (xs : Array Arg) (ps : Array Param) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody :=
xs.size.fold
  (λ i b,
    match xs.get i with
    | Arg.irrelevant := b
    | Arg.var x      :=
      /- We must add a `dec` if `x` must be consumed, it is alive after the application,
         and it has been borrowed by the application.
         Remark: `x` may occur multiple times in the application (e.g., `f x y x`).
         This is why we check whether it is the first occurrence. -/
      if mustConsume ctx x && isFirstOcc xs i && isBorrowParam x xs ps && !bLiveVars.contains x then
        addDec x b
      else b)
  b

private def addIncBeforeConsumeAll (ctx : Context) (xs : Array Arg) (b : FnBody) (liveVarsAfter : LiveVarSet) : FnBody :=
addIncBeforeAux ctx xs (λ i, true) b liveVarsAfter

/- Add `dec` instructions for parameters that are references, are not alive in `b`, and are not borrow.
   That is, we must make sure these parameters are consumed. -/
private def addDecForDeadParams (ps : Array Param) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody :=
ps.foldl
  (λ b p, if !p.borrow && p.ty.isObj && !bLiveVars.contains p.x then addDec p.x b else b)
  b

private def isPersistent : Expr → Bool
| (Expr.fap c xs) := xs.isEmpty -- all global constants are persistent objects
| _               := false

/- We do not need to consume the projection of a variable that is not consumed -/
private def consumeExpr (m : VarMap) : Expr → Bool
| (Expr.proj i x) := match m.find x with
  | some info := info.consume
  | none      := true
| other := true

/- Return true iff `v` at runtime is a scalar value stored in a tagged pointer.
   We do not need RC operations for this kind of value. -/
private def isScalarBoxedInTaggedPtr (v : Expr) : Bool :=
match v with
| Expr.ctor c ys          := c.size == 0 && c.ssize == 0 && c.usize == 0
| Expr.lit (LitVal.num n) := n ≤ maxSmallNat
| _ := false

private def updateVarInfo (ctx : Context) (x : VarId) (t : IRType) (v : Expr) : Context :=
{ varMap := ctx.varMap.insert x {
      ref := t.isObj && !isScalarBoxedInTaggedPtr v,
      persistent := isPersistent v,
      consume := consumeExpr ctx.varMap v },
  .. ctx }

private def addDecIfNeeded (ctx : Context) (x : VarId) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody :=
if mustConsume ctx x && !bLiveVars.contains x then addDec x b else b

private def processVDecl (ctx : Context) (z : VarId) (t : IRType) (v : Expr) (b : FnBody) (bLiveVars : LiveVarSet) : FnBody × LiveVarSet :=
-- dbgTrace ("processVDecl " ++ toString z ++ " " ++ toString (format v)) $ λ _,
let b := match v with
  | (Expr.ctor _ ys)       := addIncBeforeConsumeAll ctx ys (FnBody.vdecl z t v b) bLiveVars
  | (Expr.reuse _ _ _ ys)  := addIncBeforeConsumeAll ctx ys (FnBody.vdecl z t v b) bLiveVars
  | (Expr.proj _ x)        :=
    let b := addDecIfNeeded ctx x b bLiveVars;
    let b := if (getVarInfo ctx x).consume then addInc z b else b;
    (FnBody.vdecl z t v b)
  | (Expr.uproj _ x)       := FnBody.vdecl z t v (addDecIfNeeded ctx x b bLiveVars)
  | (Expr.sproj _ _ x)     := FnBody.vdecl z t v (addDecIfNeeded ctx x b bLiveVars)
  | (Expr.fap f ys)        :=
    -- dbgTrace ("processVDecl " ++ toString v) $ λ _,
    let ps := (getDecl ctx f).params;
    let b  := addDecAfterFullApp ctx ys ps b bLiveVars;
    let b  := FnBody.vdecl z t v b;
    addIncBefore ctx ys ps b bLiveVars
  | (Expr.pap _ ys)        := addIncBeforeConsumeAll ctx ys (FnBody.vdecl z t v b) bLiveVars
  | (Expr.ap x ys)         :=
    let ysx := ys.push (Arg.var x); -- TODO: avoid temporary array allocation
    addIncBeforeConsumeAll ctx ysx (FnBody.vdecl z t v b) bLiveVars
  | (Expr.unbox x)         := FnBody.vdecl z t v (addDecIfNeeded ctx x b bLiveVars)
  | other                  := FnBody.vdecl z t v b;  -- Expr.reset, Expr.box, Expr.lit are handled here
let liveVars := updateLiveVars v bLiveVars;
let liveVars := liveVars.erase z;
(b, liveVars)

def updateVarInfoWithParams (ctx : Context) (ps : Array Param) : Context :=
let m := ps.foldl (λ (m : VarMap) p, m.insert p.x { ref := p.ty.isObj, consume := !p.borrow }) ctx.varMap;
{ varMap := m, .. ctx }

partial def visitFnBody : FnBody → Context → (FnBody × LiveVarSet)
| (FnBody.vdecl x t v b)    ctx :=
  let ctx := updateVarInfo ctx x t v;
  let (b, bLiveVars) := visitFnBody b ctx;
  processVDecl ctx x t v b bLiveVars
| (FnBody.jdecl j xs v b)   ctx :=
  let (v, vLiveVars) := visitFnBody v (updateVarInfoWithParams ctx xs);
  let v   := addDecForDeadParams xs v vLiveVars;
  let ctx := { jpLiveVarMap := updateJPLiveVarMap j xs v ctx.jpLiveVarMap, .. ctx };
  let (b, bLiveVars) := visitFnBody b ctx;
  (FnBody.jdecl j xs v b, bLiveVars)
| (FnBody.uset x i y b)     ctx :=
  let (b, s) := visitFnBody b ctx;
  -- We don't need to insert `y` since we only need to track live variables that are references at runtime
  let s      := s.insert x;
  (FnBody.uset x i y b, s)
| (FnBody.sset x i o y t b) ctx :=
  let (b, s) := visitFnBody b ctx;
  -- We don't need to insert `y` since we only need to track live variables that are references at runtime
  let s      := s.insert x;
  (FnBody.sset x i o y t b, s)
| (FnBody.mdata m b)        ctx :=
  let (b, s) := visitFnBody b ctx;
  (FnBody.mdata m b, s)
| b@(FnBody.case tid x alts) ctx :=
  let caseLiveVars := collectLiveVars b ctx.jpLiveVarMap;
  let alts         := alts.map $ λ alt, match alt with
    | Alt.ctor c b  :=
      let ctx              := updateRefUsingCtorInfo ctx x c;
      let (b, altLiveVars) := visitFnBody b ctx;
      let b                := addDecForAlt ctx caseLiveVars altLiveVars b;
      Alt.ctor c b
    | Alt.default b :=
      let (b, altLiveVars) := visitFnBody b ctx;
      let b                := addDecForAlt ctx caseLiveVars altLiveVars b;
      Alt.default b;
  (FnBody.case tid x alts, caseLiveVars)
| b@(FnBody.ret x) ctx :=
  match x with
  | Arg.var x :=
    let info := getVarInfo ctx x;
    if info.ref && !info.persistent && !info.consume then (addInc x b, {x}) else (b, {x})
  | _         := (b, {})
| b@(FnBody.jmp j xs) ctx :=
  let jLiveVars := getJPLiveVars ctx j;
  let ps        := getJPParams ctx j;
  let b         := addIncBefore ctx xs ps b jLiveVars;
  let bLiveVars := collectLiveVars b ctx.jpLiveVarMap;
  (b, bLiveVars)
| FnBody.unreachable _ := (FnBody.unreachable, {})
| other ctx := (other, {}) -- unreachable if well-formed

partial def visitDecl (env : Environment) (decls : Array Decl) : Decl → Decl
| (Decl.fdecl f xs t b) :=
  let ctx : Context  := { env := env, decls := decls };
  let ctx := updateVarInfoWithParams ctx xs;
  let (b, bLiveVars) := visitFnBody b ctx;
  let b := addDecForDeadParams xs b bLiveVars;
  Decl.fdecl f xs t b
| other := other

end ExplicitRC

def explicitRC (decls : Array Decl) : CompilerM (Array Decl) :=
do env ← getEnv,
   pure $ decls.map (ExplicitRC.visitDecl env decls)

end IR
end Lean
