/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.compiler.ir.compilerm
import init.lean.compiler.ir.normids

namespace Lean
namespace IR

namespace Borrow

inductive Key
| decl (name : FunId)
| jp   (name : FunId) (jpid : JoinPointId)

namespace Key
def beq : Key → Key → Bool
| (decl n₁)   (decl n₂)   := n₁ == n₂
| (jp n₁ id₁) (jp n₂ id₂) := n₁ == n₂ && id₁ == id₂
| _           _           := false

instance : HasBeq Key := ⟨beq⟩

def getHash : Key → USize
| (decl n)  := hash n
| (jp n id) := mixHash (hash n) (hash id)

instance : Hashable Key := ⟨getHash⟩
end Key

def setBorrow (ps : Array Param) : Array Param :=
ps.hmap $ λ p, { borrow := true, .. p }

abbrev ParamMap := HashMap Key (Array Param)

def ParamMap.fmt (map : ParamMap) : Format :=
let fmts := map.fold (λ fmt k ps,
  let k := match k with
    | Key.decl n  := format n
    | Key.jp n id := format n ++ ":" ++ format id in
  fmt ++ Format.line ++ k ++ " -> " ++ formatParams ps)
 Format.nil in
"{" ++ (Format.nest 1 fmts) ++ "}"

instance : HasFormat ParamMap := ⟨ParamMap.fmt⟩
instance : HasToString ParamMap := ⟨λ m, Format.pretty (format m)⟩

local attribute [instance] monadInhabited

namespace InitParamMap

partial def visitFnBody : FnBody → ReaderT FunId (State ParamMap) Unit
| (FnBody.jdecl j xs v b) := do
  fnid ← read,
  modify $ λ m, m.insert (Key.jp fnid j) (setBorrow xs),
  visitFnBody b
| e :=
  unless (e.isTerminal) $ do
    let (instr, b) := e.split,
    visitFnBody b

def visitDecls (decls : Array Decl) : State ParamMap Unit :=
decls.mfor $ λ decl, match decl with
  | Decl.fdecl f xs _ b := do
    modify $ λ m, m.insert (Key.decl f) (setBorrow xs),
    visitFnBody b f
  | _ := pure ()
end InitParamMap

def mkInitParamMap (decls : Array Decl) : ParamMap :=
(InitParamMap.visitDecls decls *> get).run' {}

namespace ApplyParamMap

partial def visitFnBody : FnBody → FunId → ParamMap → FnBody
| (FnBody.jdecl j xs v b) fnid map :=
  let b := visitFnBody b fnid map in
  match map.find (Key.jp fnid j) with
  | some ys := FnBody.jdecl j ys v b
  | none    := FnBody.jdecl j xs v b
| e fnid map :=
  if e.isTerminal then e
  else
    let (instr, b) := e.split in
    let b := visitFnBody b fnid map in
    instr <;> b

def visitDecls (decls : Array Decl) (map : ParamMap) : Array Decl :=
decls.hmap $ λ decl, match decl with
  | Decl.fdecl f xs ty b :=
    let b := visitFnBody b f map in
    match map.find (Key.decl f) with
    | some xs := Decl.fdecl f xs ty b
    | none    := Decl.fdecl f xs ty b
  | other := other

end ApplyParamMap

def applyParamMap (decls : Array Decl) (map : ParamMap) : Array Decl :=
-- dbgTrace ("applyParamMap " ++ toString map) $ λ _,
ApplyParamMap.visitDecls decls map

structure BorrowInfCtx :=
(env : Environment) (currFn : FunId := default _) (paramSet : IndexSet := {})

structure BorrowInfState :=
(map : ParamMap) (owned : IndexSet := {}) (modifiedOwned : Bool := false) (modifiedParamMap : Bool := false)

abbrev M := ReaderT BorrowInfCtx (State BorrowInfState)

def markModifiedParamMap : M Unit :=
modify $ λ s, { modifiedParamMap := true, .. s }

def ownVar (x : VarId) : M Unit :=
-- dbgTrace ("ownVar " ++ toString x) $ λ _,
modify $ λ s,
  if s.owned.contains x.idx then s
  else { owned := s.owned.insert x.idx, modifiedOwned := true, .. s }

def ownArg (x : Arg) : M Unit :=
match x with
| (Arg.var x) := ownVar x
| _           := pure ()

def ownArgs (xs : Array Arg) : M Unit :=
xs.mfor ownArg

def isOwned (x : VarId) : M Bool :=
do s ← get,
   pure $ s.owned.contains x.idx

def updateParamMap (k : Key) : M Unit :=
do
s ← get,
match s.map.find k with
| some ps := do
  ps ← ps.hmmap $ λ (p : Param),
   if p.borrow && s.owned.contains p.x.idx then do
     markModifiedParamMap, pure { borrow := false, .. p }
   else
     pure p,
  modify $ λ s, { map := s.map.insert k ps, .. s }
| none    := pure ()

def getParamInfo (k : Key) : M (Array Param) :=
do
s ← get,
match s.map.find k with
| some ps := pure ps
| none    :=
  match k with
  | (Key.decl fn) := do
    ctx ← read,
    match findEnvDecl ctx.env fn with
    | some decl := pure decl.params
    | none      := pure Array.empty   -- unreachable if well-formed input
  | _ := pure Array.empty -- unreachable if well-formed input

/- For each ps[i], if ps[i] is owned, then mark xs[i] as owned. -/
def ownArgsUsingParams (xs : Array Arg) (ps : Array Param) : M Unit :=
xs.size.mfor $ λ i, do
  let x := xs.get i,
  let p := ps.get i,
  unless p.borrow $ ownArg x

/- For each xs[i], if xs[i] is owned, then mark ps[i] as owned.
   We use this action to preserve tail calls. That is, if we have
   a tail call `f xs`, if the i-th parameter is borrowed, but `xs[i]` is owned
   we would have to insert a `dec xs[i]` after `f xs` and consequently
   "break" the tail call. -/
def ownParamsUsingArgs (xs : Array Arg) (ps : Array Param) : M Unit :=
xs.size.mfor $ λ i, do
  let x := xs.get i,
  let p := ps.get i,
  match x with
  | Arg.var x := mwhen (isOwned x) $ ownVar p.x
  | _         := pure ()

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
do
ctx ← read,
xs.mfor $ λ x,
  match x with
  | Arg.var x := when (ctx.paramSet.contains x.idx) $ ownVar x
  | _ := pure ()

def collectExpr (z : VarId) : Expr → M Unit
| (Expr.reset x)        := ownVar x
| (Expr.reuse x _ _ ys) := ownVar x *> ownArgsIfParam ys
| (Expr.ctor _ xs)      := ownArgsIfParam xs
| (Expr.proj _ x)       := mwhen (isOwned z) $ ownVar x
| (Expr.fap g xs)       := do ps ← getParamInfo (Key.decl g),
  -- dbgTrace ("collectExpr: " ++ toString g ++ " " ++ toString (formatParams ps)) $ λ _,
  ownArgsUsingParams xs ps
| (Expr.ap x ys)        := ownVar x *> ownArgs ys
| (Expr.pap _ xs)       := ownArgs xs
| other                 := pure ()

def preserveTailCall (x : VarId) (v : Expr) (b : FnBody) : M Unit :=
do ctx ← read,
match v, b with
| (Expr.fap g ys), (FnBody.ret (Arg.var z)) :=
  when (ctx.currFn == g && x == z) $ do
    -- dbgTrace ("preserveTailCall " ++ toString b) $ λ _, do
    ps ← getParamInfo (Key.decl g),
    ownParamsUsingArgs ys ps
| _, _ := pure ()

def updateParamSet (ctx : BorrowInfCtx) (ps : Array Param) : BorrowInfCtx :=
{ paramSet := ps.foldl (λ s p, s.insert p.x.idx) ctx.paramSet, .. ctx }

partial def collectFnBody : FnBody → M Unit
| (FnBody.jdecl j ys _ b) := do
  adaptReader (λ ctx, updateParamSet ctx ys) (collectFnBody b),
  ctx ← read,
  updateParamMap (Key.jp ctx.currFn j)
| (FnBody.vdecl x _ v b) := collectFnBody b *> collectExpr x v -- *> preserveTailCall x v b
| (FnBody.jmp j ys)      := do
  ctx ← read,
  ps ← getParamInfo (Key.jp ctx.currFn j),
  ownArgsUsingParams ys ps, -- for making sure the join point can reuse
  ownParamsUsingArgs ys ps  -- for making sure the tail call is preserved
| (FnBody.case _ _ alts) := alts.mfor $ λ alt, collectFnBody alt.body
| e                      := unless (e.isTerminal) $ collectFnBody e.body

@[specialize] partial def whileModifingOwnedAux (x : M Unit) : Unit → M Unit
| _ := do
  modify $ λ s, { modifiedOwned := false, .. s },
  x,
  s ← get,
  if s.modifiedOwned then whileModifingOwnedAux ()
  else pure ()

/- Keep executing `x` while it modifies ownedSet -/
@[inline] def whileModifingOwned (x : M Unit) : M Unit :=
whileModifingOwnedAux x ()

partial def collectDecl : Decl → M Unit
| (Decl.fdecl f ys _ b) :=
  adaptReader (λ ctx, let ctx := updateParamSet ctx ys in { currFn := f, .. ctx }) $ do
   modify $ λ s : BorrowInfState, { owned := {}, .. s },
   whileModifingOwned (collectFnBody b),
   updateParamMap (Key.decl f)
| _ := pure ()

@[specialize] partial def whileModifingParamMapAux (x : M Unit) : Unit → M Unit
| _ := do
  modify $ λ s, { modifiedParamMap := false, .. s },
  s ← get,
  -- dbgTrace (toString s.map) $ λ _, do
  x,
  s ← get,
  if s.modifiedParamMap then whileModifingParamMapAux ()
  else pure ()

/- Keep executing `x` while it modifies paramMap -/
@[inline] def whileModifingParamMap (x : M Unit) : M Unit :=
whileModifingParamMapAux x ()

def collectDecls (decls : Array Decl) : M ParamMap :=
do
whileModifingParamMap (decls.mfor collectDecl),
s ← get,
pure s.map

def infer (env : Environment) (decls : Array Decl) : ParamMap :=
(collectDecls decls { env := env }).run' { map := mkInitParamMap decls }

end Borrow

def inferBorrow (decls : Array Decl) : CompilerM (Array Decl) :=
do
env ← getEnv,
let decls    := decls.hmap Decl.normalizeIds,
let paramMap := Borrow.infer env decls,
pure (Borrow.applyParamMap decls paramMap)

end IR
end Lean
