/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.Simp.Result
public import Lean.Meta.Sym.Simp.App
import Lean.Meta.Sym.SynthInstance
import Lean.Meta.Sym.Canon
import Lean.Meta.Sym.LitValues
public import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr
public import Lean.Meta.Tactic.Grind.Arith.Linear.VarRename
public import Lean.Meta.AppBuilder
import Lean.Data.RArray
public import Init.Grind.Module.NatModuleNorm
public section

namespace Lean.Meta.Sym.Arith

private structure ModuleContext where
  addFn : Expr
  zero : Expr
  nsmulFn : Expr
  subFn? : Option Expr := none
  negFn? : Option Expr := none
  zsmulFn? : Option Expr := none

private structure ModuleState where
  vars : Array Expr := #[]
  varMap : PHashMap ExprPtr Nat := {}
  /-- Cached operation comparisons at default transparency. -/
  fnMap : PHashMap (ExprPtr × ExprPtr) Bool := {}

private abbrev ModuleM := ReaderT ModuleContext (StateRefT ModuleState SymM)

private def moduleVar (e : Expr) : ModuleM Grind.Linarith.Expr := do
  if let some i := (← get).varMap.find? { expr := e } then return .var i
  if let some i ← (← get).vars.findIdxM? (fun a => withReducibleAndInstances <| isDefEq e a) then
    modify fun s => { s with varMap := s.varMap.insert { expr := e } i }
    return .var i
  let i := (← get).vars.size
  modify fun s => { s with vars := s.vars.push e, varMap := s.varMap.insert { expr := e } i }
  return .var i

private def matchesFn (e fn : Expr) (arity : Nat) : ModuleM Bool := do
  let e := e.getBoundedAppFn arity
  let key := (⟨e⟩, ⟨fn⟩)
  if let some result := (← get).fnMap.find? key then return result
  let result ← withDefault <| isDefEq e fn
  modify fun s => { s with fnMap := s.fnMap.insert key result }
  return result

private partial def reifyModule (e : Expr) : ModuleM Grind.Linarith.Expr := withIncRecDepth do
  let ctx ← read
  let numeral : Option Nat := (Sym.getNatValue? e).run
  if e.isAppOfArity ``Zero.zero 2 || numeral == some 0 then
    if ← matchesFn e ctx.zero 0 then return .zero
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    if ← matchesFn e ctx.addFn 2 then return .add (← reifyModule a) (← reifyModule b)
  | HSub.hSub _ _ _ _ a b =>
    if let some fn := ctx.subFn? then
      if ← matchesFn e fn 2 then return .sub (← reifyModule a) (← reifyModule b)
  | Neg.neg _ _ a =>
    if let some fn := ctx.negFn? then
      if ← matchesFn e fn 1 then return .neg (← reifyModule a)
  | HSMul.hSMul _ _ _ _ n a =>
    if ← matchesFn e ctx.nsmulFn 2 then
      if let some n := (Sym.getNatValue? n).run then return .natMul n (← reifyModule a)
    if let some fn := ctx.zsmulFn? then
      if ← matchesFn e fn 2 then
        if let some n := (Sym.getIntValue? n).run then return .intMul n (← reifyModule a)
  | _ => pure ()
  if let some n := numeral then
    let type ← inferType e
    if type.isConstOf ``Nat then
      let one := toExpr (1 : Nat)
      if ← withDefault <| isDefEq e (mkApp2 ctx.nsmulFn (toExpr n) one) then
        return .natMul n (← moduleVar one)
    if type.isConstOf ``Int then
      if let some fn := ctx.zsmulFn? then
        let one := toExpr (1 : Int)
        if ← withDefault <| isDefEq e (mkApp2 fn (toExpr (n : Int)) one) then
          return .intMul n (← moduleVar one)
  moduleVar e

/-- Simplify atoms and scalar coefficients, carrying their proofs through the additive tree. -/
private partial def visitModuleAtoms [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]
    (integers : Bool) (simpAtom : Expr → m Simp.Result) (e : Expr) : m Simp.Result := do
  let bin (scalar := false) : m Simp.Result := do
    match h : e with
    | .app fa@h':(.app f a) b =>
      let ra ← if scalar then simpAtom a else visitModuleAtoms integers simpAtom a
      let rb ← visitModuleAtoms integers simpAtom b
      let rf ← (Simp.mkCongrArg fa f a ra h' : SymM Simp.Result)
      (Simp.mkCongr e fa b rf rb (h' ▸ h) : SymM Simp.Result)
    | _ => unreachable!
  match_expr e with
  | HAdd.hAdd _ _ _ _ _ _ => bin
  | HSub.hSub _ _ _ _ _ _ => if integers then bin else simpAtom e
  | Neg.neg _ _ _ =>
    unless integers do return ← simpAtom e
    match h : e with
    | .app f a =>
      (Simp.mkCongrArg e f a (← visitModuleAtoms integers simpAtom a) h : SymM Simp.Result)
    | _ => unreachable!
  | HSMul.hSMul σ _ _ _ _ _ =>
    if σ.isConstOf ``Nat || (integers && σ.isConstOf ``Int) then bin true else simpAtom e
  | _ => simpAtom e

private def mkModuleContext (type inst : Expr) (u : Level) (integers : Bool) :
    ModuleContext := Id.run do
  let natInst := if integers then mkApp2 (mkConst ``Grind.IntModule.toNatModule [u]) type inst else inst
  let monoid := mkApp2 (mkConst ``Grind.NatModule.toAddCommMonoid [u]) type natInst
  let addInst := mkApp2 (mkConst ``Grind.AddCommMonoid.toAdd [u]) type monoid
  let zeroInst := mkApp2 (mkConst ``Grind.AddCommMonoid.toZero [u]) type monoid
  let smulInst := mkApp2 (mkConst ``Grind.NatModule.nsmul [u]) type natInst
  let ctx : ModuleContext := {
    addFn := mkApp4 (mkConst ``HAdd.hAdd [u, u, u]) type type type
      (mkApp2 (mkConst ``instHAdd [u]) type addInst)
    zero := mkApp3 (mkConst ``OfNat.ofNat [u]) type (mkRawNatLit 0)
      (mkApp2 (mkConst ``Zero.toOfNat0 [u]) type zeroInst)
    nsmulFn := mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) (mkConst ``Nat) type type
      (mkApp3 (mkConst ``instHSMul [0, u]) (mkConst ``Nat) type smulInst) }
  if !integers then return ctx
  let group := mkApp2 (mkConst ``Grind.IntModule.toAddCommGroup [u]) type inst
  return { ctx with
    subFn? := some (mkApp4 (mkConst ``HSub.hSub [u, u, u]) type type type
      (mkApp2 (mkConst ``instHSub [u]) type
        (mkApp2 (mkConst ``Grind.AddCommGroup.toSub [u]) type group)))
    negFn? := some (mkApp2 (mkConst ``Neg.neg [u]) type
      (mkApp2 (mkConst ``Grind.AddCommGroup.toNeg [u]) type group))
    zsmulFn? := some (mkApp4 (mkConst ``HSMul.hSMul [0, u, u]) (mkConst ``Int) type type
      (mkApp3 (mkConst ``instHSMul [0, u]) (mkConst ``Int) type
        (mkApp2 (mkConst ``Grind.IntModule.zsmul [u]) type inst))) }

private def ModuleContext.canon (ctx : ModuleContext) : SymM ModuleContext := do
  let canonFn (fn : Expr) : SymM Expr := do shareCommon (← Sym.canon fn)
  return { ctx with
    addFn := ← canonFn ctx.addFn
    zero := ← canonFn ctx.zero
    nsmulFn := ← canonFn ctx.nsmulFn
    subFn? := ← ctx.subFn?.mapM canonFn
    negFn? := ← ctx.negFn?.mapM canonFn
    zsmulFn? := ← ctx.zsmulFn?.mapM canonFn }

private def getModule? (type : Expr) : SymM (Option (ModuleContext × Expr × Level × Bool)) := do
  let some u ← getDecLevel? type | return none
  let intInst? ← Sym.synthInstance? (← shareCommon (mkApp (mkConst ``Grind.IntModule [u]) type))
  let integers := intInst?.isSome
  let inst? ← match intInst? with
    | some inst => pure (some inst)
    | none => Sym.synthInstance? (← shareCommon (mkApp (mkConst ``Grind.NatModule [u]) type))
  let some inst := inst? | return none
  let ctx := mkModuleContext type inst u integers
  return some (ctx, inst, u, integers)

private def moduleCertificate (type inst : Expr) (u : Level) (integers : Bool)
    (ctx : ModuleContext) (vars : Array Expr) (lhs rhs : Grind.Linarith.Expr) : MetaM Expr := do
  let vars ← if h : 0 < vars.size then
    RArray.toExpr type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr type id (RArray.leaf ctx.zero)
  let thm := if integers then ``Grind.Linarith.eq_of_norm_eq else ``Grind.Linarith.eq_normN
  return mkApp6 (mkConst thm [u]) type inst vars (toExpr lhs) (toExpr rhs) eagerReflBoolTrue

/-- Prove an equality by collecting additive terms over a `Grind.NatModule` or
`Grind.IntModule`. Recognizes zero, addition, and literal natural scalar multiplication;
integer modules also support subtraction, negation, and literal integer scalar multiplication.

Module operations are recognized up to definitional equality at `.default` transparency.
Before reification, `simpAtom` simplifies atoms and scalar coefficients, with its proofs
incorporated into the equality certificate. Other expressions are atoms, identified up to
definitional equality at `.instances` transparency.
Multiplication is not interpreted: a caller can first distribute products and use this procedure without
requiring associative or unital multiplication. Returns `none` when the type has neither module
structure, the proposition is not an equality, or the additive normal forms differ.
The returned proof is checked using the existing module normalization certificates. -/
def proveAddEq? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (e : Expr) (simpAtom : Expr → m Simp.Result := fun _ => pure .rfl) : m (Option Expr) :=
    withNewMCtxDepth do
  let e ← shareCommon e
  let_expr Eq type lhs rhs := e | return none
  let some (ctx, inst, u, integers) ← getModule? type | return none
  let rl ← visitModuleAtoms integers simpAtom lhs
  let rr ← visitModuleAtoms integers simpAtom rhs
  let lhs' ← shareCommon (rl.getResultExpr lhs)
  let rhs' ← shareCommon (rr.getResultExpr rhs)
  let ((lhsRe, rhsRe), s) ← (((do return (← reifyModule lhs', ← reifyModule rhs') :
    ModuleM _).run ctx).run {} : SymM _)
  let equal := if integers then lhsRe.norm == rhsRe.norm else lhsRe.toPolyN == rhsRe.toPolyN
  unless equal do return none
  let h ← moduleCertificate type inst u integers ctx s.vars lhsRe rhsRe
  let h ← match rl with
    | .rfl .. => pure h
    | .step _ hl .. => (Simp.mkEqTrans lhs lhs' hl rhs' h : SymM Expr)
  let h ← match rr with
    | .rfl .. => pure h
    | .step _ hr .. =>
      let hr := mkApp4 (mkConst ``Eq.symm [u.succ]) type rhs rhs' hr
      (Simp.mkEqTrans lhs rhs' h rhs hr : SymM Expr)
  return some (mkExpectedPropHint h e)

private def denoteModulePoly (ctx : ModuleContext) (vars : Array Expr)
    (p : Grind.Linarith.Poly) : Grind.Linarith.Expr × Expr :=
  match p with
  | .nil => (.zero, ctx.zero)
  | .add k x p =>
    let (term, expr) := if k == 1 then (.var x, vars[x]!) else
      match ctx.zsmulFn? with
      | some fn => (.intMul k (.var x), mkApp2 fn (toExpr k) vars[x]!)
      | none => (.natMul k.natAbs (.var x), mkApp2 ctx.nsmulFn (toExpr k.natAbs) vars[x]!)
    match p with
    | .nil => (term, expr)
    | _ =>
      let (tail, tailExpr) := denoteModulePoly ctx vars p
      (.add term tail, mkApp2 ctx.addFn expr tailExpr)

/-- Collect the additive terms of a `Grind.NatModule` or `Grind.IntModule` expression,
with a proof of equality. Supports the same operations as `proveAddEq?`; `simpAtom`
simplifies atoms and scalar coefficients before reification, with its proofs incorporated
into the result. Atoms are ordered by `Expr.lt`; coefficients are natural numbers for
natural modules and integers for integer modules. Multiplication need not be associative or unital.

Returns `.rfl` when the type has neither module structure or the expression is already in
normal form. Can be used as a `post` procedure in `Sym.Simp` to normalize additive expressions
inside arbitrary propositions, including goals that remain open after normalization. -/
def normalizeAdd? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (e : Expr) (simpAtom : Expr → m Simp.Result := fun _ => pure .rfl) : m Simp.Result :=
    withNewMCtxDepth do
  unless e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 ||
      e.isAppOfArity ``Neg.neg 3 || e.isAppOfArity ``HSMul.hSMul 6 do return .rfl
  let e ← shareCommon e
  let type ← Meta.inferType e
  let some (ctx, inst, u, integers) ← getModule? type | return .rfl
  let ctx ← ctx.canon
  let r ← visitModuleAtoms integers simpAtom e
  let e₁ ← shareCommon (r.getResultExpr e)
  let (re, s) ← (((reifyModule e₁).run ctx).run {} : SymM _)
  let perm := (Array.range s.vars.size).qsort fun i j => Expr.lt s.vars[i]! s.vars[j]!
  let vars := perm.map (s.vars[·]!)
  let re := re.renameVars (Grind.mkVarRename perm)
  let p := if integers then re.norm else re.toPolyN
  let (re', e') := denoteModulePoly ctx vars p
  let e' ← shareCommon e'
  if isSameExpr e₁ e' then return r.markAsDone
  let h ← moduleCertificate type inst u integers ctx vars re re'
  let h := mkExpectedPropHint h (mkApp3 (mkConst ``Eq [u.succ]) type e₁ e')
  match r with
  | .rfl _ cd => return .step e' h (done := true) (contextDependent := cd)
  | .step _ h₁ _ cd =>
    return .step e' (← (Simp.mkEqTrans e e₁ h₁ e' h : SymM Expr))
      (done := true) (contextDependent := cd)

end Lean.Meta.Sym.Arith
