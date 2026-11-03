/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Lean.Meta.Sym.Arith.Types
public import Lean.Meta.Sym.Simp.Result
public import Lean.Meta.Sym.Simp.App
import Lean.Meta.Sym.Arith.Functions
public import Lean.Meta.Sym.Arith.Norm
import Lean.Meta.Sym.Arith.ToExpr
public import Lean.Meta.Sym.Canon
import Lean.Meta.Sym.SynthInstance
public import Lean.Meta.Sym.LitValues
public import Lean.Meta.NatInstTesters
public import Lean.Meta.IntInstTesters
public import Lean.Meta.Tactic.Grind.Arith.Linear.VarRename
public import Lean.Meta.AppBuilder
import Lean.Data.RArray
public import Init.Grind.Module.NatModuleNorm
public section
namespace Lean.Meta.Sym.Arith
open Lean.Meta.Sym.Simp (Result mkEqTransResult)

/-!
# Additive normalization over modules

`normalizeAdd?` rewrites a term of a `Grind.NatModule` or `Grind.IntModule` into a sum of scalar
multiples of atoms, and `proveAddEq?` closes equalities between such terms. Zero, `+`, and `•`
by a `Nat` literal are interpreted; over an `IntModule` also `-`, negation, and `•` by an `Int`
literal. Everything else is an atom, including products, so the carrier need not have an
associative or unital multiplication.

The implementation follows the ring normalizer (`Norm.lean`). Each structure is classified once
per `SymM` run (`classifyModule?`), with canonical operators checked against the module's
instances. While reifying, an operator is interpreted when it is pointer-equal to the canonical
one after `Sym.canon`; one with another instance is an atom whose arguments are still normalized.
Atoms are identified by pointer. Each node is reified once, and its polynomial is computed from
its children's. A node whose polynomial exceeds `sym.arith.maxTerms` is an atom whose children
are normalized. The certificates number the atoms in `Expr.lt` order and are checked with the
kernel-optimized `Grind.Linarith.eq_of_norm_eq` and `Grind.Linarith.eq_normN_k`.

Over `Nat` and `Int`, numerals are multiples of the atom `1`, so `n + 1 = 2 + (n - 1)` holds
over `Int` independently of the atom order.
-/

private abbrev LinExpr := Grind.Linarith.Expr
private abbrev LinPoly := Grind.Linarith.Poly

private def canonFn (e : Expr) : SymM Expr := do
  shareCommon (← Sym.canon e)

private instance : MonadCanon SymM where
  canonExpr := canonFn
  synthInstance? e := Sym.synthInstance? e

private def tryModule? (type : Expr) : SymM (Option Nat) := do
  let some u ← getDecLevel? type | return none
  let intInst? ← Sym.synthInstance? (mkApp (mkConst ``Grind.IntModule [u]) type)
  let (inst, integers) ← match intInst? with
    | some inst => pure (inst, true)
    | none =>
      let some inst ← Sym.synthInstance? (mkApp (mkConst ``Grind.NatModule [u]) type) | return none
      pure (inst, false)
  let mod ← try mkModule type u inst integers catch ex =>
    reportIssue! "additive normalization does not apply to{indentExpr type}\n{ex.toMessageData}"
    return none
  let id := (← getArithState).modules.size
  modifyArithState fun s => { s with modules := s.modules.push { mod with id } }
  return some id

/--
Classifies `type` as a `Grind.IntModule`, or failing that a `Grind.NatModule`, returning its id in
`State.modules`. Results, including failures, are cached in `State.typeModuleClassify`.
-/
def classifyModule? (type : Expr) : SymM (Option Nat) := do
  if let some id? := (← getArithState).typeModuleClassify.find? { expr := type } then
    return id?
  let id? ← tryModule? type
  modifyArithState fun s => { s with typeModuleClassify := s.typeModuleClassify.insert { expr := type } id? }
  return id?

private def polyLength : LinPoly → Nat
  | .nil => 0
  | .add _ _ p => polyLength p + 1

private structure ModState where
  vars   : Array Expr := #[]
  varMap : PHashMap ExprPtr Nat := {}
  /-- The canonical `1` over `Nat` or `Int`, the atom numerals are multiples of. -/
  one?   : Option Expr := none
  /-- `sym.arith.maxTerms` -/
  maxTerms : Nat

private structure Node where
  /-- `e = e₁`, where `e₁` is `e` with its atoms simplified and its kept subterms normalized. -/
  r : Result
  re : LinExpr
  /--
  The polynomial of `re` over the same variables, as the certificate computes it: `Expr.norm`
  for integer modules and `Expr.toPolyN` for natural modules.
  -/
  p : LinPoly
  /-- `true` if `e₁` is an atom whose children are normalized (see `certify`). -/
  kept : Bool := false

private instance : Inhabited Node := ⟨{ r := .rfl, re := .zero, p := .nil }⟩

private abbrev VisitM (m : Type → Type) := ReaderT Module (StateT ModState m)

section Visit
variable [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]

private def chainResults (e e₁ : Expr) (r₁ r₂ : Result) : SymM Result := do
  match r₁ with
  | .rfl _ cd₁ =>
    match r₂ with
    | .rfl done cd₂ => return .rfl done (cd₁ || cd₂)
    | .step e' h done cd₂ => return .step e' h done (cd₁ || cd₂)
  | .step _ h₁ _ cd₁ => mkEqTransResult e e₁ h₁ r₂ cd₁

private def mkVar (e : Expr) : VisitM m Nat := do
  if let some x := (← get).varMap.find? { expr := e } then return x
  let x := (← get).vars.size
  modify fun s => { s with vars := s.vars.push e, varMap := s.varMap.insert { expr := e } x }
  return x

private def mkAtom (e₁ : Expr) (r : Result) (kept := false) : VisitM m Node := do
  let x ← mkVar e₁
  return { r, re := .var x, p := .add 1 x .nil, kept }

private def isInst (fn pre : Expr) : VisitM m Bool := do
  if isSameExpr fn pre then return true
  return isSameExpr fn (← canonFn pre)

/-- The canonical `1` of `Nat` or `Int`. -/
private def getOne (isNat : Bool) : VisitM m Expr := do
  if let some one := (← get).one? then return one
  let one ← canonFn (if isNat then mkNatLit 1 else toExpr (1 : Int))
  modify fun s => { s with one? := some one }
  return one

/--
`some k` if `e` is a numeral `k` of the carrier `Nat` or `Int` with its standard instance;
negative `Int` numerals are negations, interpreted separately.
-/
private def isCarrierNumeral? (e : Expr) : VisitM m (Option Nat) := do
  let_expr OfNat.ofNat α n inst := e | return none
  let .lit (.natVal k) := n | return none
  if α.isConstOf ``Nat then
    return if (← Structural.isInstOfNatNat inst) then some k else none
  if α.isConstOf ``Int then
    return if (← Structural.isInstOfNatInt inst) then some k else none
  return none

/-- `true` if `visit` interprets the head of `e`. -/
private def isInterpreted (e : Expr) : Bool :=
  e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``Neg.neg 3 ||
  e.isAppOfArity ``HSMul.hSMul 6 || e.isAppOfArity ``OfNat.ofNat 3 || e.isAppOfArity ``Zero.zero 2

private def congrBin (e fa f a b : Expr) (ra rb : Result) (h₁ : e = .app (.app f a) b)
    (h₂ : fa = .app f a) : SymM Result := do
  let r ← Simp.mkCongrArg fa f a ra h₂
  Simp.mkCongr e fa b r rb (h₂ ▸ h₁)

/-- The denotation of the polynomial `p` over `vars`, with its reification. -/
private def denoteLinPoly (mod : Module) (vars : Array Expr) (one? : Option Expr) (p : LinPoly) :
    LinExpr × Expr :=
  let term (k : Int) (x : Nat) : LinExpr × Expr :=
    let a := vars[x]!
    let re : LinExpr := if mod.integers then .intMul k (.var x) else .natMul k.natAbs (.var x)
    if one?.any (isSameExpr · a) then
      (re, if mod.type.isConstOf ``Nat then mkNatLit k.natAbs else toExpr k)
    else if k == 1 then
      (.var x, a)
    else match mod.intSMulFn? with
      | some fn => (re, mkApp2 fn (toExpr k) a)
      | none => (re, mkApp2 mod.natSMulFn (toExpr k.natAbs) a)
  let rec go : LinPoly → LinExpr × Expr
    | .nil => (.zero, mod.zeroNum)
    | .add k x .nil => term k x
    | .add k x p =>
      let (re₁, e₁) := term k x
      let (re₂, e₂) := go p
      (.add re₁ re₂, mkApp2 mod.addFn e₁ e₂)
  go p

private def ofLinExpr : LinExpr → Expr
  | .zero => mkConst ``Grind.Linarith.Expr.zero
  | .var x => mkApp (mkConst ``Grind.Linarith.Expr.var) (mkRawNatLit x)
  | .add a b => mkApp2 (mkConst ``Grind.Linarith.Expr.add) (ofLinExpr a) (ofLinExpr b)
  | .sub a b => mkApp2 (mkConst ``Grind.Linarith.Expr.sub) (ofLinExpr a) (ofLinExpr b)
  | .neg a => mkApp (mkConst ``Grind.Linarith.Expr.neg) (ofLinExpr a)
  | .natMul k a => mkApp2 (mkConst ``Grind.Linarith.Expr.natMul) (mkRawNatLit k) (ofLinExpr a)
  | .intMul k a => mkApp2 (mkConst ``Grind.Linarith.Expr.intMul) (mkIntLitK k) (ofLinExpr a)

/-- The proof of `lhs = rhs` for terms reified as `lhsRe` and `rhsRe` over `vars`. -/
private def mkCertificate (mod : Module) (vars : Array Expr) (lhs rhs : Expr) (lhsRe rhsRe : LinExpr) :
    MetaM Expr := do
  let ctx ← if h : 0 < vars.size then
    RArray.toExpr mod.type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr mod.type id (RArray.leaf mod.zeroNum)
  let thm := if mod.integers then ``Grind.Linarith.eq_of_norm_eq else ``Grind.Linarith.eq_normN_k
  let h := mkApp6 (mkConst thm [mod.u]) mod.type mod.inst ctx (ofLinExpr lhsRe) (ofLinExpr rhsRe)
    eagerReflBoolTrue
  return mkExpectedPropHint h (mkApp3 (mkConst ``Eq [mod.u.succ]) mod.type lhs rhs)

/--
Renumbers the variables of `re` in decreasing `Expr.lt` order of their atoms: the polynomial
lists larger variables first, so its denotation lists the atoms in `Expr.lt` order.
-/
private def compactVars (re : LinExpr) : VisitM m (Grind.VarRename × Array Expr) := do
  let vars := (← get).vars
  let used := Std.HashSet.toArray (re.collectVars {}) |>.qsort fun i j => Expr.lt vars[j]! vars[i]!
  return (Grind.mkVarRename used, used.map (vars[·]!))

/-- `p` with its variables renamed by `f`, sorted again with larger variables first. -/
private def renamePoly (p : LinPoly) (f : Grind.VarRename) : LinPoly :=
  let rec terms : LinPoly → Array (Int × Nat) → Array (Int × Nat)
    | .nil, acc => acc
    | .add k x p, acc => terms p (acc.push (k, f x))
  (terms p #[]).qsort (fun a b => a.2 < b.2) |>.foldl (init := .nil) fun p (k, x) => .add k x p

/--
The proof `e₁ = e'` that the visited node `n` of `e₁` equals its normal form `e'`, `done`. For a
plain atom the result is `.rfl` without `done`, so that a simplifier still visits its subterms.
-/
private def certify (e₁ : Expr) (n : Node) : VisitM m Result := do
  if n.re matches .var _ then return .rfl (done := n.kept)
  let mod ← read
  let (f, vars) ← compactVars n.re
  let (re', e') := denoteLinPoly mod vars (← get).one? (renamePoly n.p f)
  let e' ← shareCommon e'
  if isSameExpr e₁ e' then return .rfl (done := true)
  return .step e' (← mkCertificate mod vars e₁ e' (n.re.renameVars f) re') (done := true)

private def normalizeNode (e : Expr) (n : Node) : VisitM m Result := do
  let e₁ := n.r.getResultExpr e
  chainResults e e₁ n.r (← certify e₁ n)

private def chainNode (e e₂ : Expr) (r₁ : Result) (n : Node) : VisitM m Node := do
  return { n with r := (← chainResults e e₂ r₁ n.r) }

/-- `k • 1` for a numeral `k` of the carrier `Nat` or `Int`. -/
private def numeralNode (k : Nat) : VisitM m Node := do
  let mod ← read
  let x ← mkVar (← getOne (mod.type.isConstOf ``Nat))
  let re : LinExpr := if mod.integers then .intMul k (.var x) else .natMul k (.var x)
  return { r := .rfl, re, p := .add k x .nil }

mutual
private partial def visit (simpAtom : Expr → m Result) (e : Expr) : VisitM m Node := do
  let mod ← read
  let atom : VisitM m Node := do
    let r ← simpAtom e
    let e₁ := r.getResultExpr e
    if !isSameExpr e₁ e && isInterpreted e₁ then
      chainNode e e₁ r (← visit simpAtom e₁)
    else
      mkAtom e₁ r
  -- The node of `e := f a b`, kept as an atom with its children normalized.
  let keep (fa f a b : Expr) (ra rb : Result) (h₁ : e = .app (.app f a) b) (h₂ : fa = .app f a) :
      VisitM m Node := do
    let r ← congrBin e fa f a b ra rb h₁ h₂
    mkAtom (r.getResultExpr e) r (kept := true)
  let unexpected : VisitM m Unit := do
    reportIssue! "additive term with unexpected instance{indentExpr e}"
  -- A binary node with the visited children `na` and `nb`; over the budget, it is kept.
  let binNode (fa f a b : Expr) (na nb : Node) (re : LinExpr) (p : LinPoly)
      (h₁ : e = .app (.app f a) b) (h₂ : fa = .app f a) : VisitM m Node := do
    if polyLength p ≤ (← get).maxTerms then
      return { r := (← congrBin e fa f a b na.r nb.r h₁ h₂), re, p }
    keep fa f a b (← normalizeNode a na) (← normalizeNode b nb) h₁ h₂
  -- A binary operator; `mk` and `op` build the reification and the polynomial from the children's.
  let bin (fn : Expr) (mk : LinExpr → LinExpr → LinExpr) (op : LinPoly → LinPoly → LinPoly) :
      VisitM m Node := do
    match h : e with
    | .app fa@h':(.app f a) b =>
      let na ← visit simpAtom a
      let nb ← visit simpAtom b
      unless (← isInst fn f) do
        unexpected
        return (← keep fa f a b (← normalizeNode a na) (← normalizeNode b nb) h h')
      binNode fa f a b na nb (mk na.re nb.re) (op na.p nb.p) h h'
    | _ => unreachable!
  -- Scalar multiplication by a literal: `mk` builds the reification from the scalar and the child's.
  let smul (fn : Expr) (lit? : Expr → Option Int) (mk : Int → LinExpr → LinExpr) : VisitM m Node := do
    match h : e with
    | .app fa@h':(.app f k) a =>
      unless (← isInst fn f) do return (← atom)
      let rk ← simpAtom k
      let na ← visit simpAtom a
      let some kv := lit? (rk.getResultExpr k)
        | keep fa f k a rk (← normalizeNode a na) h h'
      return { r := (← congrBin e fa f k a rk na.r h h'), re := mk kv na.re, p := na.p.mul kv }
    | _ => unreachable!
  if let .mdata _ b := e then
    let n ← visit simpAtom b
    return (← chainNode e b (.step b (← Sym.mkEqRefl b)) n)
  match_expr e with
  | HAdd.hAdd α β γ _ _ _ =>
    unless (homoType? α β γ).isSome do return (← atom)
    bin mod.addFn .add (·.combine ·)
  | HSub.hSub α β γ _ _ _ =>
    let some fn := mod.subFn? | atom
    unless (homoType? α β γ).isSome do return (← atom)
    bin fn .sub fun pa pb => pa.combine (pb.mul (-1))
  | Neg.neg _ _ _ =>
    let some fn := mod.negFn? | atom
    match h : e with
    | .app f a =>
      let na ← visit simpAtom a
      unless (← isInst fn f) do
        unexpected
        return (← mkAtom e (← Simp.mkCongrArg e f a (← normalizeNode a na) h) (kept := true))
      return { r := (← Simp.mkCongrArg e f a na.r h), re := .neg na.re, p := na.p.mul (-1) }
    | _ => unreachable!
  | HSMul.hSMul σ _ _ _ _ _ =>
    if σ.isConstOf ``Nat then
      smul mod.natSMulFn (fun k => (Sym.getNatValue? k).run.map Int.ofNat) fun k re => .natMul k.toNat re
    else if σ.isConstOf ``Int then
      let some fn := mod.intSMulFn? | atom
      smul fn (fun k => (Sym.getIntValue? k).run) .intMul
    else atom
  | OfNat.ofNat _ n _ =>
    if let some k ← isCarrierNumeral? e then
      if k == 0 then return { r := .rfl, re := .zero, p := .nil }
      return (← numeralNode k)
    if n.rawNatLit? == some 0 && isSameExpr mod.zeroNum (← canonFn e) then
      return { r := .rfl, re := .zero, p := .nil }
    atom
  | Zero.zero _ _ =>
    if isSameExpr mod.zeroFn (← canonFn e) then return { r := .rfl, re := .zero, p := .nil }
    atom
  | _ => atom
end

end Visit

private def runVisit [Monad m] [MonadLiftT MetaM m] (mod : Module) (x : VisitM m α) : m α := do
  let maxTerms := sym.arith.maxTerms.get (← (getOptions : MetaM Options))
  return (← (x.run mod).run { maxTerms }).1

/-- The module of the additive term `e`: an application of `+`, `-`, negation, or `•`. -/
private def getModuleOf? (e : Expr) : SymM (Option Module) := do
  let type ← match_expr e with
    | HAdd.hAdd α β γ _ _ _ => pure (homoType? α β γ)
    | HSub.hSub α β γ _ _ _ => pure (homoType? α β γ)
    | Neg.neg α _ _ => pure (some α)
    | HSMul.hSMul σ β γ _ _ _ =>
      pure <| if (σ.isConstOf ``Nat || σ.isConstOf ``Int) && isSameExpr β γ then some β else none
    | _ => pure none
  let some type := type | return none
  let some id ← classifyModule? type | return none
  return (← getArithState).modules[id]!

/--
Normalizes the additive term `e` of a `Grind.NatModule` or `Grind.IntModule` (an application of
`+`, `-`, negation, or `•`) into a sum of scalar multiples of atoms, after simplifying the atoms
and the scalars of `•` with `simpAtom`. `e` must be maximally shared. Atoms are listed in
`Expr.lt` order; coefficients are natural numbers for natural modules and integers for integer
modules. Multiplication is not interpreted, so it need not be associative or unital.

Intended as a `pre` simproc with `simpAtom := Simp.simp`: it sees the maximal additive subtree
first and reifies it once. The result is `.rfl` when the normalizer does not apply (`e` is not
such a term, or it is an atom of its structure), and otherwise marked `done`, so that a
simplifier does not re-enter the normal form.
-/
def normalizeAdd? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]
    (e : Expr) (simpAtom : Expr → m Result := fun _ => pure .rfl) : m Result := do
  let some mod ← getModuleOf? e | return .rfl
  runVisit mod do
    let n ← visit simpAtom e
    normalizeNode e n

/--
Proves the equality `e` between terms of a `Grind.NatModule` or `Grind.IntModule` by
normalizing both sides as `normalizeAdd?` does. Returns `none` when the type has neither
module structure, `e` is not an equality, or the normal forms differ. `e` must be maximally
shared.
-/
def proveAddEq? [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]
    (e : Expr) (simpAtom : Expr → m Result := fun _ => pure .rfl) : m (Option Expr) := do
  let_expr Eq type lhs rhs := e | return none
  let some id ← classifyModule? type | return none
  let mod := (← getArithState).modules[id]!
  runVisit mod do
    let nl ← visit simpAtom lhs
    let nr ← visit simpAtom rhs
    let (f, vars) ← compactVars (.add nl.re nr.re)
    unless renamePoly nl.p f == renamePoly nr.p f do return none
    let lhsRe := nl.re.renameVars f
    let rhsRe := nr.re.renameVars f
    let lhs₁ := nl.r.getResultExpr lhs
    let rhs₁ := nr.r.getResultExpr rhs
    let h ← mkCertificate mod vars lhs₁ rhs₁ lhsRe rhsRe
    let h ← match nl.r with
      | .rfl .. => pure h
      | .step _ hl .. => Simp.mkEqTrans lhs lhs₁ hl rhs₁ h
    let h ← match nr.r with
      | .rfl .. => pure h
      | .step _ hr .. =>
        Simp.mkEqTrans lhs rhs₁ h rhs (mkApp4 (mkConst ``Eq.symm [mod.u.succ]) type rhs rhs₁ hr)
    return some (mkExpectedPropHint h e)

end Lean.Meta.Sym.Arith
