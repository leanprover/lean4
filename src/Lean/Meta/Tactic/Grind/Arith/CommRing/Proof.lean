/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
public import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
public import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM
import Lean.Data.RArray
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.ProofUtil
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Sym.Arith.ToExpr
import Lean.Meta.Sym.Arith.Kronecker
import Lean.Meta.Sym.Arith.VarRename
import Init.Data.Nat.Order
import Init.Data.Order.Lemmas
import Init.Grind.Ring.Packed
import Init.Grind.Ring.Kronecker
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith

/--
Returns a context of type `RArray α` containing the variables `vars` where
`α` is the type of the ring.
-/
private def toContextExpr [Monad m] [MonadLiftT MetaM m] [MonadCanon m] [MonadRing m] (vars : Array Expr) : m Expr := do
  let ring ← getRing
  if h : 0 < vars.size then
    RArray.toExpr ring.type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr ring.type id (RArray.leaf (mkApp (← getNatCastFn) (toExpr 0)))

private def toSContextExpr' [Monad m] [MonadLiftT MetaM m] [MonadCanon m] [MonadSemiring m] (vars : Array Expr) : m Expr := do
  let semiring ← getSemiring
  if h : 0 < vars.size then
    RArray.toExpr semiring.type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr semiring.type id (RArray.leaf (mkApp (← getNatCastFn') (toExpr 0)))

/-- Similar to `toContextExpr`, but for semirings. -/
private def toSContextExpr (semiringId : Nat) (vars : Array Expr) : RingM Expr := do
  SemiringM.run semiringId do toSContextExpr' vars

/-- Returns the multiplier `k` for the input polynomial. See comment at `PolyDerivation.step`. -/
def PolyDerivation.getMultiplier (d : PolyDerivation) : Int :=
  go d 1
where
  go (d : PolyDerivation) (acc : Int) : Int :=
    match d with
    | .input _ => acc
    | .step _ k₁ d .. => go d (k₁ * acc)
    | .normEq0 _ d .. => go d acc

private def throwNoNatZeroDivisors : RingM α := do
  throwError "`grind` internal error, `NoNatZeroDivisors` instance is needed, but it is not available for{indentExpr (← getRing).type}"

private def getPolyConst (p : Poly) : RingM Int := do
  let .num k := p
    | throwError "`grind` internal error, constant polynomial expected {indentExpr (← p.denoteExpr)}"
  return k

structure ProofM.State where
  cache       : Std.HashMap UInt64 Expr := {}
  polyDecls   : Std.HashMap Poly Expr := {}
  monDecls    : Std.HashMap Mon Expr := {}
  exprDecls   : Std.HashMap RingExpr Expr := {}
  sexprDecls  : Std.HashMap SemiringExpr Expr := {}
  /-- Packed polynomials `Grind.CommRing.PPoly` in a base, built after the variables are renamed. -/
  ppolyDecls  : Std.HashMap (Poly × Nat) Expr := {}

structure ProofM.Context where
  ctx   : Expr
  /-- Context for semiring variables if available -/
  sctx? : Option Expr

abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State RingM)

/-- Returns a Lean expression representing the variable context used to construct `CommRing` proof steps. -/
private abbrev getContext : ProofM Expr := do
  return (← read).ctx

/--
Returns a Lean expression representing the semiring variable context
used to construct `CommRing` proof steps.
-/
private abbrev getSContext : ProofM Expr := do
  let some sctx := (← read).sctx?
    | throwError "`grind` internal error, semiring context is not available"
  return sctx

private abbrev caching (c : α) (k : ProofM Expr) : ProofM Expr := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if let some h := (← get).cache[addr]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert addr h }
    return h

local macro "declare! " decls:ident a:ident : term =>
  `(do if let some x := (← get).$decls[$a]? then
         return x
       let x := mkFVar (← mkFreshFVarId);
       modify fun s => { s with $decls:ident := (s.$decls).insert $a x };
       return x)

private def mkPolyDecl (p : Poly) : ProofM Expr := do
  declare! polyDecls p

/-- The packed polynomial `p` in base `B`. -/
private def mkPPolyDecl (p : Poly) (B : Nat) : ProofM Expr := do
  let key := (p, B)
  declare! ppolyDecls key

private def mkExprDecl (e : RingExpr) : ProofM Expr := do
  declare! exprDecls e

private def mkSExprDecl (e : SemiringExpr) : ProofM Expr := do
  declare! sexprDecls e

private def mkMonDecl (m : Mon) : ProofM Expr := do
  declare! monDecls m

private def mkStepBasicPrefix (declName : Name) : ProofM Expr := do
  let ctx ← getContext
  let ring ← getCommRing
  return mkApp3 (mkConst declName [ring.u]) ring.type ring.commRingInst ctx

private def mkStepPrefix (declName declNameC : Name) : ProofM Expr := do
  if let some (charInst, char) ← nonzeroCharInst? then
    let ctx ← getContext
    let ring ← getCommRing
    return mkApp5 (mkConst declNameC [ring.u]) ring.type (toExpr char) ring.commRingInst charInst ctx
  else
    mkStepBasicPrefix declName

private def getSemiringIdOf : RingM Nat := do
  let some semiringId := (← getCommRing).semiringId? | throwError "`grind` internal error, semiring is not available"
  return semiringId

private def getSemiringOf : RingM Sym.Arith.CommSemiring := do
  SemiringM.run (← getSemiringIdOf) do getCommSemiring

private def mkSemiringPrefix (declName : Name) : ProofM Expr := do
  let sctx ← getSContext
  let semiring ← getSemiringOf
  return mkApp3 (mkConst declName [semiring.u]) semiring.type semiring.semiringInst sctx

private def mkSemiringAddRightCancelPrefix (declName : Name) : ProofM Expr := do
  let sctx ← getSContext
  let semiring ← getSemiringOf
  let some addRightCancelInst ← SemiringM.run (← getSemiringIdOf) do getAddRightCancelInst?
    | throwError "`grind` internal error, `AddRightCancel` instance is not available"
  return mkApp4 (mkConst declName [semiring.u]) semiring.type semiring.semiringInst addRightCancelInst sctx

/-- Proof of `p = p` for the certificate argument `p = …` of a step checked by definitional equality. -/
private def mkPolyRefl (p : Poly) : ProofM Expr := do
  return mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Poly) (← mkPolyDecl p)

private def mulConstR (k : Int) (p : Poly) : ProofM Poly := do
  if let some c ← nonzeroChar? then return p.mulConstC k c else return p.mulConst k

private def mulMonR (k : Int) (m : Mon) (p : Poly) : ProofM Poly := do
  if let some c ← nonzeroChar? then return p.mulMonC k m c else return p.mulMon k m

/-- Hints for `Grind.CommRing.Poly.mergeHint`: one per monomial of `b`, see `Grind.CommRing.Poly.mergeHintG`. -/
private partial def mergeHints (a b : Poly) (acc : Array Nat) : Array Nat :=
  go a b 0 acc
where
  go (a b : Poly) (n : Nat) (acc : Array Nat) : Array Nat :=
    match b with
    | .num _ => acc
    | .add _ m b' =>
      match a with
      | .add _ m' a' =>
        match m'.grevlex m with
        | .gt => go a' b (n + 1) acc
        | .eq => go a' b' 0 (acc.push (2*n + 1))
        | .lt => go a b' 0 (acc.push (2*n))
      | .num _ => go a b' 0 (acc.push (2*n))

/--
The sum of `a` and `b` (`Poly.combineC` in characteristic `c`, `Poly.combine` otherwise) together
with `mergeHints a b #[]`, in one walk.
-/
private partial def combineHints (a b : Poly) (char? : Option Nat) : Poly × Array Nat :=
  go a b 0 #[] #[]
where
  go (a b : Poly) (n : Nat) (hs : Array Nat) (ms : Array (Int × Mon)) : Poly × Array Nat :=
    match b with
    | .num k₂ =>
      let rec rest (a : Poly) (ms : Array (Int × Mon)) : Poly :=
        match a with
        | .add k m a => rest a (ms.push (k, m))
        | .num k₁ =>
          let k := k₁ + k₂
          let k := if let some c := char? then k % c else k
          ms.foldr (init := .num k) fun (k, m) p => .add k m p
      (rest a ms, hs)
    | .add k₂ m₂ b' =>
      match a with
      | .add k₁ m₁ a' =>
        match m₁.grevlex m₂ with
        | .gt => go a' b (n + 1) hs (ms.push (k₁, m₁))
        | .eq =>
          let k := k₁ + k₂
          let k := if let some c := char? then k % c else k
          go a' b' 0 (hs.push (2*n + 1)) (if k == 0 then ms else ms.push (k, m₁))
        | .lt => go a b' 0 (hs.push (2*n)) (ms.push (k₂, m₂))
      | .num _ => go a b' 0 (hs.push (2*n)) (ms.push (k₂, m₂))

/-- The number of monomials that the kernel walks to check `a.mergeHint hs b`. -/
private def hintsWalk (hs : Array Nat) : Nat :=
  hs.foldl (fun n h => n + h / 2 + 1) 0

private def hintsToExpr (hs : Array Nat) : Expr :=
  let nat := mkConst ``Nat
  hs.foldr (init := mkApp (mkConst ``List.nil [0]) nat) fun h e =>
    mkApp3 (mkConst ``List.cons [0]) nat (mkRawNatLit h) e

private def combineR (a b : Poly) : ProofM Poly := do
  if let some c ← nonzeroChar? then return a.combineC b c else return a.combine b

/--
The expression of the hints `hs` for checking `p = a.mergeHint hs b`, where `p` must be the sum of
`a` and `b`, and `hs` the hints of `a` and `b` (`mergeHints`).
-/
private def mkMergeHintsOf (a b p : Poly) (hs : Array Nat) : ProofM Expr := do
  if grind.debug.get (← getOptions) then
    unless (← combineR a b) == p do
      throwError "`grind` internal error, unexpected polynomial in ring proof step"
  return hintsToExpr hs

/-- Returns the hints for checking `p = a.mergeHint hs b`, where `p` must be the sum of `a` and `b`. -/
private def mkMergeHints (a b p : Poly) : ProofM Expr :=
  mkMergeHintsOf a b p (mergeHints a b #[])

/--
The sum of the multiples `leaves[lo:hi]` in a balanced `Grind.CommRing.SumTree`: its polynomial,
the tree, and the proof of `SumTree.AllZero` from the proofs of the leaves.
-/
private partial def mkSumTree (leaves : Array (Poly × Expr × Expr)) (lo hi : Nat) : ProofM (Poly × Expr × Expr × Nat) := do
  if hi - lo == 1 then
    let (q, t, h) := leaves[lo]!
    return (q, t, h, 0)
  let mid := (lo + hi) / 2
  let (a, ta, ha, ca) ← mkSumTree leaves lo mid
  let (b, tb, hb, cb) ← mkSumTree leaves mid hi
  let (p, hs) := combineHints a b (← nonzeroChar?)
  let t := mkApp3 (mkConst ``Grind.CommRing.SumTree.node) (hintsToExpr hs) ta tb
  let ring ← getCommRing
  let ctx ← getContext
  let allZero (t : Expr) := mkApp4 (mkConst ``Grind.CommRing.SumTree.AllZero [ring.u]) ring.type ring.ringInst ctx t
  return (p, t, mkApp4 (mkConst ``And.intro) (allZero ta) (allZero tb) ha hb, ca + cb + hintsWalk hs)

/-- `p` as a `Grind.CommRing.PPoly` in base `B`, with the same order of terms. -/
private def packedPolyExpr (B : Nat) : Poly → Expr
  | .num k => mkApp (mkConst ``Grind.CommRing.PPoly.num) (mkIntLitK k)
  | .add k m p => mkApp4 (mkConst ``Grind.CommRing.PPoly.add) (mkIntLitK k) (mkRawNatLit m.degree) (mkRawNatLit (code m)) (packedPolyExpr B p)
where
  code : Mon → Nat
    | .unit => 0
    | .mult pw m => pw.k * B ^ pw.x + code m

/-- A balanced `Grind.CommRing.PSumTree` of `leaves[lo:hi]`, and the proof of its `PSumTree.AllZero`. -/
private partial def mkPSumTree (B : Expr) (leaves : Array (Expr × Expr)) (lo hi : Nat) : ProofM (Expr × Expr) := do
  if hi - lo == 1 then return leaves[lo]!
  let mid := (lo + hi) / 2
  let (ta, ha) ← mkPSumTree B leaves lo mid
  let (tb, hb) ← mkPSumTree B leaves mid hi
  let ring ← getCommRing
  let ctx ← getContext
  let allZero (t : Expr) := mkApp5 (mkConst ``Grind.CommRing.PSumTree.AllZero [ring.u]) ring.type ring.ringInst ctx B t
  return (mkApp2 (mkConst ``Grind.CommRing.PSumTree.node) ta tb, mkApp4 (mkConst ``And.intro) (allZero ta) (allZero tb) ha hb)

/--
The proof that `p` is `base` plus the multiples `kᵢ * mᵢ * qᵢ` of `leaves`, with the step theorem
`declName` (`Stepwise.simpsP`, `Stepwise.d_stepsP`) applied to `pre`, checked with packed monomials
in a base larger than every degree of the step. Each polynomial `qᵢ` is packed once.
-/
private def mkPackedSum (declName declNameC : Name) (pre : Array Expr) (base p : Poly)
    (leaves : Array (Int × Mon × Poly × Expr)) : ProofM Expr := do
  let deg := leaves.foldl (fun d (_, m, q, _) => max d (m.degree + polyMaxDeg q)) (max (polyMaxDeg base) (polyMaxDeg p))
  let B := max 2 (deg + 1)
  let BE := mkRawNatLit B
  let ring ← getCommRing
  let ctx ← getContext
  let ppT := mkConst ``Grind.CommRing.PPoly
  let mut packed : Std.HashMap Poly (Expr × Expr) := {}
  let mut ls := #[]
  for (k, m, q, h) in leaves do
    let (Q, hQ) ← match packed[q]? with
      | some r => pure r
      | none =>
        let Q ← mkPPolyDecl q B
        let hQ := mkAppN (mkConst ``Grind.CommRing.PSumTree.leaf_zero [ring.u])
          #[ring.type, ring.commRingInst, ctx, BE, ← mkPolyDecl q, Q, eagerReflBoolTrue, mkApp2 (mkConst ``Eq.refl [1]) ppT Q, h]
        packed := packed.insert q (Q, hQ)
        pure (Q, hQ)
    ls := ls.push (mkApp4 (mkConst ``Grind.CommRing.PSumTree.leaf) (toExpr k) (← mkMonDecl m) (mkRawNatLit (polyMaxDeg q)) Q, hQ)
  let (t, hAll) ← mkPSumTree BE ls 0 ls.size
  let P ← mkPPolyDecl p B
  let refl := mkApp2 (mkConst ``Eq.refl [1]) ppT P
  let h ← mkStepPrefix declName declNameC
  return mkAppN h (pre ++ #[BE, ← mkPolyDecl base, ← mkPolyDecl p, P, t, eagerReflBoolTrue, refl, refl, hAll])

/--
The proof that `p` is `base` plus the multiples `kᵢ * mᵢ * qᵢ` of `leaves` by Kronecker
substitution (`Stepwise.simpsK`, `Stepwise.d_stepsK`, or `Stepwise.simpsM`, `Stepwise.d_stepsM`
with the multiples grouped by polynomial), applied to `pre`, if the values at the
point stay below a few million bits. In characteristic `c`, the difference over `Int` is
`c * E` for a stated polynomial `E`.
-/
private def mkKronSum? (declName declNameC declNameM declNameMC : Name) (pre : Array Expr) (base p : Poly)
    (leaves : Array (Int × Mon × Poly × Expr)) : ProofM (Option Expr) := do
  let deg := leaves.foldl (fun d (_, m, q, _) => max d (m.degree + polyMaxDeg q)) (max (polyMaxDeg base) (polyMaxDeg p))
  let B := max 2 (deg + 1)
  let c? ← nonzeroChar?
  let E : Poly ← match c? with
    | none => pure (.num 0)
    | some c =>
      let d := leaves.foldl (init := p.combine (base.mulConst (-1))) fun acc (k, m, q, _) => acc.combine (q.mulMon (-k) m)
      let E := d.divConst c
      unless E.mulConst c == d do return none
      pure E
  let c := c?.getD 0
  let norm := leaves.foldl (fun n (k, _, q, _) => n + k.natAbs * polyNorm1 q) (polyNorm1 p + polyNorm1 base + c * polyNorm1 E)
  let maxCode := leaves.foldl (fun c (_, m, q, _) => max c (monCode B m + polyMaxCode B q)) (max (polyMaxCode B base) (polyMaxCode B p))
  let some K := kronExponent? norm maxCode 4000000 | return none
  let ring ← getCommRing
  let ctx ← getContext
  -- The multiples `kᵢ * mᵢ * q` of the same `q` are one multiple `(Σ kᵢ * mᵢ) * q` (`MList`).
  let mut idx : Std.HashMap Poly Nat := {}
  let mut groups : Array (Poly × Poly × Expr) := #[]
  for (k, m, q, h) in leaves do
    if let some i := idx[q]? then
      groups := groups.modify i fun (M, q, h) => (.add k m M, q, h)
    else
      idx := idx.insert q groups.size
      groups := groups.push (.add k m (.num 0), q, h)
  -- Grouping pays off when the polynomials repeat: a group costs a product of two values, a
  -- multiple a shift.
  let grouped := 4 * groups.size < leaves.size
  let (declName, declNameC) := if grouped then (declNameM, declNameMC) else (declName, declNameC)
  let mut ls := mkConst ``Grind.CommRing.MList.nil
  let mut hAll := mkApp3 (mkConst ``Grind.CommRing.MList.allZero_nil [ring.u]) ring.type ring.ringInst ctx
  if grouped then
    for (M, q, h) in groups.reverse do
      let ME ← mkPolyDecl M
      let qE ← mkPolyDecl q
      hAll := mkAppN (mkConst ``Grind.CommRing.MList.allZero_cons [ring.u]) #[ring.type, ring.ringInst, ctx, ME, qE, ls, h, hAll]
      ls := mkApp3 (mkConst ``Grind.CommRing.MList.cons) ME qE ls
  else
    ls := mkConst ``Grind.CommRing.KList.nil
    hAll := mkApp3 (mkConst ``Grind.CommRing.KList.allZero_nil [ring.u]) ring.type ring.ringInst ctx
    for (k, m, q, h) in leaves.reverse do
      let kE := toExpr k
      let mE ← mkMonDecl m
      let qE ← mkPolyDecl q
      hAll := mkAppN (mkConst ``Grind.CommRing.KList.allZero_cons [ring.u]) #[ring.type, ring.ringInst, ctx, kE, mE, qE, ls, h, hAll]
      ls := mkApp4 (mkConst ``Grind.CommRing.KList.cons) kE mE qE ls
  let pE ← mkPolyDecl p
  let h ← mkStepPrefix declName declNameC
  let eArgs ← if c?.isSome then pure #[← mkPPolyDecl E B] else pure #[]
  let args := #[mkRawNatLit K, mkRawNatLit B, ← mkPolyDecl base, pE] ++ eArgs ++
    #[ls, eagerReflBoolTrue, eagerReflBoolTrue, hAll]
  return some (mkAppN h (pre ++ args))

/--
An estimate of the kernel cost of checking a chain `p₀, …, pₙ` with `pᵢ = pᵢ₋₁ + qᵢ` one step at a
time, in monomials: each step walks `pᵢ₋₁` and `qᵢ`, and each intermediate `pᵢ` is data of the proof.
-/
private def stepwiseCost (p₀ : Poly) (steps : Array (Poly × Poly)) : Nat := Id.run do
  let mut cost := 0
  let mut prev := p₀.length
  for h : i in [0:steps.size] do
    let (q, p) := steps[i]
    let n := p.length
    cost := cost + prev + q.length
    if i + 1 < steps.size then cost := cost + n / 2
    prev := n
  return cost

/--
`true` if a chain is checked with a sum tree of cost `treeCost` (see `mkSumTree`) rather than one
step at a time. The tree has a fixed cost per node, and it only pays off when the multiples are
small compared to the polynomials of the chain, as in long reductions of a large polynomial.
-/
private def useSumTree (treeCost seqCost : Nat) : Bool :=
  3 * treeCost < seqCost

/-- `true` if the proof of `c` was already built. -/
private def isProofCached (c : EqCnstr) : ProofM Bool := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  return (← get).cache.contains addr

/--
The simplification steps with multiplier `1` leading to `c`, from the last one down, and the
constraint below them. It stops at a constraint whose proof was already built.
-/
private partial def collectSimps1 (c : EqCnstr) (acc : Array (Int × Mon × EqCnstr × EqCnstr)) : ProofM (EqCnstr × Array (Int × Mon × EqCnstr × EqCnstr)) := do
  if (← isProofCached c) then return (c, acc)
  match c.h with
  | .simp 1 c₁ k₂ m₂ c₂ => collectSimps1 c₁ (acc.push (k₂, m₂, c₂, c))
  | _ => return (c, acc)

/-- `true` if normalizing `e` multiplies out a sum: a product or power with a sum of nonconstant terms. -/
private def expandsSum : RingExpr → Bool
  | .mul a b => (isSum a && exprDegB b ≥ 1) || (isSum b && exprDegB a ≥ 1) || expandsSum a || expandsSum b
  | .pow a k => (k ≥ 2 && isSum a) || expandsSum a
  | .add a b | .sub a b => expandsSum a || expandsSum b
  | .neg a => expandsSum a
  | _ => false
where
  isSum (e : RingExpr) : Bool := (e matches .add .. || e matches .sub ..) && exprDegB e ≥ 1

open Lean.Grind.CommRing in
/--
The proof of `p.denote ctx = 0` from `h : lhs = rhs`, where `p` is the polynomial of `lhs - rhs`,
by Kronecker substitution (`Stepwise.coreK`), if the values stay below a few million bits. In
characteristic `c`, the difference over `Int` is `c * E` for a stated polynomial `E`.
-/
private def mkKronCore? (lhs rhs : RingExpr) (p : Poly) (h : Expr) : ProofM (Option Expr) := do
  let e : RingExpr := .sub lhs rhs
  -- The evaluation pays off when the normalization of `lhs - rhs` multiplies out sums of degree 3 or more.
  if !expandsSum e || exprDegB e < 3 then return none
  let B := max 2 (max (exprDegB e) (polyMaxDeg p) + 1)
  let c? ← nonzeroChar?
  let E : Poly ← match c? with
    | none => pure (.num 0)
    | some c =>
      let diff := e.toPoly.combine (p.mulConst (-1))
      let E := diff.divConst c
      unless E.mulConst c == diff do return none
      pure E
  let c := c?.getD 0
  let maxCode := max (exprMaxCode B e) (polyMaxCode B p)
  let some K := kronExponent? (exprMajorant e + polyNorm1 p + c * polyNorm1 E) maxCode 4000000 | return none
  let pre ← mkStepPrefix ``Stepwise.coreK ``Stepwise.coreKC
  let eArgs ← if c?.isSome then pure #[← mkPPolyDecl E B] else pure #[]
  return some (mkAppN pre (#[mkRawNatLit K, mkRawNatLit B, ← mkExprDecl lhs, ← mkExprDecl rhs, ← mkPolyDecl p] ++ eArgs ++
    #[eagerReflBoolTrue, eagerReflBoolTrue, h]))

open Lean.Grind.CommRing in
partial def _root_.Lean.Meta.Grind.Arith.CommRing.EqCnstr.toExprProof (c : EqCnstr) : ProofM Expr := caching c do
  match c.h with
  | .core a b lhs rhs =>
    if let some h ← mkKronCore? lhs rhs c.p (← mkEqProof a b) then return h
    let h ← mkStepPrefix ``Stepwise.core ``Stepwise.coreC
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c.p) (← mkPolyRefl c.p) (← mkEqProof a b)
  | .coreS a b sa sb ra rb =>
    let h' ← mkSemiringPrefix ``Grind.Ring.OfSemiring.of_eq
    let h' := mkApp3 h' (← mkSExprDecl sa) (← mkSExprDecl sb) (← mkEqProof a b)
    if let some h ← mkKronCore? ra rb c.p h' then return h
    let h ← mkStepPrefix ``Stepwise.core ``Stepwise.coreC
    return mkApp5 h (← mkExprDecl ra) (← mkExprDecl rb) (← mkPolyDecl c.p) (← mkPolyRefl c.p) h'
  | .superpose k₁ m₁ c₁ k₂ m₂ c₂ =>
    let h ← mkStepPrefix ``Stepwise.superpose ``Stepwise.superposeC
    let hs ← mkMergeHints (← mulMonR k₁ m₁ c₁.p) (← mulMonR k₂ m₂ c₂.p) c.p
    return mkAppN h #[
      toExpr k₁, ← mkMonDecl m₁, ← mkPolyDecl c₁.p,
      toExpr k₂, ← mkMonDecl m₂, ← mkPolyDecl c₂.p,
      ← mkPolyDecl c.p, hs, ← mkPolyRefl c.p, ← toExprProof c₁, ← toExprProof c₂]
  | .simp k₁ c₁ k₂ m₂ c₂ =>
    if k₁ == 1 then
      let (base, steps) ← collectSimps1 c₁ #[(k₂, m₂, c₂, c)]
      let steps := steps.reverse
      let leaves ← steps.mapM fun (k₂, m₂, c₂, _) => do
        let t := mkApp3 (mkConst ``Grind.CommRing.SumTree.leaf) (toExpr k₂) (← mkMonDecl m₂) (← mkPolyDecl c₂.p)
        return (← mulMonR k₂ m₂ c₂.p, t, ← toExprProof c₂)
      let hBase ← toExprProof base
      let hs ← steps.mapIdxM fun i (k₂, m₂, c₂, _) => return (k₂, m₂, c₂.p, leaves[i]!.2.2)
      -- The chain `c.p = base.p + Σ kᵢ * mᵢ * cᵢ.p` is checked at once by Kronecker substitution
      -- when it applies, otherwise when the sum tree pays off.
      if steps.size > 1 then
        if let some h ← mkKronSum? ``Stepwise.simpsK ``Stepwise.simpsKC ``Stepwise.simpsM ``Stepwise.simpsMC #[] base.p c.p hs then
          return mkApp h hBase
      let (q, _, _, treeCost) ← mkSumTree leaves 0 leaves.size
      let seqCost := stepwiseCost base.p (steps.zipWith (fun (_, _, _, c) (q, _, _) => (q, c.p)) leaves)
      let rootHs := mergeHints base.p q #[]
      if steps.size > 1 && useSumTree (treeCost + hintsWalk rootHs) seqCost then
        let h ← mkPackedSum ``Stepwise.simpsP ``Stepwise.simpsPC #[] base.p c.p hs
        return mkApp h hBase
      -- One step at a time; the proofs of the intermediate constraints are cached.
      let mut prev := base
      let mut hPrev := hBase
      for h : i in [0:steps.size] do
        let (k₂, m₂, c₂, cᵢ) := steps[i]
        let (qᵢ, _, hᵢ) := leaves[i]!
        let hs ← mkMergeHints prev.p qᵢ cᵢ.p
        let pr := mkAppN (← mkStepPrefix ``Stepwise.simp1 ``Stepwise.simp1C) #[
          ← mkPolyDecl prev.p, toExpr k₂, ← mkMonDecl m₂, ← mkPolyDecl c₂.p,
          ← mkPolyDecl cᵢ.p, hs, ← mkPolyRefl cᵢ.p, hPrev, hᵢ]
        if i + 1 < steps.size then
          let addr := unsafe (ptrAddrUnsafe cᵢ).toUInt64 >>> 2
          modify fun s => { s with cache := s.cache.insert addr pr }
        prev := cᵢ
        hPrev := pr
      return hPrev
    let h ← mkStepPrefix ``Stepwise.simp ``Stepwise.simpC
    let hs ← mkMergeHints (← mulConstR k₁ c₁.p) (← mulMonR k₂ m₂ c₂.p) c.p
    return mkAppN h #[
      toExpr k₁, ← mkPolyDecl c₁.p,
      toExpr k₂, ← mkMonDecl m₂, ← mkPolyDecl c₂.p,
      ← mkPolyDecl c.p, hs, ← mkPolyRefl c.p, ← toExprProof c₁, ← toExprProof c₂]
  | .mul k c₁ =>
    let h ← mkStepPrefix ``Stepwise.mul ``Stepwise.mulC
    return mkApp5 h (← mkPolyDecl c₁.p) (toExpr k) (← mkPolyDecl c.p) eagerReflBoolTrue (← toExprProof c₁)
  | .div k c₁ =>
    let h ← mkStepPrefix ``Stepwise.div ``Stepwise.divC
    let some nzInst ← noZeroDivisorsInst?
      | throwNoNatZeroDivisors
    return mkApp6 h nzInst (← mkPolyDecl c₁.p) (toExpr k) (← mkPolyDecl c.p) eagerReflBoolTrue (← toExprProof c₁)
  | .gcd a b c₁ c₂ =>
    let h ← mkStepBasicPrefix ``Grind.CommRing.eq_gcd
    return mkApp8 h (toExpr a) (toExpr b) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c.p)
      eagerReflBoolTrue (← toExprProof c₁) (← toExprProof c₂)
  | .numEq0 k c₁ c₂ =>
    let h ← mkStepBasicPrefix ``Grind.CommRing.eq_normEq0
    return mkApp7 h (toExpr k) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c.p)
      eagerReflBoolTrue (← toExprProof c₁) (← toExprProof c₂)

/--
The steps with multiplier `1` of the derivation `d`, from the outermost one down, and the
derivation below them.
-/
private partial def collectSteps1 (d : PolyDerivation) (acc : Array (Int × Mon × EqCnstr × Poly)) :
    PolyDerivation × Array (Int × Mon × EqCnstr × Poly) :=
  match d with
  | .step p 1 d k₂ m₂ c₂ => collectSteps1 d (acc.push (k₂, m₂, c₂, p))
  | d => (d, acc)

open Lean.Grind.CommRing in
/--
Given a polynomial derivation, returns `(k, p₀, h)` where `h` is a proof that
`k*p₀ = d.p`
-/
private partial def derivToExprProof (d : PolyDerivation) : ProofM (Int × Poly × Expr) := do
  match d with
  | .step p 1 d' k₂ m₂ c₂ =>
    let (base, steps) := collectSteps1 d' #[(k₂, m₂, c₂, p)]
    if steps.size == 1 then derivStep p 1 d' k₂ m₂ c₂ else
    let steps := steps.reverse
    let (k, p₀, h₁) ← derivToExprProof base
    let leaves ← steps.mapM fun (k₂, m₂, c₂, _) => do
      let t := mkApp3 (mkConst ``Grind.CommRing.SumTree.leaf) (toExpr k₂) (← mkMonDecl m₂) (← mkPolyDecl c₂.p)
      return (← mulMonR k₂ m₂ c₂.p, t, ← c₂.toExprProof)
    -- The chain `p = base.p + Σ kᵢ * mᵢ * pᵢ` is checked at once by Kronecker substitution when it
    -- applies, otherwise when the sum tree pays off.
    let hs ← steps.mapIdxM fun i (k₂, m₂, c₂, _) => return (k₂, m₂, c₂.p, leaves[i]!.2.2)
    if let some h ← mkKronSum? ``Stepwise.d_stepsK ``Stepwise.d_stepsKC ``Stepwise.d_stepsM ``Stepwise.d_stepsMC #[toExpr k, ← mkPolyDecl p₀] base.p p hs then
      return (k, p₀, mkApp h h₁)
    let (q, _, _, treeCost) ← mkSumTree leaves 0 leaves.size
    let seqCost := stepwiseCost base.p (steps.zipWith (fun (_, _, _, p) (q, _, _) => (q, p)) leaves)
    let rootHs := mergeHints base.p q #[]
    if useSumTree (treeCost + hintsWalk rootHs) seqCost then
      let h ← mkPackedSum ``Stepwise.d_stepsP ``Stepwise.d_stepsPC #[toExpr k, ← mkPolyDecl p₀] base.p p hs
      return (k, p₀, mkApp h h₁)
    -- One step at a time.
    let mut prev := base.p
    let mut hPrev := h₁
    for h : i in [0:steps.size] do
      let (k₂, m₂, c₂, pᵢ) := steps[i]
      let (qᵢ, _, hᵢ) := leaves[i]!
      let hs ← mkMergeHints prev qᵢ pᵢ
      hPrev := mkAppN (← mkStepPrefix ``Stepwise.d_step1 ``Stepwise.d_step1C) #[
        toExpr k, ← mkPolyDecl p₀, ← mkPolyDecl prev,
        toExpr k₂, ← mkMonDecl m₂, ← mkPolyDecl c₂.p, ← mkPolyDecl pᵢ,
        hs, ← mkPolyRefl pᵢ, hPrev, hᵢ]
      prev := pᵢ
    return (k, p₀, hPrev)
  | .step p k₁ d k₂ m₂ c₂ => derivStep p k₁ d k₂ m₂ c₂
  | .input p₀ =>
    let h := mkApp (← mkStepBasicPrefix ``Stepwise.d_init) (← mkPolyDecl p₀)
    return (1, p₀, h)
  | .normEq0 p d c =>
    let (k, p₀, h₁) ← derivToExprProof d
    let h₂ ← c.toExprProof
    let .num a := c.p | unreachable!
    let h ← mkStepBasicPrefix ``Grind.CommRing.d_normEq0
    let h := mkApp9 h
      (toExpr k) (toExpr a.natAbs) (← mkPolyDecl p₀) (← mkPolyDecl d.p)
      (← mkPolyDecl c.p) (← mkPolyDecl p) eagerReflBoolTrue h₁ h₂
    return (k, p₀, h)
where
  derivStep (p : Poly) (k₁ : Int) (d : PolyDerivation) (k₂ : Int) (m₂ : Mon) (c₂ : EqCnstr) : ProofM (Int × Poly × Expr) := do
    let (k, p₀, h₁) ← derivToExprProof d
    let h₂ ← c₂.toExprProof
    let (h, a) ← if k₁ == 1 then
      pure (← mkStepPrefix ``Stepwise.d_step1 ``Stepwise.d_step1C, d.p)
    else
      pure (mkApp (← mkStepPrefix ``Stepwise.d_stepk ``Stepwise.d_stepkC) (toExpr k₁), ← mulConstR k₁ d.p)
    let hs ← mkMergeHints a (← mulMonR k₂ m₂ c₂.p) p
    let h := mkAppN h #[
      toExpr k, ← mkPolyDecl p₀, ← mkPolyDecl d.p,
      toExpr k₂, ← mkMonDecl m₂, ← mkPolyDecl c₂.p, ← mkPolyDecl p,
      hs, ← mkPolyRefl p, h₁, h₂]
    return (k₁*k, p₀, h)

open Lean.Grind.CommRing in
/--
The proof of `lhs = rhs` from `h₁ : k * p₀ = d.p` by Kronecker substitution (`Stepwise.imp_1eqK`,
`Stepwise.imp_keqK`): `lhs - rhs` and `p₀` have the same value at the point, if the values stay
below a few million bits. In characteristic `c`, the difference over `Int` is `c * E` for a stated
polynomial `E`.
-/
private def mkKronImp? (lhs rhs : RingExpr) (d : PolyDerivation) (k : Int) (p₀ : Poly) (h₁ : Expr) : ProofM (Option Expr) := do
  let e : RingExpr := .sub lhs rhs
  let deg := max (exprDegB e) (polyMaxDeg p₀)
  let B := max 2 (deg + 1)
  let c? ← nonzeroChar?
  let E : Poly ← match c? with
    | none => pure (.num 0)
    | some c =>
      let diff := e.toPoly.combine (p₀.mulConst (-1))
      let E := diff.divConst c
      unless E.mulConst c == diff do return none
      pure E
  let c := c?.getD 0
  let maxCode := max (exprMaxCode B e) (polyMaxCode B p₀)
  let some K := kronExponent? (exprMajorant e + polyNorm1 p₀ + c * polyNorm1 E) maxCode 4000000 | return none
  let pre ← if k == 1 then
    mkStepPrefix ``Stepwise.imp_1eqK ``Stepwise.imp_1eqKC
  else
    let some nzInst ← noZeroDivisorsInst? | return none
    pure <| mkApp2 (← mkStepPrefix ``Stepwise.imp_keqK ``Stepwise.imp_keqKC) nzInst (toExpr k)
  let eArgs ← if c?.isSome then pure #[← mkPPolyDecl E B] else pure #[]
  let dp ← mkPolyDecl d.p
  let kArgs := if k == 1 then #[] else #[eagerReflBoolFalse]
  return some (mkAppN pre (#[mkRawNatLit K, mkRawNatLit B, ← mkExprDecl lhs, ← mkExprDecl rhs, ← mkPolyDecl p₀, dp] ++ eArgs ++
    kArgs ++ #[eagerReflBoolTrue, eagerReflBoolTrue, mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Grind.CommRing.Poly) dp, h₁]))

open Lean.Grind.CommRing in
/--
Given a derivation `d` for `k * p = 0` where `lhs - rhs = p`, returns a proof for `lhs = rhs`.
-/
private def mkImpEqExprProof (lhs rhs : RingExpr) (d : PolyDerivation) : ProofM Expr := do
  assert! d.p matches .num 0
  let (k, p₀, h₁) ← derivToExprProof d
  if let some h ← mkKronImp? lhs rhs d k p₀ h₁ then return h
  let h ← if k == 1 then
    mkStepPrefix ``Stepwise.imp_1eq ``Stepwise.imp_1eqC
  else
    let some nzInst ← noZeroDivisorsInst?
      | throwNoNatZeroDivisors
    pure <| mkApp2 (← mkStepPrefix ``Stepwise.imp_keq ``Stepwise.imp_keqC) nzInst (toExpr k)
  return mkApp6 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl p₀) (← mkPolyDecl d.p) eagerReflBoolTrue h₁

/--
Caches for `polyToExprShared`. The polynomials of a proof have few distinct monomials and
coefficients, but they are separate objects; without the caches, their expressions would be
copies that the kernel hash-conses again.
-/
private structure SharedExprCache where
  mons  : Std.HashMap Mon Expr := {}
  ints  : Std.HashMap Int Expr := {}

private def monToExprShared (m : Mon) : StateM SharedExprCache Expr := do
  if let some e := (← get).mons[m]? then return e
  let e := toExpr m
  modify fun c => { c with mons := c.mons.insert m e }
  return e

private def intToExprShared (k : Int) : StateM SharedExprCache Expr := do
  if let some e := (← get).ints[k]? then return e
  let e := mkIntLitK k
  modify fun c => { c with ints := c.ints.insert k e }
  return e

/-- `toExpr p` with shared monomial and coefficient expressions. -/
private def polyToExprShared (p : Poly) : StateM SharedExprCache Expr :=
  match p with
  | .num k => return mkApp (mkConst ``Grind.CommRing.Poly.num) (← intToExprShared k)
  | .add k m p => return mkApp3 (mkConst ``Grind.CommRing.Poly.add) (← intToExprShared k) (← monToExprShared m) (← polyToExprShared p)

private def mkContext (h : Expr) : ProofM Expr := do
  let usedVars     :=
    collectMapVars (← get).monDecls (·.collectVars) >>
    collectMapVars (← get).polyDecls (·.collectVars) >>
    collectMapVars (← get).exprDecls (·.collectVars) <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getRingState).vars
  let vars         := vars'.map fun x => vars[x]!
  let (vals, cache) := ((← get).polyDecls.foldM (init := ({} : Std.HashMap Poly Expr)) fun (vals : Std.HashMap Poly Expr) (p : Poly) _ =>
    return vals.insert p (← polyToExprShared (p.renameVars varRename))).run {}
  let (mvals, _) := ((← get).monDecls.foldM (init := ({} : Std.HashMap Mon Expr)) fun (vals : Std.HashMap Mon Expr) (m : Mon) _ =>
    return vals.insert m (← monToExprShared (m.renameVars varRename))).run cache
  let h := mkLetOfMap (← get).polyDecls h `p (mkConst ``Grind.CommRing.Poly) (vals[·]!)
  let h := mkLetOfMap (← get).monDecls h `m (mkConst ``Grind.CommRing.Mon) (mvals[·]!)
  let h := mkLetOfMap (← get).ppolyDecls h `pp (mkConst ``Grind.CommRing.PPoly) fun (p, B) => packedPolyExpr B (p.renameVars varRename)
  let h := mkLetOfMap (← get).exprDecls h `e (mkConst ``Grind.CommRing.Expr) fun e => toExpr <| e.renameVars varRename
  let h := h.abstract #[(← read).ctx]
  if h.hasLooseBVars then
    let ring ← getRing
    let ctxType := mkApp (mkConst ``RArray [ring.u]) ring.type
    let ctxVal ← toContextExpr vars
    return .letE `ctx ctxType ctxVal h (nondep := false)
  else
    return h

private def mkSemiringContext (h : Expr) : ProofM Expr := do
  let some sctx := (← read).sctx? | return h
  let some semiringId := (← getCommRing).semiringId? | return h
  let semiring ← getSemiringOf
  let usedVars     := collectMapVars (← get).sexprDecls (·.collectVars) {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let svars        ← SemiringM.run semiringId do return (← getSemiringState).vars
  let vars         := vars'.map fun x => svars[x]!
  let h := mkLetOfMap (← get).sexprDecls h `s (mkConst ``Grind.CommRing.Expr) fun s => toExpr <| s.renameVars varRename
  let h := h.abstract #[sctx]
  if h.hasLooseBVars then
    let ctxType := mkApp (mkConst ``RArray [semiring.u]) semiring.type
    let ctxVal ← toSContextExpr semiringId vars
    return .letE `sctx ctxType ctxVal h (nondep := false)
  else
    return h

private abbrev withProofContext (x : ProofM Expr) : RingM Expr := do
  let ctx := mkFVar (← mkFreshFVarId)
  let sctx? ← if (← getCommRing).semiringId?.isSome then pure <| some (mkFVar (← mkFreshFVarId)) else pure none
  go { ctx, sctx? } |>.run' {}
where
  go : ProofM Expr := do
    let h ← x
    let h ← mkContext h
    mkSemiringContext h

open Lean.Grind.CommRing in
def EqCnstr.setUnsat  (c : EqCnstr) : RingM Unit := do
  let h ← withProofContext do
    let ring ← getCommRing
    if let some (charInst, char) := ring.charInst? then
      let mut h ← mkStepPrefix ``Stepwise.unsat_eq ``Stepwise.unsat_eqC
      if char == 0 then
        h := mkApp h charInst
      let k ← getPolyConst c.p
      return mkApp4 h (← mkPolyDecl c.p) (toExpr k) eagerReflBoolTrue (← c.toExprProof)
    else if let some fieldInst := ring.fieldInst? then
      return mkApp6 (mkConst ``Grind.CommRing.one_eq_zero_unsat [ring.u]) ring.type fieldInst (← getContext)
        (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
    else
      throwError "`grind ring` internal error, unexpected unsat eq proof {← c.denoteExpr}"
  closeGoal h

def DiseqCnstr.setUnsat (c : DiseqCnstr) : RingM Unit := do
  let h ← withProofContext do
    let heq ← mkImpEqExprProof c.rlhs c.rrhs c.d
    let hne ← if let some (sa, sb) := c.ofSemiring? then
      let h ← mkSemiringAddRightCancelPrefix ``Grind.Ring.OfSemiring.of_diseq
      pure <| mkApp3 h (← mkSExprDecl sa) (← mkSExprDecl sb) (← mkDiseqProof c.lhs c.rhs)
    else
      mkDiseqProof c.lhs c.rhs
    return mkApp hne heq
  closeGoal h

def propagateEq (a b : Expr) (ra rb : RingExpr) (d : PolyDerivation) : RingM Unit := do
  let heq ← withProofContext do
    mkImpEqExprProof ra rb d
  let ring ← getRing
  let eq := mkApp3 (mkConst ``Eq [.succ ring.u]) ring.type a b
  pushEq a b <| mkExpectedPropHint heq eq

/--
Given `a` and `b`, such that `a ≠ b` in the core and `sa` and `sb` their reified semiring
terms s.t. `sa.toPoly == sb.toPoly`, close the goal.
-/
def setSemiringDiseqUnsat (a b : Expr) (sa sb : SemiringExpr) : SemiringM Unit := do
  let semiring ← getCommSemiring
  let hne ← mkDiseqProof a b
  let usedVars     := sa.collectVars >> sb.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getSemiringState).vars
  let vars         := vars'.map fun x => vars[x]!
  let sa           := sa.renameVars varRename
  let sb           := sb.renameVars varRename
  let ctx          ← toSContextExpr' vars
  let h := mkApp3 (mkConst ``Grind.CommRing.eq_normS [semiring.u]) semiring.type semiring.commSemiringInst ctx
  let h := mkApp3 h (toExpr sa) (toExpr sb) eagerReflBoolTrue
  closeGoal (mkApp hne h)

/--
Given `a` and `b`, such that `a ≠ b` in the core and `ra` and `rb` their reified ring
terms s.t. `ra.toPoly_nc == rb.toPoly_nc`, close the goal.
-/
def setNonCommRingDiseqUnsat (a b : Expr) (ra rb : RingExpr) : NonCommRingM Unit := do
  let ring ← getRing
  let hne ← mkDiseqProof a b
  let usedVars     := ra.collectVars >> rb.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getRingState).vars
  let vars         := vars'.map fun x => vars[x]!
  let ra           := ra.renameVars varRename
  let rb           := rb.renameVars varRename
  let ctx          ← toContextExpr vars
  let h := if let some (charInst, c) := ring.charInst? then
    mkApp5 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_nc_eq [ring.u]) ring.type (toExpr c) ring.ringInst charInst ctx
  else
    mkApp3 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_nc_eq [ring.u]) ring.type ring.ringInst ctx
  let h := mkApp3 h (toExpr ra) (toExpr rb) eagerReflBoolTrue
  closeGoal (mkApp hne h)

/--
Given `a` and `b`, such that `a ≠ b` in the core and `sa` and `sb` their reified semiring
terms s.t. `sa.toPolyS_nc == sb.toPolyS_nc`, close the goal.
-/
def setNonCommSemiringDiseqUnsat (a b : Expr) (sa sb : SemiringExpr) : NonCommSemiringM Unit := do
  let semiring ← getSemiring
  let hne ← mkDiseqProof a b
  let usedVars     := sa.collectVars >> sb.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getSemiringState).vars
  let vars         := vars'.map fun x => vars[x]!
  let sa           := sa.renameVars varRename
  let sb           := sb.renameVars varRename
  let ctx          ← toSContextExpr' vars
  let h := mkApp3 (mkConst ``Grind.CommRing.eq_normS_nc [semiring.u]) semiring.type semiring.semiringInst ctx
  let h := mkApp3 h (toExpr sa) (toExpr sb) eagerReflBoolTrue
  closeGoal (mkApp hne h)

/--
Given `a ≠ b` in the core, where `a b : type` and `charInst : IsCharP type semiringInst 1`,
close the goal.
-/
def setCharOneDiseqUnsat (u : Level) (type semiringInst charInst a b : Expr) : GoalM Unit := do
  let h := mkApp5 (mkConst ``Grind.IsCharP.eq_of_charOne [u]) type semiringInst charInst a b
  closeGoal (mkApp (← mkDiseqProof a b) h)

private structure NormResult where
  lhs  : RingExpr
  rhs  : RingExpr
  lhs' : RingExpr
  rhs' : RingExpr
  vars : Array Expr

private def norm (vars : PArray Expr) (lhs rhs lhs' rhs' : RingExpr) : NormResult :=
  let usedVars     := lhs.collectVars >> rhs.collectVars >> lhs'.collectVars >> rhs'.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := vars'.map fun x => vars[x]!
  let lhs          := lhs.renameVars varRename
  let rhs          := rhs.renameVars varRename
  let lhs'         := lhs'.renameVars varRename
  let rhs'         := rhs'.renameVars varRename
  { lhs, rhs, lhs', rhs', vars }

def mkLeIffProof (leInst ltInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, rhs, lhs', rhs', vars } := norm (← getRingState).vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp6 (mkConst ``Grind.CommRing.le_norm_expr [ring.u]) ring.type ring.commRingInst leInst ltInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let leFn := mkApp2 (mkConst ``LE.le [ring.u]) ring.type leInst
  let le   := mkApp2 leFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let le'  := mkApp2 leFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq le le'
  return mkExpectedPropHint h expected

def mkLtIffProof (leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, rhs, lhs', rhs', vars } := norm (← getRingState).vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp7 (mkConst ``Grind.CommRing.lt_norm_expr [ring.u]) ring.type ring.commRingInst leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let ltFn := mkApp2 (mkConst ``LT.lt [ring.u]) ring.type ltInst
  let lt   := mkApp2 ltFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let lt'  := mkApp2 ltFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq lt lt'
  return mkExpectedPropHint h expected

def mkEqIffProof (lhs rhs lhs' rhs' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, rhs, lhs', rhs', vars } := norm (← getRingState).vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.eq_norm_expr [ring.u]) ring.type ring.commRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let eq   := mkApp2 eqFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let eq'  := mkApp2 eqFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq eq eq'
  return mkExpectedPropHint h expected

/--
Given `e` and `e'` s.t. `e.toPoly == e'.toPoly`, returns a proof that `e.denote ctx = e'.denote ctx`
-/
def mkTermEqProof (e e' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, lhs', vars, .. } := norm (← getRingState).vars e (.num 0) e' (.num 0)
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_eq [ring.u]) ring.type ring.commRingInst
  let h := mkApp4 h ctx (toExpr lhs) (toExpr lhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let expected := mkApp2 eqFn (← lhs.denoteExpr' vars) (← lhs'.denoteExpr' vars)
  return mkExpectedPropHint h expected

def mkNonCommLeIffProof (leInst ltInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, rhs, lhs', rhs', vars } := norm (← getRingState).vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp6 (mkConst ``Grind.CommRing.le_norm_expr_nc [ring.u]) ring.type ring.ringInst leInst ltInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let leFn := mkApp2 (mkConst ``LE.le [ring.u]) ring.type leInst
  let le   := mkApp2 leFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let le'  := mkApp2 leFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq le le'
  return mkExpectedPropHint h expected

def mkNonCommLtIffProof (leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, rhs, lhs', rhs', vars } := norm (← getRingState).vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp7 (mkConst ``Grind.CommRing.lt_norm_expr_nc [ring.u]) ring.type ring.ringInst leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let ltFn := mkApp2 (mkConst ``LT.lt [ring.u]) ring.type ltInst
  let lt   := mkApp2 ltFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let lt'  := mkApp2 ltFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq lt lt'
  return mkExpectedPropHint h expected

def mkNonCommEqIffProof (lhs rhs lhs' rhs' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, rhs, lhs', rhs', vars } := norm (← getRingState).vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.eq_norm_expr_nc [ring.u]) ring.type ring.ringInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let eq   := mkApp2 eqFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let eq'  := mkApp2 eqFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq eq eq'
  return mkExpectedPropHint h expected

/--
Given `e` and `e'` s.t. `e.toPoly_nc == e'.toPoly_nc`, returns a proof that `e.denote ctx = e'.denote ctx`
-/
def mkNonCommTermEqProof (e e' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, lhs', vars, .. } := norm (← getRingState).vars e (.num 0) e' (.num 0)
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_nc_eq [ring.u]) ring.type ring.ringInst
  let h := mkApp4 h ctx (toExpr lhs) (toExpr lhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let expected := mkApp2 eqFn (← lhs.denoteExpr' vars) (← lhs'.denoteExpr' vars)
  return mkExpectedPropHint h expected

end Lean.Meta.Grind.Arith.CommRing
