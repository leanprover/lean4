/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Int.Linear
def Poly.isZero : Poly → Bool
  | .num 0 => true
  | _ => false

/--
Returns `true` if the variables in the given polynomial are sorted
in decreasing order.
-/
def Poly.isSorted (p : Poly) : Bool :=
  go none p
where
  go : Option Var → Poly → Bool
  | _,      .num _     => true
  | none,   .add _ y p => go (some y) p
  | some x, .add _ y p => x > y && go (some y) p

def DvdCnstr.isSorted (c : DvdCnstr) : Bool :=
  c.p.isSorted

def DvdCnstr.isTrivial (c : DvdCnstr) : Bool :=
  match c.p with
  | .num k' => k' % c.k == 0
  | _ => c.k == 1

def RelCnstr.isSorted (c : RelCnstr) : Bool :=
  c.p.isSorted

def RelCnstr.isTrivial : RelCnstr → Bool
  | .eq (.num 0) => true
  | .le (.num k) => k ≤ 0
  | _ => false

end Int.Linear

namespace Lean.Meta.Grind.Arith.Cutsat
/--
`gcdExt a b` returns the triple `(g, α, β)` such that
- `g = gcd a b` (with `g ≥ 0`), and
- `g = α * a + β * β`.
-/
partial def gcdExt (a b : Int) : Int × Int × Int :=
  if b = 0 then
    (a.natAbs, if a = 0 then 0 else a / a.natAbs, 0)
  else
    let (g, α, β) := gcdExt b (a % b)
    (g, β, α - (a / b) * β)

def get' : GoalM State := do
  return (← get).arith.cutsat

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.cutsat := f s.arith.cutsat }

def getVars : GoalM (PArray Expr) :=
  return (← get').vars

def getVar (x : Var) : GoalM Expr :=
  return (← get').vars[x]!

def mkCnstrId : GoalM Nat := do
  let id := (← get').nextCnstrId
  modify' fun s => { s with nextCnstrId := id + 1 }
  return id

private partial def shrink (a : PArray Int) (sz : Nat) : PArray Int :=
  if a.size > sz then
    shrink a.pop sz
  else
    a

/-- Resets the assingment of any variable bigger or equal to `x`. -/
def resetAssignmentFrom (x : Var) : GoalM Unit := do
  modify' fun s => { s with assignment := shrink s.assignment x }

def DvdCnstrWithProof.denoteExpr (cₚ : DvdCnstrWithProof) : GoalM Expr := do
  let vars ← getVars
  cₚ.c.denoteExpr (vars[·]!)

def RelCnstrWithProof.denoteExpr (cₚ : RelCnstrWithProof) : GoalM Expr := do
  let vars ← getVars
  cₚ.c.denoteExpr (vars[·]!)

def RelCnstrWithProof.throwUnexpected (cₚ : RelCnstrWithProof) : GoalM α := do
  throwError "`grind` internal error, unexpected{indentExpr (← cₚ.denoteExpr)} "

def DvdCnstrWithProof.throwUnexpected (cₚ : DvdCnstrWithProof) : GoalM α := do
  throwError "`grind` internal error, unexpected{indentExpr (← cₚ.denoteExpr)} "

def toContextExpr : GoalM Expr := do
  let vars ← getVars
  if h : 0 < vars.size then
    return RArray.toExpr (mkConst ``Int) id (RArray.ofFn (vars[·]) h)
  else
    return RArray.toExpr (mkConst ``Int) id (RArray.leaf (mkIntLit 0))

structure ProofM.State where
  cache : Std.HashMap Nat Expr := {}

/-- Auxiliary monad for constructing cutsat proofs. -/
abbrev ProofM := ReaderT Expr (StateRefT ProofM.State GoalM)

/-- Returns a Lean expression representing the variable context used to construct cutsat proofs. -/
abbrev getContext : ProofM Expr := do
  read

abbrev caching (id : Nat) (k : ProofM Expr) : ProofM Expr := do
  if let some h := (← get).cache[id]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert id h }
    return h

abbrev DvdCnstrWithProof.caching (c : DvdCnstrWithProof) (k : ProofM Expr) : ProofM Expr :=
  Cutsat.caching c.id k

abbrev RelCnstrWithProof.caching (c : RelCnstrWithProof) (k : ProofM Expr) : ProofM Expr :=
  Cutsat.caching c.id k

abbrev withProofContext (x : ProofM Expr) : GoalM Expr := do
  withLetDecl `ctx (mkApp (mkConst ``RArray) (mkConst ``Int)) (← toContextExpr) fun ctx => do
    let h ← x ctx |>.run' {}
    mkLetFVars #[ctx] h

/--
Tries to evaluate the polynomial `p` using the partial model/assignment built so far.
The result is `none` if the polynomial contains variables that have not been assigned.
-/
def _root_.Int.Linear.Poly.eval? (p : Poly) : GoalM (Option Int) := do
  let a := (← get').assignment
  let rec go (v : Int) : Poly → Option Int
    | .num k => some (v + k)
    | .add k x p =>
      if _ : x < a.size then
        go (v + k*a[x]) p
      else
        none
  return go 0 p

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def _root_.Int.Linear.DvdCnstr.satisfied (c : DvdCnstr) : GoalM LBool := do
  let some v ← c.p.eval? | return .undef
  return decide (c.k ∣ v) |>.toLBool

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def _root_.Int.Linear.RelCnstr.satisfied (c : RelCnstr) : GoalM LBool := do
  let some v ← c.p.eval? | return .undef
  match c with
  | .eq _ => return v == 0 |>.toLBool
  | .le _ => return decide (v <= 0) |>.toLBool

end Lean.Meta.Grind.Arith.Cutsat
