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

/-- Returns `true` if `x` has been eliminated using an equality constraint. -/
def eliminated (x : Var) : GoalM Bool :=
  return (← get').elimEqs[x]!.isSome

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

def _root_.Int.Linear.Poly.pp (p : Poly) : GoalM MessageData := do
  match p with
  | .num k => return m!"{k}"
  | .add 1 x p => go (quoteIfNotAtom (← getVar x)) p
  | .add k x p => go m!"{k}*{quoteIfNotAtom (← getVar x)}" p
where
  go (r : MessageData)  (p : Int.Linear.Poly) : GoalM MessageData := do
    match p with
    | .num 0 => return r
    | .num k => return m!"{r} + {k}"
    | .add 1 x p => go m!"{r} + {quoteIfNotAtom (← getVar x)}" p
    | .add k x p => go m!"{r} + {k}*{quoteIfNotAtom (← getVar x)}" p

def _root_.Int.Linear.Poly.denoteExpr' (p : Poly) : GoalM Expr := do
  let vars ← getVars
  return (← p.denoteExpr (vars[·]!))

def DvdCnstr.isTrivial (c : DvdCnstr) : Bool :=
  match c.p with
  | .num k' => k' % c.d == 0
  | _ => c.d == 1

def DvdCnstr.pp (c : DvdCnstr) : GoalM MessageData := do
  return m!"{c.d} ∣ {← c.p.pp}"

def DvdCnstr.denoteExpr (c : DvdCnstr) : GoalM Expr := do
  return mkIntDvd (toExpr c.d) (← c.p.denoteExpr')

def DvdCnstr.throwUnexpected (c : DvdCnstr) : GoalM α := do
  throwError "`grind` internal error, unexpected{indentD (← c.pp)} "

def LeCnstr.isTrivial (c : LeCnstr) : Bool :=
  match c.p with
  | .num k => k ≤ 0
  | _ => false

def LeCnstr.pp (c : LeCnstr) : GoalM MessageData := do
  return m!"{← c.p.pp} ≤ 0"

def LeCnstr.denoteExpr (c : LeCnstr) : GoalM Expr := do
  return mkIntLE (← c.p.denoteExpr') (mkIntLit 0)

def LeCnstr.throwUnexpected (c : LeCnstr) : GoalM α := do
  throwError "`grind` internal error, unexpected{indentD (← c.pp)}"

def EqCnstr.isTrivial (c : LeCnstr) : Bool :=
  match c.p with
  | .num k => k == 0
  | _ => false

def EqCnstr.pp (c : EqCnstr) : GoalM MessageData := do
  return m!"{← c.p.pp} = 0"

def EqCnstr.denoteExpr (c : EqCnstr) : GoalM Expr := do
  return mkIntEq (← c.p.denoteExpr') (mkIntLit 0)

def EqCnstr.throwUnexpected (c : LeCnstr) : GoalM α := do
  throwError "`grind` internal error, unexpected{indentD (← c.pp)}"

/-- Returns occurrences of `x`. -/
def getOccursOf (x : Var) : GoalM (PHashSet Var) :=
  return (← get').occurs[x]!

/--
Adds `y` as an occurrence of `x`.
That is, `x` occurs in `lowers[y]`, `uppers[y]`, or `dvdCnstrs[y]`.
-/
def addOcc (x : Var) (y : Var) : GoalM Unit := do
  unless (← getOccursOf x).contains y do
    modify' fun s => { s with occurs := s.occurs.modify x fun ys => ys.insert y }

/--
Given `p` a polynomial being inserted into `lowers`, `uppers`, or `dvdCnstrs`,
get its leading variable `y`, and adds `y` as an occurrence for the remaining variables in `p`.
-/
partial def _root_.Int.Linear.Poly.updateOccs (p : Poly) : GoalM Unit := do
  let .add _ y p := p | throwError "`grind` internal error, unexpected constant polynomial"
  let rec go (p : Poly) : GoalM Unit := do
    let .add _ x p := p | return ()
    addOcc x y; go p
  go p

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

abbrev DvdCnstr.caching (c : DvdCnstr) (k : ProofM Expr) : ProofM Expr :=
  Cutsat.caching c.id k

abbrev LeCnstr.caching (c : LeCnstr) (k : ProofM Expr) : ProofM Expr :=
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

abbrev LeCnstr.isUnsat (c : LeCnstr) : Bool :=
  c.p.isUnsatLe

abbrev DvdCnstr.isUnsat (c : DvdCnstr) : Bool :=
  c.p.isUnsatDvd c.d

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def DvdCnstr.satisfied (c : DvdCnstr) : GoalM LBool := do
  let some v ← c.p.eval? | return .undef
  return decide (c.d ∣ v) |>.toLBool

def _root_.Int.Linear.Poly.satisfiedLe (p : Poly) : GoalM LBool := do
  let some v ← p.eval? | return .undef
  return decide (v <= 0) |>.toLBool

/--
Returns `.true` if `c` is satisfied by the current partial model,
`.undef` if `c` contains unassigned variables, and `.false` otherwise.
-/
def LeCnstr.satisfied (c : LeCnstr) : GoalM LBool := do
  c.p.satisfiedLe

end Lean.Meta.Grind.Arith.Cutsat
