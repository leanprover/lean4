/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSemiringAdapter
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Sym.Arith.Types
import Lean.Meta.Sym.Arith.Poly
public section

namespace Lean.Meta.Grind.Arith.CommRing
export Lean.Grind.CommRing (Var Power Mon Poly)
export Lean.Meta.Sym.Arith (RingExpr SemiringExpr)

/-!
The classification of a type as a (commutative) ring or semiring, its instances, and its
cached operator functions live in `Sym.Arith.State`, a `SymExtension` shared by the whole
`grind` run. This module only stores per-goal solver state, in the structures below, indexed
by the ids assigned by `Sym.Arith.classify?`.
-/

mutual
structure EqCnstr where
  p     : Poly
  h     : EqCnstrProof
  sugar : Nat
  id    : Nat

inductive EqCnstrProof where
  | core (a b : Expr) (ra rb : RingExpr)
  | coreS (a b : Expr) (sa sb : SemiringExpr) (ra rb : RingExpr)
  | superpose (k₁ : Int) (m₁ : Mon) (c₁ : EqCnstr) (k₂ : Int) (m₂ : Mon) (c₂ : EqCnstr)
  | simp (k₁ : Int) (c₁ : EqCnstr) (k₂ : Int) (m₂ : Mon) (c₂ : EqCnstr)
  | mul (k : Int) (e : EqCnstr)
  | div (k : Int) (e : EqCnstr)
  | gcd (a b : Int) (c₁ c₂ : EqCnstr)
  | numEq0 (k : Nat) (c₁ c₂ : EqCnstr)
end

instance : Inhabited EqCnstrProof where
  default := .core default default default default

instance : Inhabited EqCnstr where
  default := { p := default, h := default, sugar := 0, id := 0 }

protected def EqCnstr.compare (c₁ c₂ : EqCnstr) : Ordering :=
  (compare c₁.sugar c₂.sugar) |>.then
  (compare c₁.p.degree c₂.p.degree) |>.then
  (compare c₁.id c₂.id)

abbrev Queue : Type := Std.TreeSet EqCnstr EqCnstr.compare

/--
A polynomial equipped with a chain of rewrite steps that justifies its equality to the original input.
From an input polynomial `p`, we use equations (i.e., `EqCnstr`) as rewriting rules.
For example, consider the following sequence of rewrites for the input polynomial `x^2 + x*y`
using the equations `x - 1 = 0` (`c₁`) and `y - 2 = 0` (`c₂`).
```
2*x^2 + x*y                  | s₁ := .input (2*x^2 + x*y)
=           - 2*x*(x - 1)
(2*x + x*y)                  | s₂ := .step (2*x + x*y)  1 s₁ (-2) x c₁
=           - 2*1*(x - 1)
(x*y + 2)                    | s₃ := .step (x*y + 2) 1 s₂ (-2) 1 c₁
=           - 1*y*(x - 1)
(y + 2)                      | s₄ := .step (y+2) 1 s₃ (-1) y c₁
=           - 1*1*(y - 2)
4                            | s₅ := .step 4 1 s₄ 1 1 c₂
```
From the chain above, we build the certificate
```
(-2*x - y - 2)*(x-1) + (-1)*(y-2)
```
for
```
4 = (2*x^2 + x*y)
```
because `x-1 = 0` and `y-2=0`
-/
inductive PolyDerivation where
  | input (p : Poly)
  | /--
    ```
    p = k₁*d.getPoly + k₂*m₂*c.p
    ```
    The coefficient `k₁` is used because the leading monomial in `c` may not be monic.
    Thus, if we follow the chain back to the input polynomial, we have that
    `p = C * input_p` for a `C` that is equal to the product of all `k₁`s in the chain.
    We have that `C ≠ 1` only if the ring does not implement `NoNatZeroDivisors`.
    Here is a small example where we simplify `x+y` using the equations
    `2*x - 1 = 0` (`c₁`), `3*y - 1 = 0` (`c₂`), and `6*z + 5 = 0` (`c₃`)
    ```
    x + y + z            | s₁ := .input (x + y + z)
    *2
    =   - 1*1*(2*x - 1)
    2*y + 2*z + 1        | s₂ := .step (2*y + 2*z + 1) 2 s₁ (-1) 1 c₁
    *3
    =   - 2*1*(3*y - 1)
    6*z + 5              | s₃ := .step (6*z + 5) 3 s₂ (-2) 1 c₂
    =   - 1*1*(6*z + 5)
    0                    | s₄ := .step (0) 1 s₃ (-1) 1 c₃
    ```
    For this chain, we build the certificate
    ```
    (-3)*(2*x - 1) + (-2)*(3*y - 1) + (-1)*(6*z + 5)
    ```
    for
    ```
    0 = 6*(x + y + z)
    ```
    Recall that if the ring implement `NoNatZeroDivisors`, then the following property holds:
    ```
    ∀ (k : Int) (a : α), k ≠ 0 → (intCast k) * a = 0 → a = 0
    ```
    grind can deduce that `x+y+z = 0`
    -/
    step (p : Poly) (k₁ : Int) (d : PolyDerivation) (k₂ : Int) (m₂ : Mon) (c : EqCnstr)
  | /--
    Given `c.p == .num k`
    ```
    p = d.getPoly.normEq0 k
    ```
    -/
    normEq0 (p : Poly) (d : PolyDerivation) (c : EqCnstr)

def PolyDerivation.p : PolyDerivation → Poly
  | .input p   => p
  | .step p .. => p
  | .normEq0 p .. => p

/-- A disequality `lhs ≠ rhs` asserted by the core. -/
structure DiseqCnstr where
  lhs : Expr
  rhs : Expr
  /-- Reified `lhs` -/
  rlhs : RingExpr
  /-- Reified `rhs` -/
  rrhs : RingExpr
  /-- `lhs - rhs` simplification chain. If it becomes `0` we have an inconsistency. -/
  d : PolyDerivation
  /--
  If `lhs` and `rhs` are semiring expressions that have been adapted as ring ones.
  The respective semiring reified expressions are stored here.
  -/
  ofSemiring? : Option (SemiringExpr × SemiringExpr)

/-- Per-goal solver state of a (commutative or not) semiring classified by `Sym.Arith`. -/
structure SemiringState where
  /-- Mapping from Lean expressions to their representations as `SemiringExpr` -/
  denote         : PHashMap ExprPtr SemiringExpr := {}
  /--
  Mapping from variables to their denotations.
  Remark each variable can be in only one ring.
  -/
  vars           : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap         : PHashMap ExprPtr Var := {}
  deriving Inhabited

/-- Per-goal solver state of a (commutative or not) ring classified by `Sym.Arith`. -/
structure RingState where
  /--
  Mapping from variables to their denotations.
  Remark each variable can be in only one ring.
  -/
  vars           : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap         : PHashMap ExprPtr Var := {}
  /-- Mapping from Lean expressions to their representations as `RingExpr` -/
  denote         : PHashMap ExprPtr RingExpr := {}
  deriving Inhabited

/-- Per-goal solver state of a commutative ring: the Gröbner basis machinery. -/
structure CommRingState extends RingState where
  /-- `denoteEntries` is `denote` as a `PArray` for deterministic traversal. -/
  denoteEntries  : PArray (Expr × RingExpr) := {}
  /-- Next unique id for `EqCnstr`s. -/
  nextId         : Nat := 0
  /-- Number of "steps": simplification and superposition. -/
  steps          : Nat := 0
  /-- Equations to process. -/
  queue          : Queue := {}
  /--
  The basis is currently just a list. If this is a performance bottleneck, we should use
  a better data-structure. For examples, we could use a simple indexing for the linear case
  where we map variable in the leading monomial to `EqCnstr`.
  -/
  basis          : List EqCnstr := {}
  /-- Disequalities. -/
  -- TODO: add indexing
  diseqs         : PArray DiseqCnstr := {}
  /--
  If `recheck` is `true`, then new equalities have been added to the basis since we checked
  disequalities and implied equalities.
  -/
  recheck        : Bool := false
  /-- Inverse theorems that have been already asserted. -/
  invSet         : PHashSet Expr := {}
  /-- Number of variables for which `PowIdentity` equations have been pushed. -/
  powIdentityVarCount : Nat := 0
  /--
  An equality of the form `c = 0`. It is used to simplify polynomial coefficients.
  -/
  numEq0?        : Option EqCnstr := none
  /-- Flag indicating whether `numEq0?` has been updated. -/
  numEq0Updated  : Bool := false
  deriving Inhabited

/--
Per-goal state of the ring solver.

The four arrays are indexed by the ids assigned by `Sym.Arith.classify?`: `rings[i]` is the
solver state for `Sym.Arith.State.rings[i]`, and likewise for `semirings`, `ncRings`, and
`ncSemirings`. The `Sym.Arith` arrays are shared by every goal of the run and only grow, while
a goal uses only some of the rings. To keep the two indexings aligned, an array here is padded
with empty states up to the id being written (see `State.modifyRing`), and reading an id beyond
the array returns the empty state. Rings a goal never used therefore cost at most an empty
entry, and `rings.size ≤ Sym.Arith.State.rings.size` always holds.
-/
structure State where
  /-- Solver state of the commutative rings, indexed by `Sym.Arith` ring id. -/
  rings : Array CommRingState := {}
  /- Mapping from expressions/terms to their ring ids. -/
  exprToRingId : PHashMap ExprPtr Nat := {}
  /-- Solver state of the commutative semirings, indexed by `Sym.Arith` semiring id. -/
  semirings : Array SemiringState := {}
  /-
  Mapping from expressions/terms to their semiring ids.
  If an expression is in this map, it is not in `exprToRingId`.
  -/
  exprToSemiringId : PHashMap ExprPtr Nat := {}
  /-- Solver state of the non-commutative rings, indexed by `Sym.Arith` id. -/
  ncRings : Array RingState := {}
  /- Mapping from expressions/terms to their (non-commutative) ring ids. -/
  exprToNCRingId : PHashMap ExprPtr Nat := {}
  /-- Solver state of the non-commutative semirings, indexed by `Sym.Arith` id. -/
  ncSemirings : Array SemiringState := {}
  /- Mapping from expressions/terms to their (non-commutative) semiring ids. -/
  exprToNCSemiringId : PHashMap ExprPtr Nat := {}
  steps := 0
  /-- `true` if solver has already reported max degree issue. -/
  reportedMaxDegreeIssue : Bool := false
  deriving Inhabited

builtin_initialize ringExt : SolverExtension State ← registerSolverExtension (return {})

def get' : GoalM State := do
  ringExt.getState

@[inline] def modify' (f : State → State) : GoalM Unit := do
  ringExt.modifyState f

/-- Applies `f` to `a[i]`, first padding `a` with empty states so that `i` is in range. -/
@[inline] private def padAndModify [Inhabited α] (a : Array α) (i : Nat) (f : α → α) : Array α :=
  (a.rightpad (i + 1) default).modify i f

/-- Solver state of the commutative ring `ringId`; empty if this goal has not used it yet. -/
def State.getRing (s : State) (ringId : Nat) : CommRingState :=
  s.rings.getD ringId {}

@[inline] def State.modifyRing (s : State) (ringId : Nat) (f : CommRingState → CommRingState) : State :=
  { s with rings := padAndModify s.rings ringId f }

/-- Solver state of the commutative semiring `semiringId`; empty if this goal has not used it yet. -/
def State.getSemiring (s : State) (semiringId : Nat) : SemiringState :=
  s.semirings.getD semiringId {}

@[inline] def State.modifySemiring (s : State) (semiringId : Nat) (f : SemiringState → SemiringState) : State :=
  { s with semirings := padAndModify s.semirings semiringId f }

/-- Solver state of the non-commutative ring `ringId`; empty if this goal has not used it yet. -/
def State.getNCRing (s : State) (ringId : Nat) : RingState :=
  s.ncRings.getD ringId {}

@[inline] def State.modifyNCRing (s : State) (ringId : Nat) (f : RingState → RingState) : State :=
  { s with ncRings := padAndModify s.ncRings ringId f }

/-- Solver state of the non-commutative semiring `semiringId`; empty if this goal has not used it yet. -/
def State.getNCSemiring (s : State) (semiringId : Nat) : SemiringState :=
  s.ncSemirings.getD semiringId {}

@[inline] def State.modifyNCSemiring (s : State) (semiringId : Nat) (f : SemiringState → SemiringState) : State :=
  { s with ncSemirings := padAndModify s.ncSemirings semiringId f }

/-- Access to the per-goal state of the current (commutative or not) ring. -/
class MonadRingState (m : Type → Type) where
  getRingState : m RingState
  modifyRingState : (RingState → RingState) → m Unit

export MonadRingState (getRingState modifyRingState)

@[always_inline]
instance (m n) [MonadLift m n] [MonadRingState m] : MonadRingState n where
  getRingState    := liftM (getRingState : m RingState)
  modifyRingState f := liftM (modifyRingState f : m Unit)

/-- Access to the per-goal state of the current commutative ring. -/
class MonadCommRingState (m : Type → Type) where
  getCommRingState : m CommRingState
  modifyCommRingState : (CommRingState → CommRingState) → m Unit

export MonadCommRingState (getCommRingState modifyCommRingState)

@[always_inline]
instance (m n) [MonadLift m n] [MonadCommRingState m] : MonadCommRingState n where
  getCommRingState      := liftM (getCommRingState : m CommRingState)
  modifyCommRingState f := liftM (modifyCommRingState f : m Unit)

@[always_inline]
instance (m) [Monad m] [MonadCommRingState m] : MonadRingState m where
  getRingState := return (← getCommRingState).toRingState
  modifyRingState f := modifyCommRingState fun s => { s with toRingState := f s.toRingState }

/-- Access to the per-goal state of the current (commutative or not) semiring. -/
class MonadSemiringState (m : Type → Type) where
  getSemiringState : m SemiringState
  modifySemiringState : (SemiringState → SemiringState) → m Unit

export MonadSemiringState (getSemiringState modifySemiringState)

@[always_inline]
instance (m n) [MonadLift m n] [MonadSemiringState m] : MonadSemiringState n where
  getSemiringState    := liftM (getSemiringState : m SemiringState)
  modifySemiringState f := liftM (modifySemiringState f : m Unit)

end Lean.Meta.Grind.Arith.CommRing
