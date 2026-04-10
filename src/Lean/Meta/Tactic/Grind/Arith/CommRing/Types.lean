/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSemiringAdapter
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Sym.Arith.Poly
public section

namespace Lean.Meta.Grind.Arith.CommRing
export Lean.Grind.CommRing (Var Power Mon Poly)
abbrev RingExpr := Grind.CommRing.Expr
/-
**Note**: recall that we use ring expressions to represent semiring expressions,
and ignore non-applicable constructors.
-/
abbrev SemiringExpr := Grind.CommRing.Expr

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

/-- Shared state for non-commutative and commutative semirings. -/
structure Semiring where
  id             : Nat
  type           : Expr
  /-- Cached `getDecLevel type` -/
  u              : Level
  /-- `Semiring` instance for `type` -/
  semiringInst   : Expr
  addFn?         : Option Expr := none
  mulFn?         : Option Expr := none
  powFn?         : Option Expr := none
  natCastFn?     : Option Expr := none
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

/-- Shared state for non-commutative and commutative rings. -/
structure Ring where
  id             : Nat
  type           : Expr
  /-- Cached `getDecLevel type` -/
  u              : Level
  /-- `Ring` instance for `type` -/
  ringInst       : Expr
  /-- `Semiring` instance for `type` -/
  semiringInst   : Expr
  /-- `IsCharP` instance for `type` if available. -/
  charInst?      : Option (Expr × Nat)
  addFn?         : Option Expr := none
  mulFn?         : Option Expr := none
  subFn?         : Option Expr := none
  negFn?         : Option Expr := none
  powFn?         : Option Expr := none
  intCastFn?     : Option Expr := none
  natCastFn?     : Option Expr := none
  one?           : Option Expr := none
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

/-- State for each `CommRing` processed by this module. -/
structure CommRing extends Ring where
  /-- Inverse if `fieldInst?` is `some inst` -/
  invFn?         : Option Expr := none
  /--
  If this is a `OfSemiring.Q α` ring, this field contain the
  `semiringId` for `α`.
  -/
  semiringId?    : Option Nat
  /-- `CommSemiring` instance for `type` -/
  commSemiringInst   : Expr
  /-- `CommRing` instance for `type` -/
  commRingInst   : Expr
  /-- `NoNatZeroDivisors` instance for `type` if available. -/
  noZeroDivInst? : Option Expr
  /-- `Field` instance for `type` if available. -/
  fieldInst?     : Option Expr
  /-- `PowIdentity` instance, the synthesized `CommSemiring` instance, and exponent `p` if available. -/
  powIdentityInst? : Option (Expr × Expr × Nat) := none
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
State for each `CommSemiring` processed by this module.
Recall that `CommSemiring` are processed using the envelop `OfCommSemiring.Q`
-/
structure CommSemiring extends Semiring where
  /-- Id for `OfCommSemiring.Q` -/
  ringId         : Nat
  /-- `CommSemiring` instance for `type` -/
  commSemiringInst   : Expr
  /-- `AddRightCancel` instance for `type` if available. -/
  addRightCancelInst? : Option (Option Expr) := none
  toQFn?         : Option Expr := none
  deriving Inhabited

/-- State for all `CommRing` types detected by `grind`. -/
structure State where
  /--
  Commutative rings.
  We expect to find a small number of rings in a given goal. Thus, using `Array` is fine here.
  -/
  rings : Array CommRing := {}
  /--
  Mapping from types to its "ring id". We cache failures using `none`.
  `typeIdOf[type]` is `some id`, then `id < rings.size`. -/
  typeIdOf : PHashMap ExprPtr (Option Nat) := {}
  /- Mapping from expressions/terms to their ring ids. -/
  exprToRingId : PHashMap ExprPtr Nat := {}
  /-- Commutative semirings. We support them using the envelope `OfCommRing.Q` -/
  semirings : Array CommSemiring := {}
  /--
  Mapping from types to its "semiring id". We cache failures using `none`.
  `stypeIdOf[type]` is `some id`, then `id < semirings.size`.
  If a type is in this map, it is not in `typeIdOf`.
  -/
  stypeIdOf : PHashMap ExprPtr (Option Nat) := {}
  /-
  Mapping from expressions/terms to their semiring ids.
  If an expression is in this map, it is not in `exprToRingId`.
  -/
  exprToSemiringId : PHashMap ExprPtr Nat := {}
  /--
  Non commutative rings.
  -/
  ncRings : Array Ring := {}
  /- Mapping from expressions/terms to their (non-commutative) ring ids. -/
  exprToNCRingId : PHashMap ExprPtr Nat := {}
  /--
  Mapping from types to its "ring id". We cache failures using `none`.
  `nctypeIdOf[type]` is `some id`, then `id < ncRings.size`. -/
  nctypeIdOf : PHashMap ExprPtr (Option Nat) := {}
  /--
  Non commutative semirings.
  -/
  ncSemirings : Array Semiring := {}
  /- Mapping from expressions/terms to their (non-commutative) semiring ids. -/
  exprToNCSemiringId : PHashMap ExprPtr Nat := {}
  /--
  Mapping from types to its "semiring id". We cache failures using `none`.
  `ncstypeIdOf[type]` is `some id`, then `id < ncSemirings.size`. -/
  ncstypeIdOf : PHashMap ExprPtr (Option Nat) := {}
  steps := 0
  deriving Inhabited

builtin_initialize ringExt : SolverExtension State ← registerSolverExtension (return {})

def get' : GoalM State := do
  ringExt.getState

@[inline] def modify' (f : State → State) : GoalM Unit := do
  ringExt.modifyState f

end Lean.Meta.Grind.Arith.CommRing
