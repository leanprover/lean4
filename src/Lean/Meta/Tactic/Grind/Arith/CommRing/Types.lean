/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.PersistentArray
import Lean.Data.RBTree
import Lean.Meta.Tactic.Grind.ENodeKey
import Lean.Meta.Tactic.Grind.Arith.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly

namespace Lean.Meta.Grind.Arith.CommRing
export Lean.Grind.CommRing (Var Power Mon Poly)
abbrev RingExpr := Grind.CommRing.Expr

deriving instance Repr for Power, Mon, Poly

mutual

structure EqCnstr where
  p     : Poly
  h     : EqCnstrProof
  sugar : Nat
  id    : Nat

inductive EqCnstrProof where
  | core (a b : Expr) (ra rb : RingExpr)
  | superpose (k₁ : Int) (m₁ : Mon) (c₁ : EqCnstr) (k₂ : Int) (m₂ : Mon) (c₂ : EqCnstr)
  | simp (k₁ : Int) (c₁ : EqCnstr) (k₂ : Int) (m₂ : Mon) (c₂ : EqCnstr)
  | mul (k : Int) (e : EqCnstr)
  | div (k : Int) (e : EqCnstr)

end

instance : Inhabited EqCnstrProof where
  default := .core default default default default

instance : Inhabited EqCnstr where
  default := { p := default, h := default, sugar := 0, id := 0 }

protected def EqCnstr.compare (c₁ c₂ : EqCnstr) : Ordering :=
  (compare c₁.sugar c₂.sugar) |>.then
  (compare c₁.p.degree c₂.p.degree) |>.then
  (compare c₁.id c₂.id)

abbrev Queue : Type := RBTree EqCnstr EqCnstr.compare

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

def PolyDerivation.p : PolyDerivation → Poly
  | .input p   => p
  | .step p .. => p

/-- A disequality `lhs ≠ rhs` asserted by the core. -/
structure DiseqCnstr where
  lhs : Expr
  rhs : Expr
  /-- Reified `lhs` -/
  rlhs : RingExpr
  /-- Reified `rhs` -/
  rrhs : RingExpr
  /-- `lhs - rhs` simplication chain. If it becomes `0` we have an inconsistency. -/
  d : PolyDerivation

/-- State for each `CommRing` processed by this module. -/
structure Ring where
  id             : Nat
  type           : Expr
  /-- Cached `getDecLevel type` -/
  u              : Level
  /-- `CommRing` instance for `type` -/
  commRingInst   : Expr
  /-- `IsCharP` instance for `type` if available. -/
  charInst?      : Option (Expr × Nat) := .none
  /-- `NoNatZeroDivisors` instance for `type` if available. -/
  noZeroDivInst? : Option Expr := .none
  addFn          : Expr
  mulFn          : Expr
  subFn          : Expr
  negFn          : Expr
  powFn          : Expr
  intCastFn      : Expr
  natCastFn      : Expr
  /--
  Mapping from variables to their denotations.
  Remark each variable can be in only one ring.
  -/
  vars           : PArray Expr := {}
  /-- Mapping from `Expr` to a variable representing it. -/
  varMap         : PHashMap ENodeKey Var := {}
  /-- Mapping from Lean expressions to their representations as `RingExpr` -/
  denote         : PHashMap ENodeKey RingExpr := {}
  /-- Next unique id for `EqCnstr`s. -/
  nextId         : Nat := 0
  /-- Number of "steps": simplification and superposition. -/
  steps          : Nat := 0
  /-- Equations to process. -/
  queue          : Queue := {}
  /--
  Mapping from variables `x` to equations such that the smallest variable
  in the leading monomial is `x`.
  -/
  varToBasis     : PArray (List EqCnstr) := {}
  /-- Disequalities. -/
  -- TODO: add indexing
  diseqs         : PArray DiseqCnstr := {}
  /--
  If `recheck` is `true`, then new equalities have been added to the basis since we checked
  disequalities and implied equalities.
  -/
  recheck        : Bool := false
  deriving Inhabited

/-- State for all `CommRing` types detected by `grind`. -/
structure State where
  /--
  Commutative rings.
  We expect to find a small number of rings in a given goal. Thus, using `Array` is fine here.
  -/
  rings : Array Ring := {}
  /--
  Mapping from types to its "ring id". We cache failures using `none`.
  `typeIdOf[type]` is `some id`, then `id < rings.size`. -/
  typeIdOf : PHashMap ENodeKey (Option Nat) := {}
  /- Mapping from expressions/terms to their ring ids. -/
  exprToRingId : PHashMap ENodeKey Nat := {}
  steps := 0
  deriving Inhabited

end Lean.Meta.Grind.Arith.CommRing
