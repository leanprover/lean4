import Std.Internal.Do
import Std.Tactic.Do

/-! Tests for `def` contracts. A `def` carrying `require`/`ensures` clauses elaborates to the
definition plus an `@[spec]`-tagged `f.spec` Hoare triple that `vcgen` proves automatically; a
`for … invariant` clause inside the body supplies the loop invariant it needs. New cases go here. -/

open Std.Internal.Do Lean.Order

set_option mvcgen.warning false

/-! ## An `ensures` contract with a `for … invariant` loop, proved with no manual steps -/

def findSmallest (s : Array Nat) : Id (Option Nat)
    ensures r => match r with
      | none     => s.size = 0
      | some min => s.size > 0 ∧ (∃ i, i < s.size ∧ s[i]! = min)
                                ∧ (∀ j, j < s.size → min ≤ s[j]!)
  := do
  if s.size = 0 then
    return none
  else
    let mut minIndex := 0
    for i in [1:s.size]
        invariant xs => minIndex < s.size ∧ s[minIndex]! ≤ s[0]! ∧
                        ∀ j, j ∈ xs.prefix → s[minIndex]! ≤ s[j]!
      do
      if s[i]! < s[minIndex]! then
        minIndex := i
    return some s[minIndex]!

-- The contract synthesizes an `@[spec]`-tagged `findSmallest.spec` Hoare triple.
#guard_msgs (drop info) in
#check @findSmallest.spec

/-! ## `require` + `ensures` -/

def clampLow (n lo : Nat) : Id Nat
    require lo ≤ n
    ensures r => r = n
  := do return n

#guard_msgs (drop info) in
#check @clampLow.spec

/-! ## A contract over a membership-proof binder (`for h : x in xs invariant …`) -/

def sumWithMem (xs : List Nat) : Id Nat
    ensures r => 0 ≤ r := do
  let mut acc := 0
  for h : x in xs invariant cur => 0 ≤ acc do
    acc := acc + x
  return acc

#guard_msgs (drop info) in
#check @sumWithMem.spec

-- The membership binder also works over a legacy `Range`.
def sumRangeMem (n : Nat) : Id Nat
    ensures r => 0 ≤ r := do
  let mut acc := 0
  for h : i in [0:n] invariant cur => 0 ≤ acc do
    acc := acc + i
  return acc

#guard_msgs (drop info) in
#check @sumRangeMem.spec

/-! ## Several `invariant` clauses are conjoined into the loop's invariant -/

def countAndDouble (xs : List Nat) : Id (Nat × Nat)
    ensures r => r.1 = xs.length ∧ r.2 = 2 * xs.length := do
  let mut n := 0
  let mut twice := 0
  for x in xs
      invariant cur => n = cur.prefix.length
      invariant cur => twice = 2 * cur.prefix.length
    do
    n := n + 1
    twice := twice + 2
  return (n, twice)

#guard_msgs (drop info) in
#check @countAndDouble.spec

-- Each clause binds its own cursor and may name the loop's mutable variables.
def sumSteps (xs : List Nat) : Id Nat
    ensures r => 0 ≤ r := do
  let mut acc := 0
  let mut steps := 0
  for h : x in xs
      invariant cur => 0 ≤ acc
      invariant seen => steps = seen.prefix.length
    do
    acc := acc + x
    steps := steps + 1
  return acc

#guard_msgs (drop info) in
#check @sumSteps.spec

/-! ## The contract telescope is transplanted faithfully to `f.spec`

`f.spec` re-binds the definition's telescope verbatim, applies `f` to exactly the explicit arguments,
and uses `⊤` for an omitted `require`. These cover implicit, instance, strict-implicit, and autobound
binders, and a contract written without a `: type` ascription. -/

def specImplicit {α : Type} [Inhabited α] (x : α) (n : Nat) : Id α
    require n > 0
    ensures r => r = x :=
  pure x

/-- info: @specImplicit.spec : ∀ {α : Type} [inst : Inhabited α] (x : α) (n : Nat), ⦃ n > 0 ⦄ specImplicit x n ⦃ fun r => r = x ⦄ -/
#guard_msgs in
#check @specImplicit.spec

def specAutobound (v : Vector Nat n) : Id Nat
    require n > 0
    ensures r => r = n :=
  pure v.size

/-- info: @specAutobound.spec : ∀ {n : Nat} (v : Vector Nat n), ⦃ n > 0 ⦄ specAutobound v ⦃ fun r => r = n ⦄ -/
#guard_msgs in
#check @specAutobound.spec

def specStrict ⦃α : Type⦄ [Inhabited α] (x : α) : Id α
    ensures r => r = x :=
  pure x

/-- info: specStrict.spec : ∀ ⦃α : Type⦄ [inst : Inhabited α] (x : α), ⦃ ⊤ ⦄ specStrict x ⦃ fun r => r = x ⦄ -/
#guard_msgs in
#check @specStrict.spec

def specNoType (x : Nat)
    require x > 0
    ensures r => r ≥ x :=
  (pure x : Id Nat)

/-- info: specNoType.spec : ∀ (x : Nat), ⦃ x > 0 ⦄ specNoType x ⦃ fun r => r ≥ x ⦄ -/
#guard_msgs in
#check @specNoType.spec
