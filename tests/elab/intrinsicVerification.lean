import Std.Internal.Do
import Std.Tactic.Do

/-! Tests for `def` contracts. A `def` carrying `require`/`ensures` clauses elaborates to the
definition plus an `@[spec]`-tagged `f.spec` Hoare triple that `vcgen` proves automatically; a
`for … invariant` or `while … invariant` clause inside the body supplies the loop invariant it
needs. New cases go here. -/

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

/-! ## A `while … invariant … decreasing` loop, proved with no manual steps

The invariant holds before every test of the loop condition. What holds after the loop is the
invariant together with the negated condition, which is how `i = n` becomes available below. -/

def countUp (n : Nat) : Id Nat
    ensures r => r = n
  := do
  let mut i := 0
  while i < n invariant i ≤ n decreasing n - i do
    i := i + 1
  return i

#guard_msgs (drop info) in
#check @countUp.spec

def differenceMinMax (a : Array Int) : Id Int
    require a.size ≠ 0
    ensures r => 0 ≤ r
  := do
  let mut mn := a[0]!
  let mut mx := a[0]!
  let mut i := 1
  while i < a.size invariant mn ≤ mx decreasing a.size - i do
    if a[i]! < mn then mn := a[i]!
    if a[i]! > mx then mx := a[i]!
    i := i + 1
  return mx - mn

#guard_msgs (drop info) in
#check @differenceMinMax.spec

-- The annotation is erased at runtime, and the loop elaborates outside `Id` as well.
def sumUpTo (n : Nat) : StateM Nat Unit := do
  let mut i := 0
  while i < n invariant i ≤ n decreasing n - i do
    modify (· + i)
    i := i + 1

#guard ((sumUpTo 5).run 0).2 = 10
#guard Id.run (differenceMinMax #[3, 1, 4, 1, 5]) = 4

/-- error: A `while` loop's `invariant` clause needs a termination measure. Append `decreasing e`, where `e : Nat` strictly decreases on every iteration. -/
#guard_msgs in
example (n : Nat) : Id Nat := do
  let mut i := 0
  while i < n invariant i ≤ n do
    i := i + 1
  return i

/--
error: The assertion that holds after a `while` loop with an `invariant` clause is the invariant together with the negated loop condition, so control has to leave the loop through a failing condition. Restructure the body to leave through the loop condition, or drop the `invariant` clause.
-/
#guard_msgs in
example (n : Nat) : Id Nat := do
  let mut i := 0
  while i < n invariant i ≤ n decreasing n - i do
    if i = 3 then break
    i := i + 1
  return i

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
