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

/-! ## Residual verification conditions and `where finally | spec => …` sections -/

opaque Opq : Nat → Prop

axiom opq_ax (n : Nat) : Opq n

/--
error: unproved verification conditions for the contract of `residualNoSection`; discharge them in a `where finally | spec => ...` section of the definition
case vc1
n : Nat
⊢ Opq n
-/
#guard_msgs in
def residualNoSection (n : Nat) : Id Nat
    ensures r => Opq r
  := pure n

def residualWithSection (n : Nat) : Id Nat
    ensures r => Opq r
  := pure n
where finally
  | spec => exact opq_ax _

/-- info: residualWithSection.spec : ∀ (n : Nat), ⦃ ⊤ ⦄ residualWithSection n ⦃ fun r => Opq r ⦄ -/
#guard_msgs in
#check @residualWithSection.spec

/-! A verification condition mentioning the loop state: `next` names the state and the invariant,
which the witness and its proof are built from. -/

opaque Certified : Nat → Prop

axiom certify (n : Nat) : 0 ≤ n → Certified n

def sumCertified (xs : List Nat) : Id Nat
    ensures r => ∃ k, r = k ∧ Certified k
  := do
  let mut acc := 0
  for x in xs invariant _cur => 0 ≤ acc do
    acc := acc + x
  return acc
where finally
  | spec => next acc h => exact ⟨acc, rfl, certify acc h⟩

/--
info: sumCertified.spec : ∀ (xs : List Nat), ⦃ ⊤ ⦄ sumCertified xs ⦃ fun r => ∃ k, r = k ∧ Certified k ⦄
-/
#guard_msgs in
#check @sumCertified.spec

/-! The section's steps run per verification condition: both branch VCs use the same steps, and
steps sequence across lines. -/

def residualTwoVCs (b : Bool) (n : Nat) : Id Nat
    ensures r => Opq r
  := if b then pure n else pure (n + 1)
where finally
  | spec =>
    skip
    exact opq_ax _

/--
info: residualTwoVCs.spec : ∀ (b : Bool) (n : Nat), ⦃ ⊤ ⦄ residualTwoVCs b n ⦃ fun r => Opq r ⦄
-/
#guard_msgs in
#check @residualTwoVCs.spec

/-! A hole in the body is filled by the unnamed `finally` block while the `spec` section
discharges the contract. -/

def residualWithHole (n : Nat) : Id Nat
    ensures r => Opq r
  := pure ?x
where finally
  exact n
  | spec => exact opq_ax _

/-- info: residualWithHole.spec : ∀ (n : Nat), ⦃ ⊤ ⦄ residualWithHole n ⦃ fun r => Opq r ⦄ -/
#guard_msgs in
#check @residualWithHole.spec

/-- error: duplicate `spec` section -/
#guard_msgs in
def residualDupSection (n : Nat) : Id Nat
    ensures r => Opq r
  := pure n
where finally
  | spec => exact opq_ax _
  | spec => finish

/-! All verification conditions left open are reported in one aggregate error. -/

/--
error: unproved verification conditions for the contract of `residualNoSectionTwoVCs`; discharge them in a `where finally | spec => ...` section of the definition
case vc1
b : Bool
n : Nat
h✝ : b = true
⊢ Opq n

case vc2
b : Bool
n : Nat
h✝ : ¬b = true
⊢ Opq (n + 1)
-/
#guard_msgs in
def residualNoSectionTwoVCs (b : Bool) (n : Nat) : Id Nat
    ensures r => Opq r
  := if b then pure n else pure (n + 1)

/-! A verification condition the section leaves open reports itself. -/

opaque Opq2 : Nat → Prop

/--
error: unproved verification conditions for the contract of `residualSectionMiss`; the `where finally | spec => ...` section does not discharge them
case vc1
n : Nat
⊢ Opq2 n
-/
#guard_msgs in
def residualSectionMiss (n : Nat) : Id Nat
    ensures r => Opq2 r
  := pure n
where finally
  | spec => skip

/-! A section step failing on a verification condition leaves it to the aggregate report. -/

/--
error: unproved verification conditions for the contract of `residualSectionStepFails`; the `where finally | spec => ...` section does not discharge them
case vc1
n : Nat
⊢ Opq2 n
-/
#guard_msgs in
def residualSectionStepFails (n : Nat) : Id Nat
    ensures r => Opq2 r
  := pure n
where finally
  | spec => lia

/--
error: Type mismatch
  opq_ax 0
has type
  Opq 0
but is expected to have type
  Opq2 n
-/
#guard_msgs in
def residualSectionIllTyped (n : Nat) : Id Nat
    ensures r => Opq2 r
  := pure n
where finally
  | spec => exact opq_ax 0
