import Std.Internal.Do
import Std.Data.HashMap

/-! Tests for `def` contracts. A `def` carrying `requires`/`ensures` clauses elaborates to the
definition plus an `@[spec]`-tagged `f.spec` Hoare triple that `vcgen` proves automatically; a
`for … invariant` clause inside the body supplies the loop invariant it needs. New cases go here. -/

set_option mvcgen.warning false
set_option experimental.intrinsic true

/-! ## Contracts elaborate with nothing opened

The cases up to the `open` below see neither namespace, so they pin what the spec theorem must
activate by itself. A clause left out defaults to `⊤`, which prints as the constant it denotes
while its notation is out of scope. -/

def clampLow (n lo : Nat) : Id Nat
    requires lo ≤ n
    ensures r => r = n
  := pure n

/-- info: clampLow.spec : ∀ (n lo : Nat), ⦃ lo ≤ n ⦄ clampLow n lo ⦃ fun r => r = n ⦄ -/
#guard_msgs in
#check @clampLow.spec

def onlyEnsures (n : Nat) : Id Nat
    ensures r => r = n
  := pure n

/-- info: onlyEnsures.spec : ∀ (n : Nat), ⦃ Lean.Order.top ⦄ onlyEnsures n ⦃ fun r => r = n ⦄ -/
#guard_msgs in
#check @onlyEnsures.spec

def onlyRequire (n : Nat) : Id Nat
    requires 0 ≤ n
  := pure n

/-- info: onlyRequire.spec : ∀ (n : Nat), ⦃ 0 ≤ n ⦄ onlyRequire n ⦃ fun x => Lean.Order.top ⦄ -/
#guard_msgs in
#check @onlyRequire.spec

open Std.Internal.Do Lean.Order

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
        invariant pref _ => minIndex < s.size ∧ s[minIndex]! ≤ s[0]! ∧
                            ∀ j, j ∈ pref → s[minIndex]! ≤ s[j]!
      do
      if s[i]! < s[minIndex]! then
        minIndex := i
    return some s[minIndex]!

-- The contract synthesizes an `@[spec]`-tagged `findSmallest.spec` Hoare triple.
#guard_msgs (drop info) in
#check @findSmallest.spec

/-! ## An invariant over the monad's own state

The invariant need not mention a mutable variable: here it constrains the `StateM` state. -/

def sumIntoState (xs : List Nat) : StateM Nat Unit
    requires s => s = 0
    ensures _ s => s = xs.sum
  := do
  for x in xs invariant pref _ s => s = pref.sum do
    modify (· + x)

#guard_msgs (drop info) in
#check @sumIntoState.spec

/-! ## `assert` states a property at a point in the program

The bare form asserts a term; the binder form binds the assertion's own arguments, such as the
state of a state monad. -/

def assertDouble (n : Nat) : Id Nat
    requires n > 0
    ensures r => r ≥ 2
  := do
  let d := 2 * n
  assert d ≥ 2
  return d

#guard_msgs (drop info) in
#check @assertDouble.spec

def assertIntoState (xs : List Nat) : StateM Nat Unit
    requires s => s = 0
    ensures _ s => s = xs.sum
  := do
  assert s => s = 0
  for x in xs invariant pref _ s => s = pref.sum do
    modify (· + x)

#guard_msgs (drop info) in
#check @assertIntoState.spec

/-! The binders accept a type ascription, as in `fun`. -/

def assertAscribed (xs : List Nat) : StateM Nat Unit
    requires s => s = 0
    ensures _ s => s = xs.sum
  := do
  assert s : Nat => s = 0
  for x in xs invariant pref _ s => s = pref.sum do
    modify (· + x)

#guard_msgs (drop info) in
#check @assertAscribed.spec

/-! An assertion that does not follow is reported like any other undischarged condition. -/

/--
error: unproved verification conditions for the contract of `assertUnprovable`; discharge them in a `where finally | spec => ...` section of the definition
case vc1
n : Nat
⊢ 0 < n
-/
#guard_msgs in
def assertUnprovable (n : Nat) : Id Nat
    ensures r => r = n
  := do
  assert n > 0
  return n

/-! `assert!` keeps its runtime meaning: it tests a `Bool` and panics, with no gadget involved. -/

def runtimeAssert (n : Nat) : Id Nat := do
  assert! n > 0
  return n

/-- info: 3 -/
#guard_msgs in
#eval runtimeAssert 3

/-! ## The `invariant` clause needs at least two binders -/

/--
error: The `invariant` clause takes at least two binders: the elements consumed so far and the elements remaining.
-/
#guard_msgs in
example (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs invariant _pref => 0 ≤ acc do
    acc := acc + x
  return acc

/-! ## A loop over an `Array`, with and without a membership-proof binder

The membership binder (`for h : x in xs`) is covered here rather than per container. -/

def sumArray (xs : Array Nat) : Id Nat
    ensures r => r = xs.toList.sum := do
  let mut acc := 0
  for x in xs invariant pref _ => acc = pref.sum do
    acc := acc + x
  return acc

#guard_msgs (drop info) in
#check @sumArray.spec

def sumArrayMem (xs : Array Nat) : Id Nat
    ensures r => r = xs.toList.sum := do
  let mut acc := 0
  for h : x in xs invariant pref _ => acc = pref.sum do
    acc := acc + x
  return acc

#guard_msgs (drop info) in
#check @sumArrayMem.spec

/-! ## A loop over a `HashMap`, through its `PureForIn` instance

The container needs no specification of its own: stating that its loop is effect-free is enough
for the `invariant` clause to work, and the binder may destructure. -/

def sumValues (m : Std.HashMap Nat Nat) : Id Nat
    ensures r => 0 ≤ r := do
  let mut s := 0
  for (_k, v) in m invariant _pref _suff => 0 ≤ s do
    s := s + v
  return s

#guard_msgs (drop info) in
#check @sumValues.spec

/-! A loop over several collections takes no invariant. -/

/-- error: The `invariant` clause takes a `for` loop over a single collection. -/
#guard_msgs in
example (xs ys : List Nat) : Id Unit := do
  for _ in xs, _ in ys invariant _ _ => True do pure ()

/-! A container whose loop is not effect-free is reported at the clause. -/

/--
error: failed to synthesize instance of type class
  Std.Internal.PureForIn Id String Char
The `invariant` clause is stated over this class, which says that iterating the container produces its elements without effects.

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (s : String) : Id Unit := do
  for _c in s invariant _ _ => True do pure ()

/-! ## The `invariant` clause ascribes types per binder

An ascription after the binder list would cover the loop binders and the assertion binders alike. -/

/--
error: The `invariant` clause takes no type ascription covering all its binders; ascribe the type on an individual binder, as in `invariant (pref : List α) suff => ...`.
-/
#guard_msgs in
example (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs invariant pref suff : List Nat => 0 ≤ acc do
    acc := acc + x
  return acc

/-! ## The clause binders accept a type ascription, as in `fun` -/

def requiresAscribed (xs : List Nat) : StateM Nat Unit
    requires s : Nat => s = 0
    ensures _ s => s = xs.sum
  := do
  for x in xs invariant pref _ s => s = pref.sum do
    modify (· + x)

#guard_msgs (drop info) in
#check @requiresAscribed.spec

def ensuresAscribed (n : Nat) : Id Nat
    ensures r : Nat => r ≥ n
  := pure n

/-- info: ensuresAscribed.spec : ∀ (n : Nat), ⦃ ⊤ ⦄ ensuresAscribed n ⦃ fun r => r ≥ n ⦄ -/
#guard_msgs in
#check @ensuresAscribed.spec

/-! ## An `ensures` clause written with match alternatives

The clause is a `fun`, so it may state the postcondition per shape of the result. -/

def halve (n : Nat) : Id (Option Nat)
    ensures
      | none => False
      | some v => 2 * v ≤ n
  := pure (some (n / 2))

#guard_msgs (drop info) in
#check @halve.spec

/-! ## The contract telescope is transplanted faithfully to `f.spec`

`f.spec` re-binds the definition's telescope verbatim, applies `f` to exactly the explicit arguments,
and uses `⊤` for an omitted `requires`. These cover implicit, instance, strict-implicit, and autobound
binders, and a contract written without a `: type` ascription. -/

def specImplicit {α : Type} [Inhabited α] (x : α) (n : Nat) : Id α
    requires n > 0
    ensures r => r = x :=
  pure x

/-- info: @specImplicit.spec : ∀ {α : Type} [inst : Inhabited α] (x : α) (n : Nat), ⦃ n > 0 ⦄ specImplicit x n ⦃ fun r => r = x ⦄ -/
#guard_msgs in
#check @specImplicit.spec

def specAutobound (v : Vector Nat n) : Id Nat
    requires n > 0
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
    requires x > 0
    ensures r => r ≥ x :=
  (pure x : Id Nat)

/-- info: specNoType.spec : ∀ (x : Nat), ⦃ x > 0 ⦄ specNoType x ⦃ fun r => r ≥ x ⦄ -/
#guard_msgs in
#check @specNoType.spec

/-! ## Residual verification conditions and `where finally | spec => …` sections -/

opaque Opq : Nat → Prop

axiom opq_ax (n : Nat) : Opq n

/-! The case binders name a condition's inaccessible variables, here the loop's final state and its
invariant. The witness is the one `grind` will not invent. -/

def sumEvens (xs : List Nat) : Id Nat
    ensures r => ∃ k, r = 2 * k
  := do
  let mut acc := 0
  for x in xs invariant _pref _suff => acc % 2 = 0 do
    acc := acc + 2 * x
  return acc
where finally
  | spec => case vc1 acc h => exact ⟨acc / 2, by omega⟩

/-- info: sumEvens.spec : ∀ (xs : List Nat), ⦃ ⊤ ⦄ sumEvens xs ⦃ fun r => ∃ k, r = 2 * k ⦄ -/
#guard_msgs in
#check @sumEvens.spec

/-! The section is an ordinary tactic block over the conditions left open, so several of them are
addressed by their case names. -/

def residualTwoVCs (b : Bool) (n : Nat) : Id Nat
    ensures r => Opq r
  := if b then pure n else pure (n + 1)
where finally
  | spec =>
    case vc1 => exact opq_ax _
    case vc2 => exact opq_ax _

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
  | spec => skip

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

opaque Opq2 : Nat → Prop

/-! A tactic leaving a condition open reaches the report. -/

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

/-! A tactic that fails reports its own error. -/

/--
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
-/
#guard_msgs in
def residualSectionTacticFails (n : Nat) : Id Nat
    ensures r => Opq2 r
  := pure n
where finally
  | spec => omega

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
