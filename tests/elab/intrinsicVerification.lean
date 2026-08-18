import Std.WP
import Std.Data.HashMap

/-! Tests for `def` contracts. A `def` carrying `requires`/`ensures` clauses elaborates to the
definition plus an `@[spec]`-tagged `f.spec` Hoare triple that `vcgen` proves automatically; a
`for … invariant` clause inside the body supplies the loop invariant it needs. New cases go here. -/

set_option mvcgen.warning false

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

open Std.WP Lean.Order

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

/-! ## A loop over an iterator, and over the iterators a combinator builds

An iterator is a container like any other: it has a `PureForIn` instance, and a combinator returns
an iterator, so one instance covers `map` and `filter` too. -/

def sumIter (xs : List Nat) : Id Nat
    ensures r => r = xs.sum := do
  let mut s := 0
  for x in xs.iter invariant pref _suff => s = pref.sum do
    s := s + x
  return s

#guard_msgs (drop info) in
#check @sumIter.spec

def sumIterMap (xs : List Nat) : Id Nat
    ensures r => 0 ≤ r := do
  let mut s := 0
  for x in xs.iter.map (· + 1) invariant _pref _suff => 0 ≤ s do
    s := s + x
  return s

#guard_msgs (drop info) in
#check @sumIterMap.spec

def sumIterFilter (xs : List Nat) : Id Nat
    ensures r => 0 ≤ r := do
  let mut s := 0
  for x in xs.iter.filter (· > 2) invariant _pref _suff => 0 ≤ s do
    s := s + x
  return s

#guard_msgs (drop info) in
#check @sumIterFilter.spec

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

/-! ## A `repeat` or `while` loop binds whether it has left

The clause's first binder is a `Bool`: `true` once the loop is done, `false` while it iterates. The
`decreasing` clause gives the termination measure, a term over the loop's mutable variables. -/

def countDown (n : Nat) : Id Nat
    ensures r => r = 0 := do
  let mut i := n
  while i > 0
      invariant exit => if exit then i = 0 else True
      decreasing i
    do
    i := i - 1
  return i

#guard_msgs (drop info) in
#check @countDown.spec

/-! Binders past the first bind the arguments of the assertion itself, such as the state of a state
monad. -/

def countIntoState (n : Nat) : StateM Nat Unit
    requires s => s = 0
    ensures _ s => s = n := do
  let mut i := 0
  while i < n
      invariant exit s => s = i ∧ if exit then i = n else i ≤ n
      decreasing n - i
    do
    modify (· + 1)
    i := i + 1
where finally
  | spec => all_goals grind

#guard_msgs (drop info) in
#check @countIntoState.spec

/-! A wildcard binder states one assertion for both cases. A clause left out is a
condition like any other: the omitted measure is named `inv1` and discharged in the `spec` section,
which then proves the step that mentions it. -/

def countUp (n : Nat) : Id Nat
    ensures r => r ≤ n := do
  let mut i := 0
  repeat
      invariant _ => i ≤ n
    do
    if i = n then break
    i := i + 1
  return i
where finally
  | spec =>
    case inv1 => exact .ofMeasure fun i => n - i
    all_goals grind

#guard_msgs (drop info) in
#check @countUp.spec

/-! A loop may state its measure alone. The invariant is then the hole, named `inv1` like the
measure omitted by `countUp`, and it states an assertion of the monad the loop runs in. -/

def countMeasureOnly (n : Nat) : StateM Nat Unit
    requires s => s = 0
    ensures _ s => s = n := do
  let mut i := 0
  while i < n
      decreasing n - i
    do
    modify (· + 1)
    i := i + 1
where finally
  | spec =>
    case inv1 =>
      exact fun c s => match c with
        | .inl i => s = i ∧ i ≤ n
        | .inr i => s = i ∧ i = n
    all_goals grind

#guard_msgs (drop info) in
#check @countMeasureOnly.spec

/-! The measure is the hole when the loop states only its invariant, in any monad. -/

def countInvariantOnly (n : Nat) : StateM Nat Unit
    requires s => s = 0
    ensures _ s => s = 0 := do
  let mut i := 0
  while i < n
      invariant _ s => s = 0
    do
    i := i + 1
where finally
  | spec =>
    case inv1 => exact .ofMeasure fun i => n - i
    all_goals grind

#guard_msgs (drop info) in
#check @countInvariantOnly.spec

/-! The measure may read the state of a state monad, and its binders are the arguments the
assertions take. Binding more than that is reported at the clause. -/

def drain (n : Nat) : StateM Nat Unit
    requires s => s ≤ n
    ensures _ s => s = n := do
  repeat
      invariant exit s => s ≤ n ∧ (exit → s = n)
      decreasing s => n - s
    do
    let s ← get
    if s = n then break
    set (s + 1)
where finally
  | spec => all_goals grind

#guard_msgs (drop info) in
#check @drain.spec

/--
error: The measure of a loop in this monad takes one argument, and this clause has 2 binders. The loop's mutable variables are named without binding them.
-/
#guard_msgs in
example (n : Nat) : StateM Nat Unit := do
  let mut go := true
  while go
      invariant _ s => s ≤ n
      decreasing _ s => n - s
    do
    set n
    go := false

/-! A `repeat … until` loop takes the same clauses. -/

def countUntil (n : Nat) : Id Nat
    ensures r => r ≤ n := do
  let mut i := 0
  repeat
      invariant _ => i ≤ n
      decreasing n - i
    do
    if i < n then i := i + 1
  until i = n
  return i

#guard_msgs (drop info) in
#check @countUntil.spec

/-! A loop that returns early carries the returned value in a slot of the state tuple that the
invariant skips over, so a `repeat` with a `return` in its body takes the clauses like any other.
The invariant cannot name that slot, so what the loop returns is beyond what it can state. -/

def firstZero (xs : Array Nat) : Id (Option Nat)
    ensures _ => True := do
  let mut i := 0
  repeat
      invariant _ => i ≤ xs.size
      decreasing xs.size - i
    do
    if h : i < xs.size then
      if xs[i] = 0 then return some i
      i := i + 1
    else
      break
  return none

#guard_msgs (drop info) in
#check @firstZero.spec

/-! A `for` loop over a collection ends with the collection. -/

/--
error: A `for` loop terminates with the collection it iterates; `decreasing` states the termination measure of a `repeat` or `while` loop.
-/
#guard_msgs in
example (xs : List Nat) : Id Unit := do
  for _ in xs invariant _ _ => True decreasing xs.length do pure ()

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

/-! ## A `while` loop whose contract asks for a witness

The invariant relates `mn`, `mx` and `i` at every iteration, and its `exit` binder states what the
loop reaches once it leaves: `i = a.size`, so the bounds the invariant records for the prefix `[0, i)`
cover the whole array. The postcondition claims a minimum and a maximum exist, and the `spec` section
names the two the exit state holds. -/

@[local grind] def InArray (a : Array Int) (v : Int) : Prop :=
  ∃ i : Nat, i < a.size ∧ a[i]! = v

@[local grind] def IsMinOfArray (a : Array Int) (mn : Int) : Prop :=
  InArray a mn ∧ ∀ i : Nat, i < a.size → mn ≤ a[i]!

@[local grind] def IsMaxOfArray (a : Array Int) (mx : Int) : Prop :=
  InArray a mx ∧ ∀ i : Nat, i < a.size → a[i]! ≤ mx

def differenceMinMax (a : Array Int) : Id Int
    requires a.size ≠ 0
    ensures r => ∃ mn mx, IsMinOfArray a mn ∧ IsMaxOfArray a mx ∧ r = mx - mn
  := do
  let mut mn := a[0]!
  let mut mx := a[0]!
  let mut i : Nat := 1
  while i < a.size
      invariant exit => 1 ≤ i ∧ i ≤ a.size ∧ (exit → i = a.size) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
      decreasing a.size - i
    do
    let v := a[i]!
    if v < mn then mn := v
    if v > mx then mx := v
    i := i + 1
  return mx - mn
where finally
  | spec => case vc2 st _ => exact ⟨st.1, st.2.1, by grind, by grind, by grind⟩

#guard_msgs (drop info) in
#check @differenceMinMax.spec

/-! ## A loop nested in a loop

The inner loop's invariant names `i`, the index the outer loop stands at, by ordinary lexical
scoping: the clause elaborates in the body of the outer loop, where `i` is in scope alongside the
inner loop's own mutable variable `count`. -/

@[local grind] def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

@[local grind] def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x

@[local grind →] theorem mem_getElem! (lst : List Int) (w : Int) (hw : w ∈ lst) :
    ∃ k, k < lst.length ∧ lst[k]! = w := by
  obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hw
  exact ⟨k, hk, by rw [getElem!_pos lst k hk, hkv]⟩

def findMajorityElement (lst : List Int) : Id Int
    ensures r => (hasMajorityElement lst → r ∈ lst ∧ isMajorityElement lst r) ∧
                 (¬hasMajorityElement lst → r = -1)
  := do
  let n := lst.length
  let threshold := n / 2
  let mut found := false
  let mut candidate : Int := -1
  for i in [0:n]
      invariant pref _suff =>
        (found = true → candidate ∈ lst ∧ isMajorityElement lst candidate) ∧
        (found = false → ∀ k : Nat, k < pref.length → ¬isMajorityElement lst lst[k]!)
    do
    let elem := lst[i]!
    let mut count := 0
    for j in [0:n]
        invariant inner _suff => count = (lst.take inner.length).count lst[i]!
      do
      if lst[j]! = elem then
        count := count + 1
    if count > threshold then
      found := true
      candidate := elem
  if found then
    return candidate
  else
    return -1
where finally
  | spec => all_goals grind [List.take_length, List.take_succ_eq_append_getElem]

#guard_msgs (drop info) in
#check @findMajorityElement.spec
