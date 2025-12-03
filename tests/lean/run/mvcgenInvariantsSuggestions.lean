import Std.Tactic.Do
import Std

open Std Do

set_option grind.warning false
set_option mvcgen.warning false
set_option pp.rawOnError true
set_option warn.sorry false

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = 0 ∨ xs.suffix = [] ∧ letMuts = l.sum⌝
-/
#guard_msgs (info) in
theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

/--
info: Try this:
  [apply] mvcgen invariants?
---
info: Try this:
  [apply] mvcgen [mySum] invariants?
---
info: Try this:
  [apply] mvcgen +elimLets invariants?
---
info: Try this:
  [apply] mvcgen +elimLets [mySum] invariants?
-/
#guard_msgs (info) in
theorem mySum_suggest_invariant_short (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen?
  mvcgen? [mySum]
  mvcgen? +elimLets
  mvcgen? +elimLets [mySum]
  all_goals admit

def mySum2 (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  let mut acc2 := 0
  for x in l do
    acc := acc + x
    acc2 := acc2 + x
  return acc

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = ⟨0, 0⟩ ∨ xs.suffix = [] ∧ letMuts.fst = l.sum⌝
-/
#guard_msgs (info) in
theorem mySum2_suggest_invariant (l : List Nat) : mySum2 l = l.sum := by
  generalize h : mySum2 l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

def copy (l : List Nat) : Id (Array Nat) := do
  let mut acc := #[]
  for x in l do
    acc := acc.push x
  return acc

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = acc✝ ∨ xs.suffix = [] ∧ letMuts = l.toArray⌝
-/
#guard_msgs (info) in
theorem copy_suggest_invariant (l : List Nat) : ⦃⌜True⌝⦄ copy l ⦃⇓ r => ⌜r = l.toArray⌝⦄ := by
  mvcgen [copy] invariants?
  /-
  case inv1
  l : List Nat
  acc✝ : Array Nat := #[]
  ⊢ Invariant l (Array Nat) PostShape.pure
  ...
  -/
  all_goals admit

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturn (onReturn := fun r letMuts => ⌜l.Nodup ∧ (r = true ↔ l.Nodup)⌝) (onContinue :=
      fun xs letMuts => ⌜xs.prefix = [] ∧ letMuts = ∅ ∨ xs.suffix = [] ∧ l.Nodup⌝)
-/
#guard_msgs (info) in
theorem nodup_suggest_invariant (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

def nodup_twice (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  let mut seen2 : HashSet Int := ∅
  for x in l do
    if x ∈ seen2 then
      return false
    seen2 := seen2.insert x
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturn (onReturn := fun r letMuts =>
      spred(Prod.fst ?inv2 ({ «prefix» := [], suffix := l, property := ⋯ }, ⟨none, ∅⟩) ∧
          { down := r = true ↔ l.Nodup }))
      (onContinue := fun xs letMuts =>
      spred({ down := xs.prefix = [] ∧ letMuts = ∅ } ∨
          ⌜xs.suffix = []⌝ ∧
            Prod.fst ?inv2 ({ «prefix» := [], suffix := l, property := ⋯ }, ⟨none, ∅⟩) ∧ { down := True }))
  ·
    Invariant.withEarlyReturn (onReturn := fun r letMuts => ⌜l.Nodup ∧ (r = true ↔ l.Nodup)⌝) (onContinue :=
      fun xs letMuts => ⌜xs.prefix = [] ∧ letMuts = ∅ ∨ xs.suffix = [] ∧ l.Nodup⌝)
-/
#guard_msgs (info) in
theorem nodup_twice_suggest_invariant (l : List Int) : nodup_twice l ↔ l.Nodup := by
  generalize h : nodup_twice l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

structure Supply where
  counter : Nat

def mkFresh [Monad m] : StateT Supply m Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

abbrev AppM := StateT Bool (StateT Supply (StateM String))
abbrev liftCounterM : StateT Supply (StateM String) α → AppM α := liftM

def mkFreshN (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← liftCounterM mkFresh
    acc := acc.push n
  return acc.toList

-- In the following, we suggest an inaccessible variable `acc` in the invariant. Unfortunate.
/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = acc✝ ∨ xs.suffix = [] ∧ letMuts.toList.Nodup⌝
-/
#guard_msgs (info) in
theorem mkFreshN_suggest_invariant (n : Nat) : ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  mvcgen [mkFreshN, mkFresh, liftCounterM] invariants?
  all_goals admit

def mkFreshN_early_return (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← liftCounterM mkFresh
    if n > 13 then return acc.toList
    acc := acc.push n
  return acc.toList

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturn (onReturn := fun r letMuts => ⌜letMuts.toList.Nodup ∧ r.Nodup⌝) (onContinue :=
      fun xs letMuts => ⌜xs.prefix = [] ∧ letMuts = acc✝ ∨ xs.suffix = [] ∧ letMuts.toList.Nodup⌝)
-/
#guard_msgs (info) in
theorem mkFreshN_early_return_suggest_invariant (n : Nat) : ⦃⌜True⌝⦄ mkFreshN_early_return n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  mvcgen [mkFreshN_early_return, mkFresh, liftCounterM] invariants?
  all_goals admit

def earlyReturnWithoutLetMut (l : List Int) : Bool := Id.run do
  for x in l do
    if x < 0 then return true
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturn (onReturn := fun r letMuts => ⌜r = true⌝) (onContinue := fun xs letMuts =>
      ⌜xs.prefix = [] ∨ xs.suffix = []⌝)
-/
#guard_msgs (info) in
theorem earlyReturnWithoutLetMut_suggest_invariant (l : List Int) : earlyReturnWithoutLetMut l := by
  generalize h : earlyReturnWithoutLetMut l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

def notQuiteEarlyReturn (l : List Nat) : Option Nat := Id.run do
  -- The idea here is that the type of the state tuple *looks* like it's an early return, but `last`
  -- is not used as if it is an early return variable.
  let mut last : Option Nat := none
  let mut mdummy : Unit := () -- m* is important because let mut vars are sorted alphabetically
  for x in l do
    last := some x
    mdummy := ()
  return last

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = ⟨none, ()⟩ ∨ xs.suffix = [] ∧ letMuts.fst = l.getLast?⌝
-/
#guard_msgs (info) in
theorem notQuiteEarlyReturn_suggest_invariant (l : List Nat) : notQuiteEarlyReturn l = l.getLast? := by
  generalize h : notQuiteEarlyReturn l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

def polySum [Monad m] (l : List Nat) : m Nat := do
  let mut acc := 0
  let mut acc2 := 0
  for x in l do
    acc := acc + x
    acc2 := acc2 + x
  return acc

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = ⟨0, 0⟩ ∨ xs.suffix = [] ∧ letMuts.fst = l.sum⌝
-/
#guard_msgs (info) in
theorem polySum_suggest_invariant [Monad m] [WPMonad m ps] (l : List Nat) : ⦃⌜True⌝⦄ @polySum m _ l ⦃⇓ r => ⌜r = l.sum⌝⦄ := by
  mvcgen [polySum] invariants?
  all_goals admit

def polyNodup [Monad m] (l : List Int) : m Bool := do
  let mut seen : HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturn (onReturn := fun r letMuts => ⌜l.Nodup ∧ (r = true ↔ l.Nodup)⌝) (onContinue :=
      fun xs letMuts => ⌜xs.prefix = [] ∧ letMuts = seen✝ ∨ xs.suffix = [] ∧ l.Nodup⌝)
-/
#guard_msgs (info) in
theorem polyNodup_suggest_invariant [Monad m] [WPMonad m ps] (l : List Int) : ⦃⌜True⌝⦄ @polyNodup m _ l ⦃⇓r => ⌜r ↔ l.Nodup⌝⦄ := by
  mvcgen [polyNodup] invariants?
  all_goals admit

def fast_expo (x n : Nat) : Nat := Id.run do
  let mut x := x
  let mut y := 1
  let mut e := n
  for _ in [:n] do -- simulating a while loop running at most n times
    if e = 0 then break
    if e % 2 = 1 then
      y := x * y
      e := e - 1
    else
      x := x*x
      e := e/2

  return y

open Std.Do

/--
info: Try this:
  [apply] invariants
  · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = ⟨n, x, 1⟩ ∨ xs.suffix = [] ∧ letMuts.2.snd = x ^ n⌝
-/
#guard_msgs (info) in
theorem fast_expo_correct (x n : Nat) : fast_expo x n = x^n := by
  generalize h : fast_expo x n = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

namespace FreshBounded

structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFresh : EStateM String Supply Nat := do
  let supply ← get
  if h : supply.counter = supply.limit then
    throw s!"Supply exhausted: {supply.counter} = {supply.limit}"
  else
    let n := supply.counter
    have := supply.property
    set {supply with counter := n + 1, property := by omega}
    pure n

def mkFreshN (n : Nat) : ExceptT Char (EStateM String Supply) (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃post⟨fun r state => ⌜r = c ∧ c < state.counter⌝, fun _msg state => ⌜c = state.counter ∧ c = state.limit⌝⟩⦄ := by
  mvcgen [mkFresh]
  all_goals grind

/--
info: Try this:
  [apply] invariants
  ·
    post⟨fun ⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = acc✝ ∨ xs.suffix = [] ∧ letMuts.toList.Nodup⌝, fun x =>
      ⌜False⌝, fun _msg state => ⌜state.counter = state.limit⌝⟩
-/
#guard_msgs (info) in
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄
    mkFreshN n
    ⦃post⟨fun r => ⌜r.Nodup⌝, fun _ => ⌜False⌝, fun _msg state => ⌜state.counter = state.limit⌝⟩⦄ := by
  mvcgen [mkFreshN] invariants?
  -- The full invariant is:
  -- · post⟨fun ⟨xs, acc⟩ state => ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝,
  --        fun _ => ⌜False⌝,
  --        fun _msg state => ⌜state.counter = state.limit⌝⟩
  all_goals admit

end FreshBounded
