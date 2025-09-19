import Std.Tactic.Do
import Std

open Std Do

set_option grind.warning false
set_option mvcgen.warning false

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: Try this:
  invariants
    · ⇓⟨xs, acc⟩ => _
-/
#guard_msgs (info) in
theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
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
  invariants
    · Invariant.withEarlyReturn (onReturn := fun r acc => _) (onContinue := fun xs acc => _)
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
  invariants
    · Invariant.withEarlyReturn (onReturn := fun r acc => _) (onContinue := fun xs acc => _)
    · Invariant.withEarlyReturn (onReturn := fun r acc => _) (onContinue := fun xs acc => _)
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

/--
info: Try this:
  invariants
    · ⇓⟨xs, acc⟩ => _
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
  invariants
    · Invariant.withEarlyReturn (onReturn := fun r acc => _) (onContinue := fun xs acc => _)
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
  invariants
    · Invariant.withEarlyReturn (onReturn := fun r acc => _) (onContinue := fun xs acc => _)
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
  invariants
    · ⇓⟨xs, acc⟩ => _
-/
#guard_msgs (info) in
theorem notQuiteEarlyReturn_suggest_invariant (l : List Nat) : notQuiteEarlyReturn l = l.getLast? := by
  generalize h : notQuiteEarlyReturn l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
  all_goals admit

def polyMonad [Monad m] (l : List Nat) : m (Option Nat) := do
  -- The idea here is that the type of the state tuple *looks* like it's an early return, but `last`
  -- is not used as if it is an early return variable. Specifically, `last` is set without breaking
  -- out of the loop.
  let mut last : Option Nat := none
  let mut mdummy : Unit := () -- m* is important because let mut vars are sorted alphabetically
  for x in l do
    last := some x
    mdummy := ()
  return last

/--
info: Try this:
  invariants
    · ⇓⟨xs, acc⟩ => _
-/
#guard_msgs (info) in
theorem polyMonad_suggest_invariant [Monad m] [WPMonad m ps] (l : List Nat) : ⦃⌜True⌝⦄ @polyMonad m _ l ⦃⇓ r => ⌜True⌝⦄ := by
  mvcgen [polyMonad] invariants?
  all_goals admit
