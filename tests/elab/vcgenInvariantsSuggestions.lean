import Std.WP
import Std.Tactic.Do
import Std

/-!
Tests for the `vcgen invariants?` suggestion mechanism: `vcgen` inspects how each `Invariant`
metavariable is used in the verification conditions and suggests an initial invariant.
-/

open Std.WP Lean.Order

set_option mvcgen.warning false
set_option warn.sorry false

def mySum (l : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in l do
    acc := acc + x
  return acc

/--
info: Try this:
  [apply] invariants
  · fun pref suff letMuts => pref = [] ∧ letMuts = 0 ∨ suff = [] ∧ letMuts = l.sum
-/
#guard_msgs (info) in
theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
  generalize h : mySum l = r
  apply Id.of_run_eq_wp h
  vcgen invariants?
  all_goals sorry

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
  · fun pref suff letMuts => pref = [] ∧ letMuts = (0, 0) ∨ suff = [] ∧ letMuts.fst = l.sum
-/
#guard_msgs (info) in
theorem mySum2_suggest_invariant (l : List Nat) : mySum2 l = l.sum := by
  generalize h : mySum2 l = r
  apply Id.of_run_eq_wp h
  vcgen invariants?
  all_goals sorry

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturnNewDo (onContinue := fun pref suff letMuts =>
      pref = [] ∧ letMuts = ∅ ∨ suff = [] ∧ l.Nodup) (onReturn := fun r letMuts => (r = true ↔ l.Nodup) ∧ l.Nodup)
-/
#guard_msgs (info) in
theorem nodup_suggest_invariant (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_run_eq_wp h
  vcgen invariants?
  all_goals sorry

def sumSt (l : List Nat) : StateM Nat Unit := do
  for x in l do
    modify (· + x)

/--
info: Try this:
  [apply] invariants
  · fun pref suff letMuts s => pref = [] ∧ letMuts = PUnit.unit ∨ suff = [] ∧ s = l.sum
-/
#guard_msgs (info) in
theorem sumSt_suggest_invariant (l : List Nat) :
    ⦃ fun s => s = 0 ⦄ sumSt l ⦃ fun _ s => s = l.sum ⦄ := by
  vcgen [sumSt] invariants?
  all_goals sorry

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

/--
info: Try this:
  [apply] invariants
  · fun pref suff letMuts => pref = [] ∧ letMuts = (x, 1, n) ∨ suff = [] ∧ letMuts.snd.fst = x ^ n
-/
#guard_msgs (info) in
theorem fast_expo_suggest_invariant (x n : Nat) : fast_expo x n = x^n := by
  generalize h : fast_expo x n = r
  apply Id.of_run_eq_wp h
  vcgen invariants?
  all_goals sorry

def earlyReturnWithoutLetMut (l : List Int) : Bool := Id.run do
  for x in l do
    if x < 0 then return true
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturnNewDo (onContinue := fun pref suff letMuts => pref = [] ∨ suff = []) (onReturn :=
      fun r letMuts => r = true)
-/
#guard_msgs (info) in
theorem earlyReturnWithoutLetMut_suggest_invariant (l : List Int) : earlyReturnWithoutLetMut l := by
  generalize h : earlyReturnWithoutLetMut l = r
  apply Id.of_run_eq_wp h
  vcgen invariants?
  all_goals sorry

def notQuiteEarlyReturn (l : List Nat) : Option Nat := Id.run do
  -- The type of the state tuple *looks* like an early return, but `last` is not used
  -- according to early return semantics.
  let mut last : Option Nat := none
  let mut mdummy : Unit := ()
  for x in l do
    last := some x
    mdummy := ()
  return last

/--
info: Try this:
  [apply] invariants
  · fun pref suff letMuts => pref = [] ∧ letMuts = (none, PUnit.unit) ∨ suff = [] ∧ letMuts.fst = l.getLast?
-/
#guard_msgs (info) in
theorem notQuiteEarlyReturn_suggest_invariant (l : List Nat) : notQuiteEarlyReturn l = l.getLast? := by
  generalize h : notQuiteEarlyReturn l = r
  apply Id.of_run_eq_wp h
  vcgen invariants?
  all_goals sorry

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
  [apply] invariants
  · fun pref suff letMuts s1 s2 s3 => pref = [] ∧ letMuts = { toList := [] } ∨ suff = [] ∧ letMuts.toList.Nodup
-/
#guard_msgs (info) in
theorem mkFreshN_suggest_invariant (n : Nat) :
    ⦃ fun _ _ _ => True ⦄ mkFreshN n ⦃ fun r _ _ _ => r.Nodup ⦄ := by
  vcgen [mkFreshN, mkFresh, liftCounterM] invariants?
  all_goals sorry

def mkFreshN_early_return (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let k ← liftCounterM mkFresh
    if k > 13 then return acc.toList
    acc := acc.push k
  return acc.toList

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturnNewDo (onContinue := fun pref suff letMuts s1 s2 s3 =>
      pref = [] ∧ letMuts = { toList := [] } ∨ suff = [] ∧ letMuts.toList.Nodup) (onReturn := fun r letMuts s1 s2 s3 =>
      r.Nodup ∧ letMuts.toList.Nodup)
-/
#guard_msgs (info) in
theorem mkFreshN_early_return_suggest_invariant (n : Nat) :
    ⦃ fun _ _ _ => True ⦄ mkFreshN_early_return n ⦃ fun r _ _ _ => r.Nodup ⦄ := by
  vcgen [mkFreshN_early_return, mkFresh, liftCounterM] invariants?
  all_goals sorry

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
  · fun pref suff letMuts => ⌜pref = [] ∧ letMuts = (0, 0) ∨ suff = [] ∧ letMuts.fst = l.sum⌝
-/
#guard_msgs (info) in
theorem polySum_suggest_invariant [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (l : List Nat) :
    ⦃ (⊤ : Pred) ⦄ (polySum l : m Nat) ⦃ fun r => (⌜r = l.sum⌝ : Pred) ⦄ := by
  vcgen [polySum] invariants?
  all_goals sorry

def polyNodup [Monad m] (l : List Int) : m Bool := do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

/--
info: Try this:
  [apply] invariants
  ·
    Invariant.withEarlyReturnNewDo (onContinue := fun pref suff letMuts =>
      ⌜pref = [] ∧ letMuts = ∅ ∨ suff = [] ∧ l.Nodup⌝) (onReturn := fun r letMuts => ⌜(r = true ↔ l.Nodup) ∧ l.Nodup⌝)
-/
#guard_msgs (info) in
theorem polyNodup_suggest_invariant [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] (l : List Int) :
    ⦃ (⊤ : Pred) ⦄ (polyNodup l : m Bool) ⦃ fun r => (⌜r = true ↔ l.Nodup⌝ : Pred) ⦄ := by
  vcgen [polyNodup] invariants?
  all_goals sorry

def esum (l : List Nat) : EStateM String Nat Unit := do
  for x in l do
    if x > 100 then throw "too big"
    modify (· + x)

/--
info: Try this:
  [apply] invariants
  · fun pref suff letMuts s => pref = [] ∧ letMuts = PUnit.unit ∨ suff = [] ∧ s = l.sum
-/
#guard_msgs (info) in
theorem esum_suggest_invariant (l : List Nat) :
    ⦃ fun s => s = 0 ⦄ esum l ⦃ fun _ s => s = l.sum ⦄ := by
  vcgen [esum] invariants?
  all_goals sorry
