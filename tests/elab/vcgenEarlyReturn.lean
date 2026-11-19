import Std.WP

set_option sym.debug true

/-!
`vcgen` checks a `return` inside a loop against the code after the loop (#16377). The invariant of
such a loop ranges over the loop's mutable variables, and every example closes with `finish`.
-/

open Std.WP

set_option experimental.vcgen true
set_option experimental.intrinsic true

/-! ## Intrinsic loops -/

/-- The example of #16377: a `return` inside an annotated `while` loop. -/
def findZero (xs : Array Nat) : Except String Nat := do
  let mut i := 0
  while i < xs.size
    invariant _ => i ≤ xs.size
    decreasing xs.size - i
  do
    if xs[i]! = 0 then return i
    i := i + 1
  throw "no zero"

theorem findZero_spec (xs : Array Nat) :
    ⦃ True ⦄ findZero xs ⦃ fun r => r < xs.size ∧ xs[r]! = 0; fun e => e = "no zero" ⦄ := by
  vcgen [findZero] with finish

/-- Code after the loop runs only when the loop does not return. -/
def findZeroOr (xs : Array Nat) : Except String Nat := do
  let mut i := 0
  while i < xs.size
    invariant done => i ≤ xs.size ∧ (done = true → i = xs.size)
    decreasing xs.size - i
  do
    if xs[i]! = 0 then return i
    i := i + 1
  let j := i * 2
  if j > 100 then throw "too long"
  return j + 1

theorem findZeroOr_spec (xs : Array Nat) :
    ⦃ True ⦄ findZeroOr xs
    ⦃ fun r => (r < xs.size ∧ xs[r]! = 0) ∨ r = 2 * xs.size + 1; fun _ => True ⦄ := by
  vcgen [findZeroOr] with finish

/-- A `return` inside an annotated `for` loop. -/
def firstAbove (xs : List Nat) (k : Nat) : Id (Option Nat) := do
  for x in xs invariant pref _ => ∀ y ∈ pref, y ≤ k do
    if x > k then return some x
  return none

theorem firstAbove_spec (xs : List Nat) (k : Nat) :
    ⦃ True ⦄ firstAbove xs k ⦃ fun r => (∀ x, r = some x → x > k) ∧ (r = none → ∀ y ∈ xs, y ≤ k) ⦄ := by
  vcgen [firstAbove] with finish

/-- The inner loop returns from the whole function. -/
def findPair (xs ys : List Nat) : Id (Option (Nat × Nat)) := do
  for x in xs invariant _ _ => True do
    for y in ys invariant _ _ => True do
      if x + y = 10 then return some (x, y)
  return none

theorem findPair_spec (xs ys : List Nat) :
    ⦃ True ⦄ findPair xs ys ⦃ fun r => ∀ p, r = some p → p.1 + p.2 = 10 ⦄ := by
  vcgen [findPair] with finish

/-! ## Extrinsic loops -/

/-- A `return` inside a `for` loop without annotations. -/
def firstAboveE (xs : List Nat) (k : Nat) : Id (Option Nat) := do
  for x in xs do
    if x > k then return some x
  return none

theorem firstAboveE_spec (xs : List Nat) (k : Nat) :
    ⦃ True ⦄ firstAboveE xs k ⦃ fun r => ∀ x, r = some x → x > k ⦄ := by
  vcgen [firstAboveE] invariants
  | inv1 => fun _ _ _ => True
  with finish

/-- A `return` inside a `while` loop without annotations, with a mutable variable. -/
def countdown (n : Nat) : Id Nat := do
  let mut i := n
  while i > 0 do
    if i = 3 then return 42
    i := i - 1
  return i

theorem countdown_spec (n : Nat) : ⦃ True ⦄ countdown n ⦃ fun r => r = 42 ∨ r = 0 ⦄ := by
  vcgen [countdown] invariants
  | inv1 => WhileInvariant.ofInvariantAndBreak (fun _ => True) (fun i => i = 0)
  | inv2 => .ofMeasure fun s => s.2
  with finish

/-- A `return` inside a `for h : x in xs` loop. -/
def firstZeroMem (xs : List Nat) : Id (Option Nat) := do
  for h : x in xs do
    if x = 0 then return some x
  return none

theorem firstZeroMem_spec (xs : List Nat) :
    ⦃ True ⦄ firstZeroMem xs ⦃ fun r => ∀ x, r = some x → x = 0 ⦄ := by
  vcgen [firstZeroMem] invariants
  | inv1 => fun _ _ _ => True
  with finish

/-- A `return` inside a loop over a `String`. -/
def firstSpace (s : String) : Id (Option Char) := do
  for c in s do
    if c = ' ' then return some c
  return none

theorem firstSpace_spec (s : String) :
    ⦃ True ⦄ firstSpace s ⦃ fun r => ∀ c, r = some c → c = ' ' ⦄ := by
  vcgen [firstSpace] invariants
  | inv1 => fun _ _ => True
  with finish

/-! ## Inlined callees

After `simp only` inlines `firstSmall` into `callerSmall`, the code after the call is a join point
that every exit of `firstSmall` jumps to. -/

def firstSmall (xs : List Nat) : StateM Nat Nat := do
  for x in xs invariant _ _ _ => True do
    if x = 0 then return 0
    if x = 1 then return 1
    if x = 2 then return 2
  return 3

def callerSmall (xs : List Nat) : StateM Nat Nat := do
  let v ← firstSmall xs
  set v
  return v + 1

theorem callerSmall_spec (xs : List Nat) :
    ⦃ fun _ => True ⦄ callerSmall xs ⦃ fun r s => r = s + 1 ∧ s ≤ 3 ⦄ := by
  simp only [callerSmall, firstSmall]
  vcgen +jp with finish

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (xs : List Nat) : ⦃ fun _ => True ⦄ callerSmall xs ⦃ fun r _ => r > 10 ⦄ := by
  simp only [callerSmall, firstSmall]
  vcgen +jp
  case vc1 => sorry

/-- `chain xs 12` inlines twelve early-return blocks, each followed by the rest of the chain. `vcgen
+jp` proves each rest once, so the chain fits a small heartbeat limit. -/
def chainStep (xs : List Nat) : StateM Nat Nat := do
  let mut acc := 0
  for x in xs invariant _ _ _ => True do
    if x = 0 then return acc
    if x = 1 then return acc + 1
    acc := acc + x
  let s ← get
  set (s + acc)
  return acc + s

def chain (xs : List Nat) : Nat → StateM Nat Nat
  | 0 => pure 0
  | n + 1 => do
    let r ← chainStep xs
    let q ← chain xs n
    return r + q

set_option maxHeartbeats 100000 in
example (xs : List Nat) : ⦃ fun _ => True ⦄ chain xs 12 ⦃ fun _ _ => True ⦄ := by
  simp only [chain, chainStep]
  vcgen +jp
