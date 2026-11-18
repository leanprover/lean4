import Lean
/-!
The equation compiler skips an alternative of a `match` when a discriminant and the corresponding
pattern are different literals, and the local context has no hypotheses. Only literals in their
standard representation are considered: no instance is unfolded, and no type is evaluated.
-/
open Lean Meta

/-! `(5 : UInt8)` is elaborated with a local instance, and denotes `0`. -/

def f (b : Bool) : Nat :=
  letI : OfNat UInt8 5 := ⟨0⟩
  match (5 : UInt8), b with
  | 0, true => 1
  | _, _ => 2

/--
info: f.eq_1: f true = 1
---
info: f.eq_2: ∀ (b_1 : Bool), (5 = 0 → b_1 = true → False) → f b_1 = 2
-/
#guard_msgs in
run_meta do
  for n in (← getEqnsFor? ``f).get! do
    logInfo m!"{n}: {(← getConstInfo n).type}"

example : f true = 1 := f.eq_1

/-! The same example with `Float`, whose functions are opaque. -/

def g (b : Bool) : Nat :=
  letI : OfNat Float 5 := ⟨0⟩
  match (5 : Float), b with
  | 0, true => 1
  | _, _ => 2

example : g true = 1 := g.eq_1

/-! The discriminants are not evaluated: here, it would exceed the recursion depth limit. -/

def slowUInt8 : Nat → UInt8
  | 0 => 5
  | n+1 => slowUInt8 n

def k (b : Bool) : Nat :=
  letI : OfNat UInt8 5 := ⟨slowUInt8 10000⟩
  match (5 : UInt8), b with
  | _, false => 1
  | _, true => 2

example : k false = 1 := k.eq_1

def slow : Nat → Nat
  | 0 => 7
  | n+1 => slow n

def width (b : Bool) : Nat :=
  match (5 : BitVec (slow 10000)), b with
  | _, false => 1
  | _, true => 2

example : width false = 1 := width.eq_1

/-! Literals of the supported types. -/

def str (b : Bool) : String → Nat
  | "a" => 0
  | "b" => if b then 1 else 2
  | _ => 3

example : str true "b" = 1 := by simp [str]
example : str true "c" = 3 := by simp [str]

def nat (b : Bool) : Nat → Nat
  | 0 => 0
  | 5 => if b then 1 else 2
  | _ => 3

example : nat true 5 = 1 := by simp [nat]
example : nat true 7 = 3 := by simp [nat]

def int (b : Bool) : Int → Nat
  | -5 => 0
  | 5 => if b then 1 else 2
  | _ => 3

example : int true 5 = 1 := by simp [int]
example : int true (-5) = 0 := by simp [int]
example : int true 7 = 3 := by simp [int]

def char (b : Bool) : Char → Nat
  | 'a' => 0
  | 'b' => if b then 1 else 2
  | _ => 3

example : char true 'b' = 1 := by simp [char]
example : char true 'c' = 3 := by simp [char]

def uint8 (b : Bool) : UInt8 → Nat
  | 0 => 0
  | 5 => if b then 1 else 2
  | _ => 3

example : uint8 true 5 = 1 := by simp [uint8]
example : uint8 true 7 = 3 := by simp [uint8]

def fin (b : Bool) : Fin 8 → Nat
  | 0 => 0
  | 5 => if b then 1 else 2
  | _ => 3

example : fin true 5 = 1 := by simp [fin]
example : fin true 7 = 3 := by simp [fin]

def bitVec (b : Bool) : BitVec 8 → Nat
  | 0#8 => 0
  | 5#8 => if b then 1 else 2
  | _ => 3

example : bitVec true 5#8 = 1 := by simp [bitVec]
example : bitVec true 7#8 = 3 := by simp [bitVec]

/-!
The equations of these functions at a literal. The second alternative is selected after the first
one is skipped.
-/

/--
info: nat.eq_2: ∀ (b : Bool), nat b 5 = if b = true then 1 else 2
---
info: int.eq_2: ∀ (b : Bool), int b 5 = if b = true then 1 else 2
---
info: char.eq_2: ∀ (b : Bool), char b 'b' = if b = true then 1 else 2
---
info: uint8.eq_2: ∀ (b : Bool), uint8 b 5 = if b = true then 1 else 2
---
info: fin.eq_2: ∀ (b : Bool), fin b 5 = if b = true then 1 else 2
---
info: bitVec.eq_2: ∀ (b : Bool), bitVec b 5#8 = if b = true then 1 else 2
-/
#guard_msgs in
run_meta do
  for f in [``nat, ``int, ``char, ``uint8, ``fin, ``bitVec] do
    let n := (← getEqnsFor? f).get![1]!
    logInfo m!"{n}: {(← getConstInfo n).type}"

/-!
An alternative with a different literal is still selected if a local hypothesis states that the
two literals are equal.
-/

def absurdNat (_h : 1 = 2) : Nat :=
  match (1 : Nat) with
  | 2 => 10
  | _ => 20

example (h : 1 = 2) : absurdNat h = 10 := absurdNat.eq_1 h

def absurdStr (_h : "a" = "b") : Nat :=
  match "a" with
  | "b" => 10
  | _ => 20

example (h : "a" = "b") : absurdStr h = 10 := absurdStr.eq_1 h

abbrev Value : Bool → Type | true => Nat | false => String

def absurdHEq (_h : HEq (0 : Nat) (1 : Nat)) : Nat :=
  match (motive := (b : Bool) → Value b → Nat) true, (0 : Nat) with
  | true, (1 : Nat) => 10
  | true, _ => 20
  | false, _ => 30

example (h : HEq (0 : Nat) (1 : Nat)) : absurdHEq h = 10 := absurdHEq.eq_1 h

/-! The type of a hypothesis is not unfolded: here, it would exceed the recursion depth limit. -/

def SlowProp : Nat → Prop
  | 0 => True
  | n + 1 => SlowProp n

def slowHyp (_ : SlowProp 10000) : Nat :=
  match (1 : Nat) with
  | 1 => 10
  | _ => 20

/-- info: slowHyp.eq_1: ∀ (x : SlowProp 10000), slowHyp x = 10 -/
#guard_msgs in
run_meta do
  for n in (← getEqnsFor? ``slowHyp).get! do
    logInfo m!"{n}: {(← getConstInfo n).type}"

/-! A hypothesis that proves the equality between the two literals using a unification hint. -/

def Hidden : Prop := (1 : Nat) = 2
unif_hint where
  |- Hidden ≟ ((1 : Nat) = 2)

def hint (_h : Hidden) (_bad : False) : Nat :=
  match (1 : Nat) with
  | 2 => 10
  | _ => 20

/-- info: hint.eq_1: ∀ (_h : Hidden) (_bad : False), hint _h _bad = 10 -/
#guard_msgs in
run_meta do
  for n in (← getEqnsFor? ``hint).get! do
    logInfo m!"{n}: {(← getConstInfo n).type}"
