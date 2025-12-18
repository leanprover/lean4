/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
import Std.Do.SPred.Notation

open Std.Do

variable
  (φ : Prop)
  (P Q R : SPred [Nat,Char,Bool])
  (Ψ : Nat → SPred [Nat, Char, Bool])
  (Φ : Nat → Nat → SPred [Nat, Char, Bool])

/-- info: P ⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊢ₛ Q

/-- info: P ⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊢ₛ Q

/-- info: P ⊣⊢ₛ Q : Prop -/
#guard_msgs in
#check P ⊣⊢ₛ Q


/-- info: ⌜φ⌝ : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check (⌜φ⌝ : SPred [Nat,Char,Bool])

/-- info: spred(P ∧ Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P ∧ Q)

/-- info: spred(P ∧ Q ∧ R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P ∧ (Q ∧ R))

/-- info: spred(P ∨ Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P ∨ Q)

/-- info: spred(P ∨ Q ∨ R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P ∨ (Q ∨ R))

/-- info: spred(¬P) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(¬ P)

/-- info: spred(¬(P ∨ Q)) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(¬ (P ∨ Q))


/-- info: spred(P → Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P → Q)

/-- info: spred(P → Q → R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P → (Q → R))

/-- info: spred(P ∧ Q → R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred((P ∧ Q) → R)

/-- info: spred(P → Q ∧ R) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P → (Q ∧ R))


/-- info: spred(P ↔ Q) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(P ↔ Q)

/-- info: spred(P ∧ Q ↔ Q ∧ P) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred((P ∧ Q) ↔ (Q ∧ P))


/-- info: ∀ (x : Nat), x = 0 : Prop -/
#guard_msgs in
#check ∀ (x : Nat), x = 0

/-- info: spred(∀ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∀ x, Ψ x)

/-- info: spred(∀ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∀ (x : Nat), Ψ x)

/-- info: spred(∀ x, ∀ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∀ x y, Φ x y)

/-- info: spred(∀ x, ∀ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∀ (x : Nat) (y : Nat), Φ x y)

/-- info: spred(∀ x, ∀ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∀ (x y : Nat), Φ x y)


/-- info: spred(∃ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∃ x, Ψ x)

/-- info: spred(∃ x, Ψ x) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∃ (x : Nat), Ψ x)

/-- info: spred(∃ x, ∃ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∃ x y, Φ x y)

/-- info: spred(∃ x, ∃ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∃ (x : Nat) (y : Nat), Φ x y)

/-- info: spred(∃ x, ∃ y, Φ x y) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(∃ (x y : Nat), Φ x y)


/--
info: if true = true then
  match (1, 2) with
  | (x, y) => Φ x y
else ⌜False⌝ : SPred [Nat, Char, Bool]
-/
#guard_msgs in
#check spred(if true then term(match (1,2) with | (x,y) => Φ x y) else ⌜False⌝)

/-- info: Ψ (1 + 1) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(Ψ (1 + 1))

example (P Q : SPred [Nat, Bool]): SPred [Char, Nat, Bool] :=
  spred(fun _ => ((∀ y, if y = 4 then (fun theNat => ⌜y = theNat⌝) ∧ P else Q) ∧ Q) → (∃ x, P → if (x : Bool) then Q else P))
