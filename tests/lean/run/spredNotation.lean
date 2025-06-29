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


/-- info: ⌜φ⌝ : SVal [Nat, Char, Bool] Prop -/
#guard_msgs in
#check (⌜φ⌝ : SPred [Nat,Char,Bool])

-- TODO: Figure out how to delaborate away tuple below
/--
info: ⌜7 + ‹Nat›ₛ tuple = if ‹Bool›ₛ tuple = true then 13 else 7⌝ : SVal [Nat, Char, Bool] Prop
-/
#guard_msgs in
#check (⌜7 + ‹Nat›ₛ = if ‹Bool›ₛ then 13 else 7⌝ : SPred [Nat,Char,Bool])

private abbrev theChar : SVal [Nat,Char,Bool] Char := fun _ c _ => c
/-- info: ⌜#theChar tuple = 'a'⌝ : SVal [Nat, Char, Bool] Prop -/
#guard_msgs in
#check ⌜#theChar = 'a'⌝


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
else ⌜False⌝ : SVal [Nat, Char, Bool] Prop
-/
#guard_msgs in
#check spred(if true then term(match (1,2) with | (x,y) => Φ x y) else ⌜False⌝)

/-- info: Ψ (1 + 1) : SPred [Nat, Char, Bool] -/
#guard_msgs in
#check spred(Ψ (1 + 1))


private abbrev theNat : SVal [Nat, Bool] Nat := fun n _ => n
example (P Q : SPred [Nat, Bool]): SPred [Char, Nat, Bool] :=
  spred(fun c => ((∀ y, if y = 4 then ⌜y = #theNat⌝ ∧ P else Q) ∧ Q) → (∃ x, P → if (x : Bool) then Q else P))

-- A bigger example testing unexpansion as well: (TODO: Figure out how to delaborate away tuple below)
/--
info: fun P Q n =>
  spred((∀ y, if y = n then ⌜‹Nat›ₛ tuple + #theNat tuple = 4⌝ else Q) ∧ Q →
      P → ∃ x, P → if x = true then Q else P) : SPred [Nat, Bool] → SPred [Nat, Bool] → Char → SPred [Nat, Bool]
-/
#guard_msgs in
#check fun P Q => spred(fun (n : Char) => ((∀ y, if y = n then ⌜‹Nat›ₛ + #theNat = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))

-- Unexpansion should work irrespective of binder name for `f`/`escape`:
/--
info: ∀ (a b n o : Nat) (s : Nat × Nat), ⌜a = n ∧ b = o⌝ ⊢ₛ ⌜s.fst = n ∧ a = n + 1 ∧ b = o⌝ : Prop
-/
#guard_msgs in
set_option linter.unusedVariables false in
#check ∀ (a b n o : Nat) (s : Nat × Nat), (SVal.curry fun f => a = n ∧ b = o) ⊢ₛ SVal.curry fun f => s.1 = n ∧ a = n + 1 ∧ b = o
