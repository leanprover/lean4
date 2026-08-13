import Std.Tactic.Do
import Std.Internal.Do

/-!
`vcgen` tries the `@[spec]` theorems matching a program in descending priority order and applies the
first one whose backward rule applies. A spec guarded by an instance the call site does not provide
is passed over for the next candidate.
-/

set_option mvcgen.warning false
set_option warn.sorry false

open Std.Internal.Do Lean.Order

class Missing (ρ : Type) : Prop

class Provided (ρ : Type) : Prop

instance : Provided (List Nat) := ⟨⟩

opaque run {ρ : Type} (xs : ρ) (init : Nat) : Id Nat

@[spec] theorem spec_run_list {xs : List Nat} {init : Nat} :
    ⦃⌜True⌝⦄ run xs init ⦃fun r => ⌜r = 1⌝⦄ := sorry

@[spec high] theorem spec_run_missing {ρ : Type} [Missing ρ] {xs : ρ} {init : Nat} :
    ⦃⌜True⌝⦄ run xs init ⦃fun r => ⌜r = 2⌝⦄ := sorry

-- The higher-priority `spec_run_missing` needs `Missing (List Nat)`, so `spec_run_list` applies.
example : ⦃⌜True⌝⦄ run [1, 2, 3] 0 ⦃fun r => ⌜r = 1⌝⦄ := by
  vcgen

opaque tick {ρ : Type} (xs : ρ) : Id Nat

@[spec] theorem spec_tick_list {xs : List Nat} : ⦃⌜True⌝⦄ tick xs ⦃fun r => ⌜r = 1⌝⦄ := sorry

@[spec high] theorem spec_tick_provided {ρ : Type} [Provided ρ] {xs : ρ} :
    ⦃⌜True⌝⦄ tick xs ⦃fun r => ⌜r = 2⌝⦄ := sorry

-- `Provided (List Nat)` is available, so the higher-priority `spec_tick_provided` wins.
example : ⦃⌜True⌝⦄ tick [1, 2, 3] ⦃fun r => ⌜r = 2⌝⦄ := by
  vcgen

opaque solo {ρ : Type} (xs : ρ) : Id Nat

@[spec] theorem spec_solo_missing {ρ : Type} [Missing ρ] {xs : ρ} :
    ⦃⌜True⌝⦄ solo xs ⦃fun r => ⌜r = 1⌝⦄ := sorry

/-- error: No spec applicable to program solo [1, 2, 3] in monad Id. Candidates were [SpecProof.global spec_solo_missing]. -/
#guard_msgs in
example : ⦃⌜True⌝⦄ solo [1, 2, 3] ⦃fun r => ⌜r = 1⌝⦄ := by
  vcgen
