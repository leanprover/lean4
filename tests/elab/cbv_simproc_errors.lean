import Lean

open Lean Meta Sym.Simp

-- Attribute on a def that was never declared as a cbv simproc
meta def notASimproc : Simproc := fun _ => return .rfl

/-- error: Invalid `[cbv_simproc]` attribute: `notASimproc` is not a cbv simproc -/
#guard_msgs in
attribute [cbv_simproc] notASimproc

-- Attribute on a def with wrong type
def plainNat : Nat := 42

/-- error: Cbv simproc `plainNat` has an unexpected type: Expected `Simproc`, but found `Nat` -/
#guard_msgs in
attribute [cbv_simproc] plainNat

-- Erase from something without the attribute
cbv_simproc_decl untaggedProc (Nat.gcd _ _) := fun _ => return .rfl

/-- error: `untaggedProc` does not have a [cbv_simproc] attribute -/
#guard_msgs in
attribute [-cbvSimprocAttr] untaggedProc

-- Wrong type in cbv_simproc_decl pattern registration
def wrongType : Nat := 42

/--
error: Unexpected type for cbv simproc pattern: Expected `Simproc`, but `wrongType` has type
  Nat
-/
#guard_msgs in
cbv_simproc_pattern% Nat.succ _ => wrongType
