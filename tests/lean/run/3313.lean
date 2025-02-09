class AddCommGroup (α : Type) extends Zero α where

class Ring (α : Type) extends Zero α, AddCommGroup α

class Module (R : Type) (M : Type) [Zero R] [Zero M] where

instance (R : Type) [Zero R] : Module R R := ⟨⟩

structure Submodule (R : Type) (M : Type) [Zero R] [Zero M] [Module R M] : Type where

class HasQuotient (A : outParam <| Type) (B : Type) where
  quotient' : B → Type

instance Submodule.hasQuotient {R : Type} {M : Type} [Ring R] [AddCommGroup M]
  [Module R M]: HasQuotient M (Submodule R M) := ⟨fun _ => M⟩

def Synonym (M : Type) [Zero M] := M

instance Synonym.zero {G : Type} [Zero G] : Zero (Synonym G) := ⟨(Zero.zero : G)⟩

instance Synonym.addCommGroup {G : Type} [AddCommGroup G] : AddCommGroup (Synonym G) :=
  { Synonym.zero with }

instance Synonym.module (M : Type) {R : Type} [Zero R] [Zero M] [Module R M] :
    Module R (Synonym M) := { }

variable (R : Type) [Ring R]


set_option maxSynthPendingDepth 2 in
/-- info: Submodule.hasQuotient -/
#guard_msgs in
#synth HasQuotient (Synonym (Synonym R)) (Submodule R (Synonym (Synonym R))) -- works

/-!
After https://github.com/leanprover/lean4/pull/5920 works without changing maxSynthPendingDepth.
-/
/-- info: Submodule.hasQuotient -/
#guard_msgs in
#synth HasQuotient (Synonym (Synonym R)) (Submodule R (Synonym (Synonym R)))
