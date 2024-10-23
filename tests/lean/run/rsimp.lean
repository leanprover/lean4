import Std.Tactic.RSimp

/-!
Basic testing of syntax
-/

set_option trace.tactic.rsimp_decide true

structure MyTrue : Prop

instance : Decidable MyTrue := .isTrue MyTrue.mk
@[simp] theorem decide_MyTrue : decide MyTrue  = true := rfl

/--
info: [tactic.rsimp_decide] Optimized expression:
      decide MyTrue
-/
#guard_msgs in
def ex1 : MyTrue := by rsimp_decide

/--
info: [tactic.rsimp_decide] Optimized expression:
      true
-/
#guard_msgs in
def ex2 : MyTrue := by rsimp_decide [decide_MyTrue]


attribute [rsimp] decide_MyTrue

/--
info: [tactic.rsimp_decide] Optimized expression:
      true
-/
#guard_msgs in
def ex3 : MyTrue := by rsimp_decide

/--
info: [tactic.rsimp_decide] Optimized expression:
      decide MyTrue
-/
#guard_msgs in
def ex4 : MyTrue := by rsimp_decide only

/--
error: tactic 'rsimp_decide' failed, this may be because the proposition is false, involves non-computable axioms or opaque definitions.
⊢ False
---
info: [tactic.rsimp_decide] Optimized expression:
      decide False
-/
#guard_msgs in
def ex5 : False := by rsimp_decide

/--
error: tactic 'rsimp_decide' failed, this may be because the proposition is false, involves non-computable axioms or opaque definitions.
⊢ False
---
info: [tactic.rsimp_decide] Optimized expression:
      decide False
[tactic.rsimp_decide.debug] mkAuxLemma failed: (kernel) declaration type mismatch, 'lean.run.rsimp._auxLemma.3' has type
      true = true
    but it is expected to have type
      decide False = true
-/
#guard_msgs in
set_option trace.tactic.rsimp_decide.debug true in
def ex6 : False := by rsimp_decide


-- Check that level parameters don't trip it up
local instance inst.{u} : Decidable (Nonempty PUnit.{u}) := .isTrue ⟨⟨⟩⟩
def ex7.{v} : Nonempty (PUnit.{v}) := by rsimp_decide
