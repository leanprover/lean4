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
