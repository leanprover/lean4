module

public structure A where
  a : Nat
deriving DecidableEq, BEq

-- should all be exposed

/-- info: @[expose] def instDecidableEqA : DecidableEq A -/
#guard_msgs in #with_exporting #print sig instDecidableEqA

/-- info: @[expose] def instDecidableEqA.decEq : (x x_1 : A) → Decidable (x = x_1) -/
#guard_msgs in #with_exporting #print sig instDecidableEqA.decEq

/-- info: @[expose] def instBEqA : BEq A -/
#guard_msgs in #with_exporting #print sig instBEqA

/-- info: @[expose] def instBEqA.beq : A → A → Bool -/
#guard_msgs in #with_exporting #print sig instBEqA.beq

structure B where
  a : Nat
deriving DecidableEq, BEq

-- Should not be visible with `#with_exporting` since `B` is private

/-- error: Unknown constant `instDecidableEqB` -/
#guard_msgs in #with_exporting #print sig instDecidableEqB

/-- error: Unknown constant `instDecidableEqB.decEq` -/
#guard_msgs in #with_exporting #print sig instDecidableEqB.decEq

/-- error: Unknown constant `instBEqB` -/
#guard_msgs in #with_exporting #print sig instBEqB

/-- error: Unknown constant `instBEqB.beq` -/
#guard_msgs in #with_exporting #print sig instBEqB.beq

public structure C where
  private a : Nat
deriving DecidableEq, BEq

-- Should not be visible with `#with_exporting` since `B` is private

/-- info: @[expose] def instDecidableEqC : DecidableEq C -/
#guard_msgs in #with_exporting #print sig instDecidableEqC

/-- info: def instDecidableEqC.decEq : (x x_1 : C) → Decidable (x = x_1) -/
#guard_msgs in #with_exporting #print sig instDecidableEqC.decEq

/-- info: @[expose] def instBEqC : BEq C -/
#guard_msgs in #with_exporting #print sig instBEqC

/-- info: def instBEqC.beq : C → C → Bool -/
#guard_msgs in #with_exporting #print sig instBEqC.beq
