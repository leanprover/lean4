class Top₁   (n : Nat) : Type := (u : Unit := ())
class Bot₁   (n : Nat) : Type := (u : Unit := ())
class Left₁  (n : Nat) : Type := (u : Unit := ())
class Right₁ (n : Nat) : Type := (u : Unit := ())

instance Bot₁Inst : Bot₁ Nat.zero := {}
instance Left₁ToBot₁   (n : Nat) [Left₁ n]  : Bot₁ n := {}

instance Right₁ToBot₁  (n : Nat) [Right₁ n] : Bot₁ n := {}
instance Top₁ToLeft₁   (n : Nat) [Top₁ n]   : Left₁ n := {}
instance Top₁ToRight₁  (n : Nat) [Top₁ n]   : Right₁ n := {}
instance Bot₁ToTopSucc (n : Nat) [Bot₁ n]   : Top₁ n.succ := {}

class Top₂ (n : Nat) : Type := (u : Unit := ())
class Bot₂   (n : Nat) : Type := (u : Unit := ())
class Left₂  (n : Nat) : Type := (u : Unit := ())
class Right₂ (n : Nat) : Type := (u : Unit := ())

instance Left₂ToBot₂   (n : Nat) [Left₂ n]  : Bot₂ n := {}
instance Right₂ToBot₂  (n : Nat) [Right₂ n] : Bot₂ n := {}
instance Top₂ToLeft₂   (n : Nat) [Top₂ n]   : Left₂ n := {}
instance Top₂ToRight₂  (n : Nat) [Top₂ n]   : Right₂ n := {}
instance Bot₂ToTopSucc (n : Nat) [Bot₂ n]   : Top₂ n.succ := {}

class Top (n : Nat) : Type := (u : Unit := ())

instance Top₁ToTop (n : Nat) [Top₁ n] : Top n := {}
instance Top₂ToTop (n : Nat) [Top₂ n] : Top n := {}

set_option synthInstance.maxHeartbeats 5000

#synth Top Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ

def tst : Top Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ :=
inferInstance
