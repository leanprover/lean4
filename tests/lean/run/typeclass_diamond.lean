@[class] axiom Top₁   (n : Nat) : Type
@[class] axiom Bot₁   (n : Nat) : Type
@[class] axiom Left₁  (n : Nat) : Type
@[class] axiom Right₁ (n : Nat) : Type

@[instance] axiom Bot₁Inst : Bot₁ Nat.zero

@[instance] axiom Left₁ToBot₁   (n : Nat) [Left₁ n]  : Bot₁ n
@[instance] axiom Right₁ToBot₁  (n : Nat) [Right₁ n] : Bot₁ n
@[instance] axiom Top₁ToLeft₁   (n : Nat) [Top₁ n]   : Left₁ n
@[instance] axiom Top₁ToRight₁  (n : Nat) [Top₁ n]   : Right₁ n
@[instance] axiom Bot₁ToTopSucc (n : Nat) [Bot₁ n]   : Top₁ n.succ

@[class] axiom Top₂ (n : Nat) : Type
@[class] axiom Bot₂   (n : Nat) : Type
@[class] axiom Left₂  (n : Nat) : Type
@[class] axiom Right₂ (n : Nat) : Type

@[instance] axiom Left₂ToBot₂   (n : Nat) [Left₂ n]  : Bot₂ n
@[instance] axiom Right₂ToBot₂  (n : Nat) [Right₂ n] : Bot₂ n
@[instance] axiom Top₂ToLeft₂   (n : Nat) [Top₂ n]   : Left₂ n
@[instance] axiom Top₂ToRight₂  (n : Nat) [Top₂ n]   : Right₂ n
@[instance] axiom Bot₂ToTopSucc (n : Nat) [Bot₂ n]   : Top₂ n.succ

@[class] axiom Top (n : Nat) : Type

@[instance] axiom Top₁ToTop (n : Nat) [Top₁ n] : Top n
@[instance] axiom Top₂ToTop (n : Nat) [Top₂ n] : Top n

#synth Top Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
