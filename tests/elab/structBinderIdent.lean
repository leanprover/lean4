/-!
# Testing structure declarations, including unbracketed parameters
-/

/-!
Structure with no parameters, no type, named constructor, and derived instance
-/
structure NatPair where
  mkPair ::
  fst : Nat
  snd : Nat
  deriving Inhabited

/-- info: NatPair : Type -/
#guard_msgs in
#check NatPair

/-- info: NatPair.mkPair (fst snd : Nat) : NatPair -/
#guard_msgs in
#check NatPair.mkPair

/-- info: instInhabitedNatPair -/
#guard_msgs in
#synth Inhabited NatPair

/-!
Structure with type and no parameters
-/
structure Pointed : Type u where
  α : Sort u
  x : α

/-- info: Pointed.{u} : Type u -/
#guard_msgs in
#check Pointed

/-- info: Pointed.mk.{u} (α : Sort u) (x : α) : Pointed -/
#guard_msgs in
#check Pointed.mk

/-!
Structure with unbracketed parameter, no type, and derived instance
-/
structure Δ n where
  val : Fin (n + 1)
  deriving Inhabited

/-- info: Δ (n : Nat) : Type -/
#guard_msgs in
#check Δ

/-- info: Δ.mk {n : Nat} (val : Fin (n + 1)) : Δ n -/
#guard_msgs in
#check Δ.mk

/-- info: @instInhabitedΔ -/
#guard_msgs in
#synth ∀ n, Inhabited (Δ n)

/-!
Structure with unbracketed parameters, type, and extends
-/
structure Prod₃ α β γ : Type u extends toProd : α × β where
  trd : (γ : Type u)

/-- info: Prod₃.{u} (α β γ : Type u) : Type u -/
#guard_msgs in
#check Prod₃

/-- info: Prod₃.mk.{u} {α β γ : Type u} (toProd : α × β) (trd : γ) : Prod₃ α β γ -/
#guard_msgs in
#check Prod₃.mk

/-- info: Prod₃.toProd.{u} {α β γ : Type u} (self : Prod₃ α β γ) : α × β -/
#guard_msgs in
#check Prod₃.toProd

/-!
Structure with no type and mixture of bracketed and unbracketed parameters
-/
structure IsLt {n} (i : Fin n) j where
  pf : i < j

/-- info: IsLt {n : Nat} (i j : Fin n) : Prop -/
#guard_msgs in
#check IsLt

/-- info: IsLt.mk {n : Nat} {i j : Fin n} (pf : i < j) : IsLt i j -/
#guard_msgs in
#check IsLt.mk

/-!
Structure with type and mixture of bracketed and unbracketed parameters
-/
structure Eval {n} (F : Fin n → Sort u) i : Sort (max 1 u) where
  value : F i

/-- info: Eval.{u} {n : Nat} (F : Fin n → Sort u) (i : Fin n) : Sort (max 1 u) -/
#guard_msgs in
#check Eval

/-- info: Eval.mk.{u} {n : Nat} {F : Fin n → Sort u} {i : Fin n} (value : F i) : Eval F i -/
#guard_msgs in
#check Eval.mk
