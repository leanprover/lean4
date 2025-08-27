module

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
  deriving DecidableEq

inductive Test (α : Type)
  | mk₀
  | mk₁ : (n : Nat) → (α × α) → List α → Vec α n → Test α
  | mk₂ : Test α → α → Test α
  deriving DecidableEq

def t1 [DecidableEq α] : DecidableEq (Vec α n) :=
  inferInstance

def t2 [DecidableEq α] : DecidableEq (Test α) :=
  inferInstance

/-! Public structures should yield public instances independent of `public section`. -/

public inductive PubEnum where
  | a | b
deriving DecidableEq

/-- info: decide (PubEnum.b = PubEnum.b) : Bool -/
#guard_msgs in
#with_exporting
#check decide (PubEnum.b = PubEnum.b)

public inductive PubInd where
  | a (n : Nat) | b
deriving DecidableEq

/-- info: Decidable.rec (fun h => false) (fun h => true) (decEqPubInd✝ PubInd.b PubInd.b) -/
#guard_msgs in
#with_exporting
#reduce decide (PubInd.b = PubInd.b)

public inductive PubExpInd where
  | a (n : Nat) | b
deriving @[expose] DecidableEq

/-- info: true -/
#guard_msgs in
#with_exporting
#reduce decide (PubExpInd.b = PubExpInd.b)
