/-!
Tests for deriving decidable equality using the linear-size parallel match construction that takes
`x1.ctorIdx = x2.ctorIdx` as assumption.
-/

-- We always want to use the new construction in this test
set_option deriving.decEq.linear_construction_threshold 0

inductive EmptyType : Type
deriving DecidableEq

structure SimpleStruct where
  field : Bool
deriving DecidableEq

inductive DependentStruct1 : Nat → Type where
  | mk (n : Nat) (x : Fin n): DependentStruct1 n
deriving DecidableEq

/--
error: Dependent elimination failed: Failed to solve equation
  Bool.rec (motive := fun x => x.Reflects (b✝ = true) → Nat) (fun x => 1) (fun x => 0) (decide (b✝ = true)) ⋯ =
    Bool.rec (motive := fun x => x.Reflects (b = true) → Nat) (fun x => 1) (fun x => 0) (decide (b = true)) ⋯
-/
#guard_msgs in
inductive DependentStruct2 : Nat → Type where
  | mk (b : Bool) : DependentStruct2 (if b then 0 else 1)
deriving DecidableEq

inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
deriving DecidableEq

inductive Test (α : Type)
  | mk₀
  | mk₁ : (n : Nat) → (α × α) → List α → Vec α n → Test α
  | mk₂ : Test α → α → Test α
deriving DecidableEq
