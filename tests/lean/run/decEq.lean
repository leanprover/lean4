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

/-! Public structures should yield public exposed instances independent of `public section`. -/

/--
trace: [Elab.Deriving.decEq] ⏎
    public instance : DecidableEq✝ PubEnum✝ := fun x✝ y✝ =>
      if h✝ : x.toCtorIdx✝ = y.toCtorIdx✝ then
        isTrue✝
          (by
            first
            | have aux✝ := congrArg✝ PubEnum.ofNat h✝; rw [PubEnum.ofNat_toCtorIdx, PubEnum.ofNat_toCtorIdx] at aux✝;
              assumption
            | rfl)
      else isFalse✝ fun h✝ => by subst h✝; contradiction
-/
#guard_msgs in
set_option trace.Elab.Deriving.decEq true in
public inductive PubEnum where
  | a | b
deriving DecidableEq

/--
trace: [Elab.Deriving.decEq] ⏎
    [mutual
       @[expose✝]
       public def decEqPubInd✝ (x✝ : @PubInd✝) (x✝¹ : @PubInd✝) : Decidable✝ (x✝ = x✝¹) :=
         match x✝, x✝¹ with
         | @PubInd.a a✝, @PubInd.a b✝ =>
           if h✝ : @a✝ = @b✝ then by subst h✝; exact isTrue✝ rfl✝
           else isFalse✝ (by intro n✝; injection n✝; apply h✝ _; assumption)
         | PubInd.a .., PubInd.b .. => isFalse✝¹ (by intro h✝¹; injection h✝¹)
         | PubInd.b .., PubInd.a .. => isFalse✝¹ (by intro h✝¹; injection h✝¹)
         | @PubInd.b, @PubInd.b => isTrue✝¹ rfl✝¹
     end,
     @[expose✝]
     public instance : DecidableEq✝ (@PubInd✝) :=
       decEqPubInd✝]
-/
#guard_msgs in
set_option trace.Elab.Deriving.decEq true in
public inductive PubInd where
  | a (n : Nat) | b
deriving DecidableEq
