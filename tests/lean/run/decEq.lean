module

import Lean

set_option trace.Elab.Deriving.decEq true
set_option deriving.deceq.avoid_match_threshold 1

public inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n+1)
  -- deriving DecidableEq

run_meta Lean.mkCasesOnSameCtor `Vec.match_OnSameCtor ``Vec

#eval do pure (← Lean.Meta.getMatcherInfo? ``Vec.match_OnSameCtor).isSome

set_option trace.Elab.definition.structural true

def decEqVec {α} {a} [DecidableEq α] (x : @Vec α a) (x_1 : @Vec α a) : Decidable (x = x_1) :=
  if h : Vec.ctorIdx x = Vec.ctorIdx x_1 then
    Vec.match_OnSameCtor x x_1 h (isTrue rfl)
      @fun a_1 _ a_2 b b_1 =>
        if h_1 : @a_1 = @b then by
          subst h_1
          exact
            let inst := decEqVec @a_2 @b_1;
            if h_2 : @a_2 = @b_1 then by subst h_2; exact isTrue rfl
            else isFalse (by intro n; injection n; apply h_2 _; assumption)
        else isFalse (by intro n_1; injection n_1; apply h_1 _; assumption)
  else isFalse (fun h' => h (congrArg Vec.ctorIdx h'))
termination_by structural x
#print decEqVec

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

/-- info: Decidable.rec (fun h => false) (fun h => true) (decEqPubInd PubInd.b PubInd.b) -/
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
