namespace MutualCoinduction
  mutual
    def f : Prop :=
      g
    coinductive_fixpoint

    def g : Prop :=
      f
    coinductive_fixpoint
  end
  /--
    info: MutualCoinduction.f.coinduct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2) (hyp_2 : pred_2 → pred_1) : pred_1 → f
  -/
  #guard_msgs in
  #check MutualCoinduction.f.coinduct
  /--
    info: MutualCoinduction.f.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2) (hyp_2 : pred_2 → pred_1) :
  (pred_1 → f) ∧ (pred_2 → g)
  -/
  #guard_msgs in
  #check MutualCoinduction.f.mutual_induct
  /--
    info: MutualCoinduction.g.coinduct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2) (hyp_2 : pred_2 → pred_1) : pred_2 → g
  -/
  #guard_msgs in
  #check MutualCoinduction.g.coinduct
  /--
    info: MutualCoinduction.g.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_1 → pred_2) (hyp_2 : pred_2 → pred_1) :
  (pred_1 → f) ∧ (pred_2 → g)
  -/
  #guard_msgs in
  #check MutualCoinduction.g.mutual_induct
end MutualCoinduction

namespace MutualInduction
  mutual
    def f : Prop :=
      g
    inductive_fixpoint

    def g : Prop :=
      f
    inductive_fixpoint
  end
  /--
    info: MutualInduction.f.induct (pred_1 pred_2 : Prop) (hyp_1 : pred_2 → pred_1) (hyp_2 : pred_1 → pred_2) : f → pred_1
  -/
  #guard_msgs in
  #check MutualInduction.f.induct
  /--
    info: MutualInduction.f.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_2 → pred_1) (hyp_2 : pred_1 → pred_2) :
  (f → pred_1) ∧ (g → pred_2)
  -/
  #guard_msgs in
  #check MutualInduction.f.mutual_induct
  /--
    info: MutualInduction.g.induct (pred_1 pred_2 : Prop) (hyp_1 : pred_2 → pred_1) (hyp_2 : pred_1 → pred_2) : g → pred_2
  -/
  #guard_msgs in
  #check MutualInduction.g.induct
  /--
    info: MutualInduction.g.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : pred_2 → pred_1) (hyp_2 : pred_1 → pred_2) :
  (f → pred_1) ∧ (g → pred_2)
  -/
  #guard_msgs in
  #check MutualInduction.g.mutual_induct
end MutualInduction

namespace MixedInductionCoinduction

  mutual
    def f : Prop :=
      g → f
    inductive_fixpoint

    def g : Prop :=
      f → g
    coinductive_fixpoint
  end
  /--
    info: MixedInductionCoinduction.f.induct (pred_1 pred_2 : Prop) (hyp_1 : (pred_2 → pred_1) → pred_1)
  (hyp_2 : pred_2 → pred_1 → pred_2) : f → pred_1
  -/
  #guard_msgs in
  #check f.induct
  /--
    info: MixedInductionCoinduction.f.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : (pred_2 → pred_1) → pred_1)
  (hyp_2 : pred_2 → pred_1 → pred_2) : (f → pred_1) ∧ (pred_2 → g)
  -/
  #guard_msgs in
  #check f.mutual_induct
  /--
    info: MixedInductionCoinduction.g.coinduct (pred_1 pred_2 : Prop) (hyp_1 : (pred_2 → pred_1) → pred_1)
  (hyp_2 : pred_2 → pred_1 → pred_2) : pred_2 → g
  -/
  #guard_msgs in
  #check g.coinduct
    /--
    info: MixedInductionCoinduction.g.mutual_induct (pred_1 pred_2 : Prop) (hyp_1 : (pred_2 → pred_1) → pred_1)
  (hyp_2 : pred_2 → pred_1 → pred_2) : (f → pred_1) ∧ (pred_2 → g)
  -/
  #guard_msgs in
  #check g.mutual_induct
end MixedInductionCoinduction

namespace DifferentPredicateTypes
  mutual
    def f (n : Nat) : Prop :=
      g (n+1) (n+2)
    coinductive_fixpoint

    def g (n m : Nat): Prop :=
      f (n + 2) ∨ g (m + 1) m
    coinductive_fixpoint
  end

  /--
    info: DifferentPredicateTypes.f.coinduct (pred_1 : Nat → Prop) (pred_2 : Nat → Nat → Prop)
  (hyp_1 : ∀ (x : Nat), pred_1 x → pred_2 (x + 1) (x + 2))
  (hyp_2 : ∀ (x x_1 : Nat), pred_2 x x_1 → pred_1 (x + 2) ∨ pred_2 (x_1 + 1) x_1) (x✝ : Nat) : pred_1 x✝ → f x✝
  -/
  #guard_msgs in
  #check f.coinduct
  /--
    info: DifferentPredicateTypes.f.mutual_induct (pred_1 : Nat → Prop) (pred_2 : Nat → Nat → Prop)
  (hyp_1 : ∀ (x : Nat), pred_1 x → pred_2 (x + 1) (x + 2))
  (hyp_2 : ∀ (x x_1 : Nat), pred_2 x x_1 → pred_1 (x + 2) ∨ pred_2 (x_1 + 1) x_1) :
  (∀ (x : Nat), pred_1 x → f x) ∧ ∀ (x x_1 : Nat), pred_2 x x_1 → g x x_1
  -/
  #guard_msgs in
  #check f.mutual_induct
  /--
    info: DifferentPredicateTypes.g.coinduct (pred_1 : Nat → Prop) (pred_2 : Nat → Nat → Prop)
  (hyp_1 : ∀ (x : Nat), pred_1 x → pred_2 (x + 1) (x + 2))
  (hyp_2 : ∀ (x x_1 : Nat), pred_2 x x_1 → pred_1 (x + 2) ∨ pred_2 (x_1 + 1) x_1) (x✝ x✝¹ : Nat) :
  pred_2 x✝ x✝¹ → g x✝ x✝¹
  -/
  #guard_msgs in
  #check g.coinduct
    /--
    info: DifferentPredicateTypes.g.mutual_induct (pred_1 : Nat → Prop) (pred_2 : Nat → Nat → Prop)
  (hyp_1 : ∀ (x : Nat), pred_1 x → pred_2 (x + 1) (x + 2))
  (hyp_2 : ∀ (x x_1 : Nat), pred_2 x x_1 → pred_1 (x + 2) ∨ pred_2 (x_1 + 1) x_1) :
  (∀ (x : Nat), pred_1 x → f x) ∧ ∀ (x x_1 : Nat), pred_2 x x_1 → g x x_1
  -/
  #guard_msgs in
  #check g.mutual_induct
end DifferentPredicateTypes
