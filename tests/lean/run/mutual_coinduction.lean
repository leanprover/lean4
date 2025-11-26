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
  (hyp_1 : ∀ (n : Nat), pred_1 n → pred_2 (n + 1) (n + 2))
  (hyp_2 : ∀ (n m : Nat), pred_2 n m → pred_1 (n + 2) ∨ pred_2 (m + 1) m) (n : Nat) : pred_1 n → f n
-/
#guard_msgs in
  #check f.coinduct
  /--
info: DifferentPredicateTypes.f.mutual_induct (pred_1 : Nat → Prop) (pred_2 : Nat → Nat → Prop)
  (hyp_1 : ∀ (n : Nat), pred_1 n → pred_2 (n + 1) (n + 2))
  (hyp_2 : ∀ (n m : Nat), pred_2 n m → pred_1 (n + 2) ∨ pred_2 (m + 1) m) :
  (∀ (n : Nat), pred_1 n → f n) ∧ ∀ (n m : Nat), pred_2 n m → g n m
-/
#guard_msgs in
  #check f.mutual_induct
  /--
info: DifferentPredicateTypes.g.coinduct (pred_1 : Nat → Prop) (pred_2 : Nat → Nat → Prop)
  (hyp_1 : ∀ (n : Nat), pred_1 n → pred_2 (n + 1) (n + 2))
  (hyp_2 : ∀ (n m : Nat), pred_2 n m → pred_1 (n + 2) ∨ pred_2 (m + 1) m) (n m : Nat) : pred_2 n m → g n m
-/
#guard_msgs in
  #check g.coinduct
end DifferentPredicateTypes
