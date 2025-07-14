-- set_option trace.Elab.definition.partialFixpoint.induction true

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
    info: MutualCoinduction.f.coinduct (x : Prop ×' Prop) (y : (x.1 → x.2) ∧ (x.2 → x.1)) : (x.1 → f) ∧ (x.2 → g)
  -/
  #guard_msgs in
  #check MutualCoinduction.f.coinduct
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
    info: MutualInduction.f.induct (x : Prop ×' Prop) (y : (x.2 → x.1) ∧ (x.1 → x.2)) : (f → x.1) ∧ (g → x.2)
  -/
  #guard_msgs in
  #check MutualInduction.f.induct
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
    info: MixedInductionCoinduction.f.induct (x : Prop ×' Prop) (y : ((x.2 → x.1) → x.1) ∧ (x.2 → x.1 → x.2)) :
  (f → x.1) ∧ (x.2 → g)
  -/
  #guard_msgs in
  #check f.induct

    /--
    info: MixedInductionCoinduction.g.coinduct (x : Prop ×' Prop) (y : ((x.2 → x.1) → x.1) ∧ (x.2 → x.1 → x.2)) :
  (f → x.1) ∧ (x.2 → g)
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

  def pred1 := fun m : Nat => True
  def pred2 := fun m n : Nat => True

  #check f.coinduct

  /--
    info: DifferentPredicateTypes.f.coinduct (x : (Nat → Prop) ×' (Nat → Nat → Prop))
  (y :
    (∀ (x_1 : Nat), x.1 x_1 → x.2 (x_1 + 1) (x_1 + 2)) ∧
      ∀ (x_1 x_2 : Nat), x.2 x_1 x_2 → x.1 (x_1 + 2) ∨ x.2 (x_2 + 1) x_2) :
  (∀ (x_1 : Nat), x.1 x_1 → f x_1) ∧ ∀ (x_1 x_2 : Nat), x.2 x_1 x_2 → g x_1 x_2
  -/
  #guard_msgs in
  #check f.coinduct


end DifferentPredicateTypes
