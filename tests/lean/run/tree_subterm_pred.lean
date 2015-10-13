import logic
open eq.ops

inductive tree (A : Type) :=
| leaf : A → tree A
| node : tree A → tree A → tree A

namespace tree

inductive direct_subterm {A : Type} : tree A → tree A → Prop :=
| node_l : Π (l r : tree A), direct_subterm l (node l r)
| node_r : Π (l r : tree A), direct_subterm r (node l r)

definition direct_subterm.wf {A : Type} : well_founded (@direct_subterm A) :=
well_founded.intro (λ t : tree A,
  tree.rec_on t
    (λ (a : A), acc.intro (leaf a) (λ (s : tree A) (H : direct_subterm s (leaf a)),
       have gen : ∀ r : tree A, direct_subterm s r → r = leaf a → acc direct_subterm s, from
         λ r H, direct_subterm.rec_on H (λ l r e, tree.no_confusion e) (λ l r e, tree.no_confusion e),
       gen (leaf a) H rfl))
    (λ (l r : tree A) (ihl : acc direct_subterm l) (ihr : acc direct_subterm r),
      acc.intro (node l r) (λ (s : tree A) (H : direct_subterm s (node l r)),
        have gen : ∀ n₁ : tree A, direct_subterm s n₁ → node l r = n₁ → acc direct_subterm s, from
          λ n₁ H, direct_subterm.rec_on H
           (λ (l' r' : tree A) (Heq : node l r = node l' r'), tree.no_confusion Heq (λ leq req, eq.rec_on leq ihl))
           (λ (l' r' : tree A) (Heq : node l r = node l' r'), tree.no_confusion Heq (λ leq req, eq.rec_on req ihr)),
        gen (node l r) H rfl)))

definition direct_subterm.wf₂ {A : Type} : well_founded (@direct_subterm A) :=
begin
  constructor, intro t, induction t,
  repeat (constructor; intro y hlt; cases hlt; repeat assumption)
end

definition subterm {A : Type} : tree A → tree A → Prop := tc (@direct_subterm A)

definition subterm.wf {A : Type} : well_founded (@subterm A) :=
tc.wf (@direct_subterm.wf A)
open nat
example : subterm (leaf (2:nat)) (node (leaf 1) (leaf 2)) :=
!tc.base !direct_subterm.node_r

example : subterm (leaf (2:nat)) (node (node (leaf 1) (leaf 2)) (leaf 3)) :=
have s₁ : subterm (leaf 2) (node (leaf 1) (leaf 2)), from
  !tc.base !direct_subterm.node_r,
have s₂ : subterm (node (leaf 1) (leaf 2)) (node (node (leaf 1) (leaf 2)) (leaf 3)), from
  !tc.base !direct_subterm.node_l,
!tc.trans s₁ s₂

end tree
