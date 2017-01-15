universe variables u

inductive tree (α : Type u)
| leaf {} : tree
| node    : tree → α → tree → tree

open tree

def tree.size {α : Type u} : tree α → nat
| leaf := 0
| (node l a r) := tree.size l + tree.size r + 1

vm_eval tree.size (@leaf nat)
vm_eval tree.size (tree.node leaf 1 leaf)
vm_eval tree.size (tree.node (tree.node leaf 1 leaf) 2 leaf)

lemma ex1 : tree.size (tree.node (tree.node leaf 1 leaf) 2 leaf) = 2 :=
rfl

def tree.elems_core {α : Type u} : tree α → list α → list α
| leaf lst := lst
| (node l a r) lst :=
  let lst₁ := tree.elems_core l lst,
      lst₂ := a :: lst₁
  in tree.elems_core r lst₂

def tree.elems {α : Type u} (t : tree α) : list α :=
(tree.elems_core t [])^.reverse

vm_eval tree.elems (tree.node (tree.node (tree.node leaf 0 leaf) 1 leaf) 2 leaf)

lemma ex2 : tree.elems (tree.node (tree.node (tree.node leaf 0 leaf) 1 leaf) 2 leaf) = [0, 1, 2] :=
rfl

lemma ex3 (t₁ t₂ : tree nat) : t₁ = leaf → t₂ = node leaf 1 leaf → t₁ ≠ t₂ :=
begin [smt]
  intros
end

lemma ex4 (t₁ t₂ : tree nat) : t₁ = leaf → t₂ = node leaf 1 leaf → t₁ ≠ t₂ :=
begin
  intros,
  subst t₁, subst t₂,
  tactic.intro1,
  contradiction
end

lemma ex5 (a b : nat) (t₁ t₂ t₃ t₄ : tree nat) : node t₁ a t₂ = node t₃ b t₄ →
                                                 t₁ = t₃ ∧ a = b ∧ t₂ = t₄ :=
begin [smt]
  intros
end

lemma ex6 (a b : nat) (t₁ t₂ t₃ t₄ : tree nat) : node t₁ a t₂ = node t₃ b t₄ →
                                                 t₁ = t₃ ∧ a = b ∧ t₂ = t₄ :=
begin
  intro h,
  injection h with h₁ h₂ h₃,
  split, assumption, split, assumption, assumption
end

lemma ex7 {α : Type u} (t : tree α) : t ≠ leaf → tree.size t > 0 :=
begin
  induction t,
  {intros, contradiction},
  {intros, unfold size, apply nat.zero_lt_succ }
end

inductive tree_list (α : Type u)
| leaf : tree_list
| node : list tree_list → α → tree_list
