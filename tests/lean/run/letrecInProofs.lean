import Lean

inductive Tree
  | leaf : Tree
  | node : Tree → Tree → Tree

abbrev notLtX (x : Tree) (t : Tree) : Prop :=
  Tree.ibelow (motive := fun z => x ≠ z) t

theorem Tree.acyclic (x t : Tree) : x = t → notLtX x t := by
  let rec right (x s : Tree) (b : Tree) (h : notLtX x b) : node s x ≠ b ∧ notLtX (node s x) b := by
    match b, h with
    | leaf,     h =>
      apply And.intro _ trivial
      intro h; injection h
    | node l r, h =>
      have ihl : notLtX x l → node s x ≠ l ∧ notLtX (node s x) l from right x s l
      have ihr : notLtX x r → node s x ≠ r ∧ notLtX (node s x) r from right x s r
      have hl : x ≠ l ∧ notLtX x l from h.1
      have hr : x ≠ r ∧ notLtX x r from h.2.1
      have ihl : node s x ≠ l ∧ notLtX (node s x) l from ihl hl.2
      have ihr : node s x ≠ r ∧ notLtX (node s x) r from ihr hr.2
      apply And.intro
      focus
        intro h
        injection h with _ h
        exact absurd h hr.1
        done
      focus
        apply And.intro
        apply ihl
        apply And.intro _ trivial
        apply ihr
  let rec left (x t : Tree) (b : Tree) (h : notLtX x b) : node x t ≠ b ∧ notLtX (node x t) b := by
    match b, h with
    | leaf, h     =>
      apply And.intro _ trivial
      intro h; injection h
    | node l r, h =>
      have ihl : notLtX x l → node x t ≠ l ∧ notLtX (node x t) l from left x t l
      have ihr : notLtX x r → node x t ≠ r ∧ notLtX (node x t) r from left x t r
      have hl : x ≠ l ∧ notLtX x l from h.1
      have hr : x ≠ r ∧ notLtX x r from h.2.1
      have ihl : node x t ≠ l ∧ notLtX (node x t) l from ihl hl.2
      have ihr : node x t ≠ r ∧ notLtX (node x t) r from ihr hr.2
      apply And.intro
      focus
        intro h
        injection h with h _
        exact absurd h hl.1
        done
      focus
        apply And.intro
        apply ihl
        apply And.intro _ trivial
        apply ihr
  let rec aux : (x : Tree) → notLtX x x
    | leaf     => trivial
    | node l r => by
        have ih₁ : notLtX l l from aux l
        have ih₂ : notLtX r r from aux r
        show (node l r ≠ l ∧ notLtX (node l r) l) ∧ (node l r ≠ r ∧ notLtX (node l r) r) ∧ True
        apply And.intro
        focus
          apply left
          assumption
        apply And.intro _ trivial
        focus
          apply right
          assumption
  intro h
  subst h
  apply aux

open Tree

theorem ex1 (x : Tree) : x ≠ node leaf (node x leaf) := by
  intro h
  exact absurd rfl $ Tree.acyclic _ _ h $.2.1.2.1.1

theorem ex2 (x : Tree) : x ≠ node x leaf := by
  intro h
  exact absurd rfl $ Tree.acyclic _ _ h $.1.1

theorem ex3 (x y : Tree) : x ≠ node y x := by
  intro h
  exact absurd rfl $ Tree.acyclic _ _ h $.2.1.1
