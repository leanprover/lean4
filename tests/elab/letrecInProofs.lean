import Lean

inductive Tree
  | leaf : Tree
  | node : Tree → Tree → Tree

abbrev notSubtree (x : Tree) (t : Tree) : Prop :=
  t.rec True fun l r l_ih r_ih => (x ≠ l ∧ l_ih) ∧ (x ≠ r ∧ r_ih)

infix:50 "≮" => notSubtree

theorem Tree.acyclic (x t : Tree) : x = t → x ≮ t := by
  let rec right (x s : Tree) (b : Tree) (h : x ≮ b) : node s x ≠ b ∧ node s x ≮ b := by
    match b, h with
    | leaf,     h =>
      apply And.intro _ trivial
      intro h; injection h
    | node l r, h =>
      have ihl : x ≮ l → node s x ≠ l ∧ node s x ≮ l := right x s l
      have ihr : x ≮ r → node s x ≠ r ∧ node s x ≮ r := right x s r
      have hl : x ≠ l ∧ x ≮ l := h.1
      have hr : x ≠ r ∧ x ≮ r := h.2
      have ihl : node s x ≠ l ∧ node s x ≮ l := ihl hl.2
      have ihr : node s x ≠ r ∧ node s x ≮ r := ihr hr.2
      apply And.intro
      focus
        intro h
        injection h with _ h
        exact absurd h hr.1
        done
      focus
        apply And.intro
        apply ihl
        apply ihr
  let rec left (x t : Tree) (b : Tree) (h : x ≮ b) : node x t ≠ b ∧ node x t ≮ b := by
    match b, h with
    | leaf, h     =>
      apply And.intro _ trivial
      intro h; injection h
    | node l r, h =>
      have ihl : x ≮ l → node x t ≠ l ∧ node x t ≮ l := left x t l
      have ihr : x ≮ r → node x t ≠ r ∧ node x t ≮ r := left x t r
      have hl : x ≠ l ∧ x ≮ l := h.1
      have hr : x ≠ r ∧ x ≮ r := h.2
      have ihl : node x t ≠ l ∧ node x t ≮ l := ihl hl.2
      have ihr : node x t ≠ r ∧ node x t ≮ r := ihr hr.2
      apply And.intro
      focus
        intro h
        injection h with h _
        exact absurd h hl.1
        done
      focus
        apply And.intro
        apply ihl
        apply ihr
  let rec aux : (x : Tree) → x ≮ x
    | leaf     => trivial
    | node l r => by
        have ih₁ : l ≮ l := aux l
        have ih₂ : r ≮ r := aux r
        show (node l r ≠ l ∧ node l r ≮ l) ∧ (node l r ≠ r ∧ node l r ≮ r)
        apply And.intro
        focus
          apply left
          assumption
        focus
          apply right
          assumption
  intro h
  subst h
  apply aux

open Tree

theorem ex1 (x : Tree) : x ≠ node leaf (node x leaf) := by
  intro h
  exact absurd rfl $ Tree.acyclic _ _ h |>.2.2.1.1

theorem ex2 (x : Tree) : x ≠ node x leaf := by
  intro h
  exact absurd rfl $ Tree.acyclic _ _ h |>.1.1

theorem ex3 (x y : Tree) : x ≠ node y x := by
  intro h
  exact absurd rfl $ Tree.acyclic _ _ h |>.2.1
