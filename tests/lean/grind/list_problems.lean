open List Nat

attribute [grind] List.getElem_cons_zero

attribute [grind] List.filter_nil List.filter_cons
attribute [grind] List.any_nil List.any_cons

@[simp] theorem any_filter {l : List α} {p q : α → Bool} :
    (filter p l).any q = l.any fun a => p a && q a := by
  induction l <;> grind
  -- Fails at:
  -- [grind] Goal diagnostics ▼
  -- [facts] Asserted facts ▼
  --   [prop] (filter p tail).any q = tail.any fun a => p a && q a
  --   [prop] ¬(filter p (head :: tail)).any q = (head :: tail).any fun a => p a && q a
  --   [prop] filter p (head :: tail) = if p head = true then head :: filter p tail else filter p tail
  --   [prop] ((head :: tail).any fun a => p a && q a) = (p head && q head || tail.any fun a => p a && q a)
  --   [prop] ¬p head = true
  -- [eqc] False propositions ▼
  --   [prop] (filter p (head :: tail)).any q = (head :: tail).any fun a => p a && q a
  --   [prop] p head = true
  -- [eqc] Equivalence classes ▼
  --   [] {(head :: tail).any fun a => p a && q a, p head && q head || tail.any fun a => p a && q a}
  --   [] {filter p (head :: tail), filter p tail, if p head = true then head :: filter p tail else filter p tail}
  --   [] {(filter p tail).any q, (filter p (head :: tail)).any q, tail.any fun a => p a && q a}
  -- Despite knowing that `p head = false`, grind doesn't see that
  -- `p head && q head || tail.any fun a => p a && q a = tail.any fun a => p a && q a`,
  -- which should finish the problem.
