theorem ex1 (p q r : Prop) (h1 : p ∨ q) (h2 : p → q) : q :=
  have : q := by -- Error here
    skip
  by skip -- Error here
     skip

theorem ex2 (p q r : Prop) (h1 : p ∨ q) (h2 : p → q) : q :=
  have : q := by {
    skip
  } -- Error here
  by skip -- Error here
     skip

theorem ex3 (p q r : Prop) (h1 : p ∨ q) (h2 : p → q) : q := by
  cases h1
  { skip
    skip } -- Error here
  { skip
    skip } -- Error here

theorem ex4 (p q r : Prop) (h1 : p ∨ q) (h2 : p → q) : q := by
  first | done | apply ex3 p q r h1 h2

theorem ex5 (p q r : Prop) (h1 : p ∨ q) (h2 : p → q) : q := by
  cases h1
  . skip  -- Error here
    skip
  . skip  -- Error here
    skip
