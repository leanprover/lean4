open List

attribute [grind =] getElem_cons_zero
attribute [grind =] getElem?_cons_zero

example (h : (a :: t)[0]? = some b) : (a :: t)[0] = b := by
  grind -- ✓

example [Inhabited α] : ∀ {l : List α} {i : Nat}, l[i]? = some b → l[i]! = b
  | a::t, 0, _ => by
    rw [getElem!_pos]
    · grind -- 'grind' failed, goals contains metavariables
    · sorry
  | _::l, _+1, e => sorry
