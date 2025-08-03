example (h : (fun (_ : Unit) => x = 1) = (fun _ => True)) : x = 1 := by
  grind

example
    (h₁ : f = fun (_ : Unit) => x = 1)
    (h₂ : g = fun (_ : Unit) => True)
    (h₃ : f = g)
    : x = 1 := by
  grind

example
    (h₁ : f = fun (_ : Unit × Unit) => x = 1)
    (h₂ : g = fun (_ : Unit × Unit) => True)
    (h₃ : f = g)
    : x = 1 := by
  grind

example (h : (fun (_ : True → Unit) (_ : Unit) => x + 1) = (fun _ _ => 1 + y)) : x = y := by
  grind

example (h : (fun (_ : Unit) => x + 1) = (fun _ => 1 + y)) : x = y := by
  grind

example (h : (fun (_ : Unit → Unit) => x + 1) = (fun _ => 1 + y)) : x = y := by
  grind

example
    (x y z : Nat)
    (h₁ : f = fun (_ : Unit × Unit) => x + y)
    (h₂ : g = fun (_ : Unit × Unit) => w)
    (h₃ : f = g)
    (h₄ : f = fun (_ : Unit × Unit) => y + z)
    : x = z ∧ x + y = w := by
  grind
