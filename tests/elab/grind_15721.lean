/-!
Regression test for #15721: `grind` built an ill-typed proof when propagating equations between
constant functions whose equivalence classes contain more than one lambda.
-/

example (q r : Prop) (h₁ : (fun _ : Nat => True) = fun _ => q)
    (h₂ : (fun _ : Nat => False) = fun _ => r) (h₃ : (fun _ : Nat => q) = fun _ => r) : False := by
  grind

example (p q : Prop) (f g h : Unit → Prop)
    (h₁ : f = fun _ => p) (h₂ : f = fun _ => q)
    (h₃ : g = fun _ => True) (h₄ : g = h) (h₅ : f = g) : p := by
  grind

def D := Nat

example (q : Prop) (h₁ : (fun _ : Nat => False) = fun _ : D => q)
    (h₂ : (fun _ : D => q) = fun _ : Nat => True) : False := by
  grind

example (p q : Prop) (h₁ : (fun _ : Nat => p) = fun _ => True)
    (h₂ : (fun _ : Nat => q) = fun _ => False) (h₃ : (fun _ : Nat => p) = fun _ => q) : False := by
  grind
