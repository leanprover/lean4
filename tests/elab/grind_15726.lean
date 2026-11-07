/-!
Regression test for #15726: `grind` must not internalize heterogeneous arithmetic applications
(e.g., `c * xs` with `c : Nat` and `xs : Vector Nat n`) as terms of the scalar type.
-/

example {n : Nat} (c : Nat) (xs ys : Vector Nat n) (h : c * (xs + ys) = c * xs + c * ys) :
    c * (xs + ys) = c * xs + c * ys := by grind

example {n : Nat} (c : Nat) (xs ys zs : Vector Nat n) (h₁ : c * xs = zs) (h₂ : zs = c * ys) :
    c * xs = c * ys := by grind

example {n : Nat} (c : Int) (xs ys : Vector Int n) (h : c * (xs + ys) = c * xs + c * ys) :
    c * (xs + ys) = c * xs + c * ys := by grind

structure Foo where
  x : Nat

instance : HAdd Nat Foo Foo := ⟨fun a f => ⟨a + f.x⟩⟩
instance : HSub Nat Foo Foo := ⟨fun a f => ⟨a - f.x⟩⟩
instance : HPow Nat Nat Foo := ⟨fun a _ => ⟨a⟩⟩

example (c : Nat) (a b : Foo) (h : c + a = b) : c + a = b := by grind
example (c : Nat) (a b : Foo) (h : c - a = b) : c - a = b := by grind
example (c k : Nat) (b : Foo) (h : c ^ k = b) : c ^ k = b := by grind
example (c : Nat) (a b : Foo) (h : c + a = b) : c + a = b := by grind -ring
example (c : Nat) (a b : Foo) (h : c + a = b) : c + a = b := by grind -lia
