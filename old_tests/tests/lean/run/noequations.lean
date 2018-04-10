example : empty → false.

def f := empty → false
example : f.

def g := ∀ (a : nat) (h : a = a), @eq.rec nat a (λ x, Prop) (empty → false) a h

example : g.
