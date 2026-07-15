module
/--
trace: [grind.eqResolution] ∀ (x : Nat), p x a → ∀ (y : Nat), p y b → ¬x = y, ∀ (y : Nat), p y a → p y b → False
[grind.ematch.instance] h: p c a → p c b → c ≠ c
[grind.ematch.instance] local_0: p c a → ¬p c b
-/
#guard_msgs (trace) in
example
    (p : Nat → Nat → Prop)
    (a b c : Nat)
    (h : ∀ x, p x a → ∀ y, p y b → x ≠ y)
    (h₁ : p c a)
    (h₂ : p c b)
    : False := by
  set_option trace.grind.eqResolution true in
  set_option trace.grind.ematch.instance true in
  grind

example
    (f : Nat → Nat)
    (h : ∀ x y, f x = f y → x = y)
    : f (f a) = f (f b) → a = b := by
  grind only
