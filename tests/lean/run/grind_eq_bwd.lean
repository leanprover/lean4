theorem dummy (x : Nat) : x = x :=
  rfl

/--
error: invalid pattern for `dummy`
  [@Lean.Grind.eqBwdPattern `[Nat] #0 #0]
the pattern does not contain constant symbols for indexing
-/
#guard_msgs in
attribute [grind ←=] dummy

def α : Type := sorry
def inv : α → α := sorry
def mul : α → α → α := sorry
def one : α := sorry

theorem inv_eq {a b : α} (w : mul a b = one) : inv a = b := sorry

/--
info: [grind.ematch.pattern] inv_eq: [@Lean.Grind.eqBwdPattern `[α] (inv #2) #1]
-/
#guard_msgs in
set_option trace.grind.ematch.pattern true in
attribute [grind ←=] inv_eq

example {a b : α} (w : mul a b = one) : inv a = b := by
  grind

example {a b : α} (w : mul a b = one) : inv a = b := by
  grind only [<-= inv_eq]

structure S where
  f : Bool → α
  h : mul (f true) (f false) = one
  h' : mul (f false) (f true) = one

attribute [grind =] S.h S.h'

example (s : S) : inv (s.f true) = s.f false := by
  grind

example (s : S) : inv (s.f true) = s.f false := by
  grind only [<-= inv_eq, = S.h]

example (s : S) : s.f false = inv (s.f true) := by
  grind

example (s : S) : a = false → s.f a = inv (s.f true) := by
  grind

example (s : S) : a ≠ s.f false → a = inv (s.f true) → False := by
  grind

/--
info: [grind.ematch.instance] inv_eq: mul (s.f true) (s.f false) = one → inv (s.f true) = s.f false
[grind.ematch.instance] S.h: mul (s.f true) (s.f false) = one
-/
#guard_msgs (info) in
set_option trace.grind.ematch.instance true in
example (s : S) : inv (s.f true) = s.f false := by
  grind
