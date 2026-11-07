/-!
The `Sym.simp`-based `grind` normalizer eta-reduces a lambda before simplifying its body:
`fun x => Nat.succ x` becomes `Nat.succ`, not `fun x => x + 1`, so it stays equal to an
unapplied `Nat.succ` elsewhere in the goal.
-/
set_option warn.sorry false
set_option backward.grind.normalizer false

section
variable (p : (Nat → Nat) → Prop) (f : Nat → Nat)

example : p (fun x => Nat.succ x) := by
  grind_norm sym; guard_target = p Nat.succ; sorry

example : p (fun x => f x) := by
  grind_norm sym; guard_target = p f; sorry

-- Not an eta-redex: the body is simplified.
example : p (fun x => Nat.succ (x + 0)) := by
  grind_norm sym; guard_target = p (fun x => x + 1); sorry

example : id (fun x => Nat.succ x) = id Nat.succ := by
  grind

example (h : p (fun x => Nat.succ x)) : p Nat.succ := by
  grind

-- Binder notations keep their bodies.
example (q : Nat → Nat → Prop) (r : Prop → Prop) : r (∃ y, q 0 y) := by
  grind_norm sym; guard_target = r (∃ y, q 0 y); sorry

example (q : Nat → Nat → Prop) (s : Type → Prop) : s {x // q 0 x} := by
  grind_norm sym; guard_target = s {x // q 0 x}; sorry

end

/-! `have` telescopes are simplified as beta-applications of lambdas; eta-reducing a lambda must
not interfere with that. -/
def f (a : Nat) (b : Bool) : Nat := if b then a else 0

example : (have a := 1 + 1; have b := true; have c := f a b; c = 2) := by
  grind [f]

def g (a b : Nat) : Nat := 2 * a + b

example : (have a := 1 + 1; have b := 3; have c := g a b; c = 7) := by
  grind [g]
