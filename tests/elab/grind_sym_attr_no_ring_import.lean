prelude
import Init.Core
import Init.Data.Nat.Basic

/-!
`@[grind]` attributes with the `Sym.simp`-based normalizer in a module that does not import the
`Lean.Grind.CommRing`/`CommSemiring` classes. The arithmetic normalizer used to query these classes
unconditionally and failed with `Unknown constant`.
-/

set_option backward.grind.normalizer false
set_option warn.sorry false
set_option trace.grind.ematch.pattern true

axiom P : Nat → Prop
axiom f : Nat → Nat
axiom g : Bool → Bool
/-- trace: [grind.ematch.pattern] t0: [f #0] -/
#guard_msgs in
@[grind =] theorem t0 (x : Nat) : f x = x := sorry
/-- trace: [grind.ematch.pattern] t1: [g #0] -/
#guard_msgs in
@[grind =] theorem t1 (x : Bool) : g x = x := sorry
/-- trace: [grind.ematch.pattern] t2: [f (#0 + 1)] -/
#guard_msgs in
@[grind =] theorem t2 (x : Nat) : f (x + 1) = f x := sorry
/-- trace: [grind.ematch.pattern] t3: [P (f #0)] -/
#guard_msgs in
@[grind .] theorem t3 (x : Nat) : P (f x) := sorry
/-- trace: [grind.ematch.pattern] t4: [P (f #0)] -/
#guard_msgs in
@[grind .] theorem t4 (x : Nat) : P (f x) ∧ True := sorry
/-- trace: [grind.ematch.pattern] t5: [P (@HSub.hSub `[Nat] `[Nat] `[Nat] `[instHSub] (@HAdd.hAdd `[Nat] `[Nat] `[Nat] `[instHAdd] #1 #0) #1)] -/
#guard_msgs in
@[grind .] theorem t5 (x y : Nat) : P (x + y - x) := sorry
