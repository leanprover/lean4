reset_grind_attrs%

set_option trace.grind.ematch.pattern true

attribute [grind =] Array.size_set

set_option grind.debug true

example (as bs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        : as.size = bs.size := by
  grind

example (as bs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        : as.size = bs.size := by
  have : as.size = bs.size := by
    grind
  exact this

set_option trace.grind.ematch.instance true

attribute [grind =] Array.getElem_set_ne

/--
info: [grind.ematch.instance] Array.size_set: (as.set i v ⋯).size = as.size
[grind.ematch.instance] Array.getElem_set_ne: ∀ (pj : j < as.size), i ≠ j → (as.set i v ⋯)[j] = as[j]
-/
#guard_msgs (info) in
example (as bs cs : Array α) (v : α)
        (i : Nat)
        (h₁ : i < as.size)
        (h₂ : bs = as.set i v)
        (h₃ : cs = bs)
        (h₄ : i ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind


opaque R : Nat → Nat → Prop
theorem Rtrans (a b c : Nat) : R a b → R b c → R a c := sorry

grind_pattern Rtrans => R a b, R b c

/--
info: [grind.ematch.instance] Rtrans: R a b → R b c → R a c
-/
#guard_msgs (info) in
example : R a b → R b c → R a c := by
  grind


/--
info: [grind.ematch.instance] Rtrans: R a d → R d e → R a e
[grind.ematch.instance] Rtrans: R c d → R d e → R c e
[grind.ematch.instance] Rtrans: R b c → R c d → R b d
[grind.ematch.instance] Rtrans: R a b → R b c → R a c
[grind.ematch.instance] Rtrans: R a c → R c d → R a d
[grind.ematch.instance] Rtrans: R a c → R c e → R a e
[grind.ematch.instance] Rtrans: R b d → R d e → R b e
[grind.ematch.instance] Rtrans: R a b → R b d → R a d
[grind.ematch.instance] Rtrans: R b c → R c e → R b e
-/
#guard_msgs (info) in
example : R a b → R b c → R c d → R d e → R a d := by
  grind


namespace using_grind_fwd

opaque S : Nat → Nat → Prop

/--
error: `@[grind →] theorem using_grind_fwd.StransBad` failed to find patterns in the antecedents of the theorem, consider using different options or the `grind_pattern` command
-/
#guard_msgs (error) in
@[grind→] theorem StransBad (a b c d : Nat) : S a b ∨ R a b → S b c → S a c ∧ S b d := sorry


set_option trace.grind.ematch.pattern.search true in
/--
info: [grind.ematch.pattern.search] candidate: S a b
[grind.ematch.pattern.search] found pattern: S #4 #3
[grind.ematch.pattern.search] candidate: R a b
[grind.ematch.pattern.search] skip, no new variables covered
[grind.ematch.pattern.search] candidate: S b c
[grind.ematch.pattern.search] found pattern: S #3 #2
[grind.ematch.pattern.search] found full coverage
[grind.ematch.pattern] Strans: [S #4 #3, S #3 #2]
-/
#guard_msgs (info) in
@[grind→] theorem Strans (a b c : Nat) : S a b ∨ R a b → S b c → S a c := sorry

/--
info: [grind.ematch.instance] Strans: S a b ∨ R a b → S b c → S a c
-/
#guard_msgs (info) in
example : S a b → S b c → S a c := by
  grind

end using_grind_fwd

namespace using_grind_bwd

opaque P : Nat → Prop
opaque Q : Nat → Prop
opaque f : Nat → Nat → Nat

/-- info: [grind.ematch.pattern] pqf: [f #2 #1] -/
#guard_msgs (info) in
@[grind←] theorem pqf : Q x → P (f x y) := sorry

/--
info: [grind.ematch.instance] pqf: Q a → P (f a b)
-/
#guard_msgs (info) in
example : Q 0 → Q 1 → Q 2 → Q 3 → ¬ P (f a b) → a = 1 → False := by
  grind

end using_grind_bwd

namespace using_grind_fwd2

opaque P : Nat → Prop
opaque Q : Nat → Prop
opaque f : Nat → Nat → Nat

/--
error: `@[grind →] theorem using_grind_fwd2.pqfBad` failed to find patterns in the antecedents of the theorem, consider using different options or the `grind_pattern` command
-/
#guard_msgs (error) in
@[grind→] theorem pqfBad : Q x → P (f x y) := sorry

/--
info: [grind.ematch.pattern] pqf: [Q #1]
-/
#guard_msgs (info) in
@[grind→] theorem pqf : Q x → P (f x x) := sorry

/--
info: [grind.ematch.instance] pqf: Q 3 → P (f 3 3)
[grind.ematch.instance] pqf: Q 2 → P (f 2 2)
[grind.ematch.instance] pqf: Q 1 → P (f 1 1)
[grind.ematch.instance] pqf: Q 0 → P (f 0 0)
-/
#guard_msgs (info) in
example : Q 0 → Q 1 → Q 2 → Q 3 → ¬ P (f a a) → a = 1 → False := by
  grind

end using_grind_fwd2

namespace using_grind_mixed

opaque P : Nat → Nat → Prop
opaque Q : Nat → Nat → Prop

/--
error: `@[grind →] theorem using_grind_mixed.pqBad1` failed to find patterns in the antecedents of the theorem, consider using different options or the `grind_pattern` command
-/
#guard_msgs (error) in
@[grind→] theorem pqBad1 : P x y → Q x z := sorry

/--
error: `@[grind ←] theorem using_grind_mixed.pqBad2` failed to find patterns in the theorem's conclusion, consider using different options or the `grind_pattern` command
-/
#guard_msgs (error) in
@[grind←] theorem pqBad2 : P x y → Q x z := sorry


/--
info: [grind.ematch.pattern] pqBad: [Q #3 #1, P #3 #2]
-/
#guard_msgs (info) in
@[grind] theorem pqBad : P x y → Q x z := sorry

example : P a b → Q a c := by
  grind

end using_grind_mixed


namespace using_grind_rhs

opaque f : Nat → Nat
opaque g : Nat → Nat → Nat

/--
info: [grind.ematch.pattern] fq: [g #0 (f #0)]
-/
#guard_msgs (info) in
@[grind =_]
theorem fq : f x = g x (f x) := sorry

end using_grind_rhs

namespace using_grind_lhs_rhs

opaque f : Nat → Nat
opaque g : Nat → Nat → Nat

/--
info: [grind.ematch.pattern] fq: [f #0]
[grind.ematch.pattern] fq: [g #0 (g #0 #0)]
-/
#guard_msgs (info) in
@[grind _=_]
theorem fq : f x = g x (g x x) := sorry

end using_grind_lhs_rhs

-- the following should still work
#check _=_
