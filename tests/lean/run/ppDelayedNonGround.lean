/-!
This test case tests the flag `pp.mvars.delayedNonGround`.
It is an extract of the test cases `funParen.lean`, `4144.lean`, `match1.lean` and
`anonymous_constructor_error_msg.lean`, the output of which differs when the flag is on.
By default it is off, so as long as that is the case we should keep this test case.

Note that the difference in output is simply that more metavariables show up as `sorry` instead
of random synthetic opaque metavariables (with `pp.mvars.delayed` set to true) or their
randomly named root synthetic opaque metavariables (with `pp.mvars.delayed` set to false).
Witness by setting the flag below to `false`.
-/

set_option pp.mvars.delayedNonGround true

/--
error: Invalid match expression: The type of pattern variable 'a' contains metavariables:
  ?m.12
---
info: fun x => sorry : ?m.12 × ?m.13 → ?m.12
-/
#guard_msgs in
#check fun (a, b) => a

/--
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`
---
info: fun x => sorry : (x : ?m.1) → ?m.4 x
-/
#guard_msgs in
#check fun (x id) => x

/--
error: Invalid projection: Type of
  x✝
is not known; cannot resolve projection `1`
---
error: unsolved goals
case refine'_1
⊢ Sort ?u.104

case refine'_2
⊢ Sort ?u.103

case refine'_3
⊢ ?refine'_1

case refine'_4
⊢ ?refine'_1

case refine'_5
⊢ ¬(fun x => sorry) ?refine'_3 = (fun x => sorry) ?refine'_4
-/
#guard_msgs in
example : False := by
  refine' absurd (congrArg (·.1) sorry) _

structure Foo := (n : Nat)

def Foo.sum (xs : List Foo) : Foo :=
xs.foldl (λ s x => ⟨s.n + x.n⟩) ⟨0⟩

/--
error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
---
info: let x1 := { n := 1 };
let x2 := { n := 2 };
let x3 := { n := 3 };
let x4 := sorry;
let x5 := { n := 5 };
let x6 := { n := 6 };
Foo.sum [x1, x2, x3, x5, x6] : Foo
-/
#guard_msgs in
#check
let x1 := ⟨1⟩
let x2 := ⟨2⟩
let x3 := ⟨3⟩
let x4 := ⟨4⟩; -- If this line is uncommented we get the error at `⟨`
let x5 := ⟨5⟩
let x6 := ⟨6⟩
Foo.sum [x1, x2, x3, x5, x6]
