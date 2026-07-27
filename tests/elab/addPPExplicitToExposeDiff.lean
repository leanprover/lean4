/-!
# Tests of `addPPExplicitToExposeDiff`
-/
set_option pp.mvars false

/-!
Basic example.
-/
/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  1 = 2
-/
#guard_msgs in example : 1 = 2 := by
  exact rfl


/-!
Error message shouldn't fake a higher-order unification. This next one used to give
```
  type mismatch
    test n2 ?_
  has type
    (fun x ↦ x * 2) (g2 n2) = n2 : Prop
  but is expected to have type
    (fun x ↦ x * 2) (g2 n2) = n2 : Prop
```
It now doesn't for the stronger reason that we don't let `addPPExplicitToExposeDiff` have side effects,
but still it avoids doing incorrect higher-order unifications in its reasoning.
-/

theorem test {f g : Nat → Nat} (n : Nat) (hfg : ∀ a, f (g a) = a) :
    f (g n) = n := hfg n

/--
error: Type mismatch
  test n2 ?_
has type
  ?_ (?_ n2) = n2
but is expected to have type
  (fun x => x * 2) (g2 n2) = n2
-/
#guard_msgs in
example {g2 : Nat → Nat} (n2 : Nat) : (fun x => x * 2) (g2 n2) = n2 := by
  with_reducible refine test n2 ?_


/-!
Exposes an implicit argument because the explicit arguments can be unified.
-/
def f {a : Nat} (b : Nat) : Prop := a + b = 0
/--
error: Type mismatch
  sorry
has type
  @f 0 ?_
but is expected to have type
  @f 1 2
-/
#guard_msgs in
example : @f 1 2 := by
  exact (sorry : @f 0 _)

def myId {x : Nat} : Nat := x
def one : Nat := 1

/-!
Exposes an implicit argument nested inside an outer implicit argument because
the out explicit arguments can be unified, but the outer implicit argument
cannot, and its nested explicit arguments can be unified.
-/
/--
error: Type mismatch
  sorry
has type
  @f (@myId 1) 2
but is expected to have type
  @f (@myId one) 2
-/
#guard_msgs in
example : @f (myId (x := one)) 2 := by
  with_implicit exact (sorry : @f (myId (x := 1)) 2)

/-!
Add type ascriptions for numerals if they have different types.
-/
/--
error: Type mismatch
  Eq.refl 0
has type
  (0 : Int) = 0
but is expected to have type
  (0 : Nat) = 0
-/
#guard_msgs in example : 0 = (0 : Nat) := by
  exact Eq.refl (0 : Int)

-- Even if the numerals are different.
/--
error: Type mismatch
  Eq.refl 1
has type
  (1 : Int) = 1
but is expected to have type
  (0 : Nat) = 0
-/
#guard_msgs in example : 0 = (0 : Nat) := by
  exact Eq.refl (1 : Int)

-- Even for numerals that are functions
section
local instance {α : Type _} [OfNat β n] : OfNat (α → β) n where
  ofNat := fun _ => OfNat.ofNat n
/--
error: Type mismatch
  Eq.refl (0 1)
has type
  (0 : Nat → Int) 1 = 0 1
but is expected to have type
  (0 : Nat → Nat) 1 = 0 1
-/
#guard_msgs in example : (0 : Nat → Nat) 1 = (0 : Nat → Nat) 1 := by
  exact Eq.refl ((0 : Nat → Int) 1)
end

/-!
Exposes differences in pi type domains
-/
/--
error: Type mismatch
  fun h => trivial
has type
  (1 : Int) = 1 → True
but is expected to have type
  (1 : Nat) = 1 → True
-/
#guard_msgs in example : (1 : Nat) = 1 → True :=
  fun (h : (1 : Int) = 1) => trivial

/-!
Exposes differences in pi type codomains
-/
/--
error: Type mismatch
  fun h => rfl
has type
  True → (1 : Int) = 1
but is expected to have type
  True → (1 : Nat) = 1
-/
#guard_msgs in example : True → (1 : Nat) = 1 :=
  (fun h => rfl : True → (1 : Int) = 1)

/-!
Exposes differences in fun domains
-/
/--
error: Type mismatch
  sorry
has type
  { x : Int // x > 0 }
but is expected to have type
  { x : Nat // x > 0 }
-/
#guard_msgs in example : {x : Nat // x > 0} :=
  (sorry : {x : Int // x > 0})

/-!
Exposes differences in fun values
-/
/--
error: Type mismatch
  sorry
has type
  { x // @decide (p x) (d2 x) = true }
but is expected to have type
  { x // @decide (p x) (d1 x) = true }
-/
#guard_msgs in example (p : Nat → Prop) (d1 d2 : DecidablePred p) :
    {x : Nat // @decide _ (d1 x) = true} :=
  (sorry : {x : Nat // @decide _ (d2 x) = true})

/-!
`change` diagnoses at the transparency of the failed check.
-/
/--
error: 'change' tactic failed, pattern
  @f (@myId 1) 2
is not definitionally equal to target
  @f (@myId one) 2
-/
#guard_msgs in
example : @f (myId (x := one)) 2 := by
  with_reducible change @f (myId (x := 1)) 2

/-!
`#check_tactic` diagnoses at the reducible transparency of its check.
-/
/--
error: Term reduces to
  @myId one
but is expected to reduce to ⏎
  @myId 1
-/
#guard_msgs in
#check_tactic (myId (x := one)) ~> myId (x := 1) by skip

/-!
`#check_tactic` diagnoses at the reducible transparency of its check.
-/
/--
error: Term reduces to
  @f (@myId one) 2
but is expected to reduce to ⏎
  @f (@myId 1) 2
-/
#guard_msgs in
#check_tactic @f (myId (x := one)) 2 ~> @f (myId (x := 1)) 2 by skip

/-!
`rewrite` diagnoses at the transparency `kabstract` matched at.
-/
/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  @f (@myId 1) 2
in the target expression
  @f (@myId one) 2

h : f 2 = True
⊢ f 2
-/
#guard_msgs in
example (h : @f (@myId 1) 2 = True) : @f (myId (x := one)) 2 := by
  rewrite [h]

/-!
`apply` diagnoses at the configuration of the failed check.
-/
/--
error: Tactic `apply` failed: could not unify the type of `h`
  @f (@myId 1) 2
with the goal
  @f (@myId one) 2

h : f 2
⊢ f 2
-/
#guard_msgs in
example (h : @f (@myId 1) 2) : @f (myId (x := one)) 2 := by
  with_reducible apply h

/-!
`@[defeq]` diagnoses at the configuration of its defeq check (transparency `.all`), so the
diff is not attributed to `one'` vs. `1`, which are defeq at that transparency.
-/
axiom testSorry : α
@[irreducible] def one' : Nat := 1
opaque a : Nat
opaque b : Nat
opaque g : {_ : Nat} → Nat → Nat

/--
error: Not a definitional equality: the left-hand side
  @g a one'
is not definitionally equal to the right-hand side
  @g b 1
-/
#guard_msgs in
@[defeq] theorem gEq : @g a one' = @g b 1 := testSorry

/-!
`clear_value` diagnoses with assignable synthetic opaque metavariables, matching its check, so
the diff is attributed to `a` vs. `b` rather than to the assignable `?_`.
-/
/--
error: Provided term
  f ?_ ∧ @f b 2
is not definitionally equal to
  x := f 1 ∧ @f a 2
-/
#guard_msgs in
example : True := by
  let x : Prop := @f 1 1 ∧ @f a 2
  clear_value (h : x = (@f 1 ?_ ∧ @f b 2))
