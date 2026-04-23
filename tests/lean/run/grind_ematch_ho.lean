module
reset_grind_attrs%
public section
set_option trace.grind.ematch.pattern true
set_option warn.sorry false

/-! # Higher-order E-matching tests

These tests verify the HO pattern matching feature. When a pattern contains a
lambda whose body applies pattern variables to distinct lambda-bound variables
(Miller condition), it is wrapped as `ho[...]` and matched via `isDefEq` at
instantiation time rather than the E-graph.

Lambdas of the form `fun x => f x` are eta-reduced during pattern preprocessing,
so they never reach the HO handler. These tests use non-eta-reducible lambdas.
-/

/-! ## Basic: lambda with argument reordering (non-eta-reducible) -/

opaque applyFlip : (Nat → Nat → Nat) → Nat → Nat → Nat

/-- trace: [grind.ematch.pattern] applyFlip_spec: [applyFlip ho[fun x => fun y => #2 y x] #1 #0] -/
#guard_msgs (trace, warning) in
@[grind =] theorem applyFlip_spec (f : Nat → Nat → Nat) (a b : Nat)
    : applyFlip (fun x y => f y x) a b = f b a := sorry

example (h : applyFlip (fun x y => Nat.add y x) 3 4 = 42) : Nat.add 4 3 = 42 := by
  grind

/-! ## Partial application: lambda uses only some lambda-bound vars -/

opaque applyConst : (Nat → Nat → Nat) → Nat → Nat → Nat

/-- trace: [grind.ematch.pattern] applyConst_spec: [applyConst ho[fun x => fun _ => #2 x] #1 #0] -/
#guard_msgs (trace, warning) in
@[grind =] theorem applyConst_spec (f : Nat → Nat) (a b : Nat)
    : applyConst (fun x _ => f x) a b = f a := sorry

example (h : applyConst (fun x _ => x + 1) 5 10 = 42) : 6 = 42 := by
  grind

/-! ## Non-Miller rejection: fun x => g (x + 1) fails Miller → dontCare -/

-- `g (x + 1)` means the argument to `g` is not a bare bvar → Miller fails.
-- With dontCare, `g` is not covered on the LHS nor RHS.
-- This theorem can still be tagged with `@[grind .]` which finds a multi-pattern.
opaque applyMod : (Nat → Nat) → Nat → Nat

theorem applyMod_spec (g : Nat → Nat) (a : Nat)
    : applyMod (fun x => g (x + 1)) a = g (a + 1) := sorry

/-! ## Pattern variable in both HO and FO positions -/

opaque applyWith : (Nat → Nat → Nat) → Nat → Nat → Nat → Nat

/--
trace: [grind.ematch.pattern] applyWith_spec: [applyWith ho[fun x => fun y => #3 y x] #2 #1 #0]
-/
#guard_msgs (trace, warning) in
@[grind =] theorem applyWith_spec (f : Nat → Nat → Nat) (a b c : Nat)
    : applyWith (fun x y => f y x) a b c = f b a + c := sorry

example (h : applyWith (fun x y => Nat.add y x) 1 2 3 = 42) : Nat.add 2 1 + 3 = 42 := by
  grind

/-! ## Realistic example: foldl with flipped cons -/

-- The lambda `fun xs y => y :: xs` doesn't need HO matching (no pattern variable
-- in Miller position — only `α` appears as a bare bvar). First-order matching with
-- dontCare suffices since the lambda is alpha-equivalent to the one in the goal.
/-- trace: [grind.ematch.pattern] foldl_flip_cons_eq_append': [@List.foldl (List #2) _ _ #0 #1] -/
#guard_msgs (trace, warning) in
@[grind =] theorem foldl_flip_cons_eq_append' {l l' : List α}
    : l.foldl (fun xs y => y :: xs) l' = l.reverse ++ l' := sorry

example (xs ys : List Nat) (h : xs.foldl (fun a b => b :: a) ys = [1, 2, 3])
    : xs.reverse ++ ys = [1, 2, 3] := by
  grind



end
