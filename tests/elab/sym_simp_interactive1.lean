import Lean

/-! Tests for interactive `simp` tactic in `sym =>` mode -/

theorem test_zero_add : 0 + n = n := Nat.zero_add n
theorem test_add_zero : n + 0 = n := Nat.add_zero n

/-! ## Test 1: `simp` with named variant -/

register_sym_simp testNatSimp where
  post := rewrite [test_zero_add, test_add_zero]

example (x : Nat) : 0 + x = x := by
  sym =>
    simp testNatSimp
    tactic => rfl

/-! ## Test 2: named variant simplifies compound expression -/

example (x : Nat) : 0 + (x + 0) = x := by
  sym =>
    simp testNatSimp
    tactic => rfl

/-! ## Test 3: named variant with extra theorems -/

theorem test_succ_add : Nat.succ n + m = Nat.succ (n + m) := Nat.succ_add n m

example (x : Nat) : 0 + (Nat.succ 0 + x) = Nat.succ (0 + x) := by
  sym =>
    simp testNatSimp [test_succ_add]
    tactic => rfl

/-! ## Test 4: variant with ground evaluation (closes goal) -/

register_sym_simp groundSimp where
  post := ground

example : (3 + 4 : Nat) = 7 := by
  sym =>
    simp groundSimp

/-! ## Test 5: variant with pre and post (ground in pre closes via evalGround in default) -/

register_sym_simp prePostSimp where
  pre  := ground
  post := rewrite [test_zero_add]

example (x : Nat) : 0 + x = x := by
  sym =>
    simp prePostSimp

/-! ## Test 6: bare `simp` uses default methods (with `@[sym_simp]` set) -/

attribute [sym_simp] test_zero_add

example (x : Nat) : 0 + x = x := by
  sym =>
    simp

/-! ## Test 7: unknown variant produces error -/

/--
error: unknown Sym.simp variant `nonExistent`
-/
#guard_msgs in
example (x : Nat) : 0 + x = x := by
  sym =>
    simp nonExistent

/-! ## Test 8: `simp` with `>>` combinator in variant -/

register_sym_simp chainSimp where
  post := ground >> rewrite [test_zero_add]

example (x : Nat) : 0 + x = x := by
  sym =>
    simp chainSimp

/-! ## Test 9: repeated simp shares cache -/

example (x y : Nat) : 0 + x = x ∧ 0 + y = y := by
  sym =>
    apply And.intro
    · simp testNatSimp; tactic => rfl
    · simp testNatSimp; tactic => rfl

/-! ## Test 10: verify persistent cache is shared across `simp` invocations.
The second `simp` should hit the persistent cache for shared subterms like `0`.
Enable trace to confirm (run manually to inspect). -/

register_sym_simp simple where
  post := ground >> rewrite [Nat.zero_add, Nat.add_zero, true_and, and_true]

/--
trace: [sym.simp.debug.cache] persistent cache hit: x
[sym.simp.debug.cache] persistent cache hit: x
[sym.simp.debug.cache] persistent cache hit: 0
[sym.simp.debug.cache] persistent cache hit: x
[sym.simp.debug.cache] persistent cache hit: f (f (f (f x)))
[sym.simp.debug.cache] persistent cache hit: f (f (f (f x)))
[sym.simp.debug.cache] persistent cache hit: y
[sym.simp.debug.cache] persistent cache hit: f (f (f (f x))) = y
---
trace: [sym.simp.debug.cache] persistent cache hit: f (f (f (f x))) = y
-/
#guard_msgs in
set_option trace.sym.simp.debug.cache true in
example (f : Nat → Nat) (x y : Nat) (h : f (f (f (f x))) = y) : 0 + x = x ∧ 0 + f (f (f (f x))) = y := by
  sym =>
    simp simple
    try simp simple
    apply h

/-! ## Test 11: duplicate variant name is rejected -/

/--
error: Sym.simp variant `simple` is already registered
-/
#guard_msgs in
register_sym_simp simple where

/-! ## Test 12: unknown theorem in `rewrite [...]` is rejected -/

/--
error: Unknown constant `bla`
-/
#guard_msgs in
register_sym_simp simple₁ where
  pre := rewrite [bla]

/-! ## Test 13: unknown theorem set in `rewrite setName` is rejected -/

/--
error: unknown Sym.simp theorem set `boo`
-/
#guard_msgs in
register_sym_simp simple₃ where
  pre := rewrite boo
