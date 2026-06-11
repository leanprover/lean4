/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import Std
import Std.Tactic.Do

set_option mvcgen.warning false

/-!
# Do-logic tests for `mvcgen'`

Ported from `tests/elab/doLogicTests.lean`, keeping only `mvcgen`-specific test cases
and replacing `mvcgen` with `mvcgen'` where possible.

Tests that are not yet working with `mvcgen'` keep the original `mvcgen`-based proof.
The deprecation warning emitted by `mvcgen` indicates which tests still need migration.

Tests whose proofs do not mention `mvcgen`/`mvcgen'` (manual `mspec`/`mintro` proofs)
are intentionally not ported.
-/

open Lean Meta Elab Tactic Sym Std Do SpecAttr

set_option grind.warning false
set_option warn.sorry false
set_option backward.do.legacy false

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Code

def fib_impl (n : Nat) : Id Nat := do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

@[simp, grind =]
def fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

abbrev AppState := Nat × Nat

def mkFreshNat [Monad m] [MonadStateOf AppState m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

def mkFreshPair : StateM AppState (Nat × Nat) := do
  let a ← mkFreshNat
  let b ← mkFreshNat
  pure (a, b)

def sum_loop : Id Nat := do
  let mut x := 0
  for i in [1:5] do x := x + i
  return x

def throwing_loop : ExceptT Nat (StateT Nat Id) Nat := do
  let mut x := 0
  let s ← get
  for i in [1:s] do { x := x + i; if x > 4 then throw 42 }
  (set 1 : ExceptT Nat (StateT Nat Id) PUnit)
  return x

def breaking_loop : StateT Nat Id Nat := do
  let mut x := 0
  let s ← get
  for i in [1:s] do { x := x + i; if x > 4 then break }
  set 1
  return x

def returning_loop : StateT Nat Id Nat := do
  let mut x := 0
  let s ← get
  for i in [1:s] do { x := x + i; if x > 4 then return 42 }
  set 1
  return x

def unfold_to_expose_match : StateM Nat Nat :=
  (some get).getD (pure 3)

end Code

namespace Automated

open Code

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  unfold fib_impl
  mvcgen'
  case inv1 => exact ⇓ (xs, ⟨a, b⟩) =>
    ⌜a = fib_spec xs.pos ∧ b = fib_spec (xs.pos + 1)⌝
  all_goals grind

theorem fib_triple_step : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  unfold fib_impl
  mvcgen' (stepLimit := some 14)
  case inv1 => exact ⇓ ⟨xs, a, b⟩ =>
    ⌜a = fib_spec xs.pos ∧ b = fib_spec (xs.pos + 1)⌝
  all_goals simp_all +zetaDelta [Nat.sub_one_add_one]

attribute [local spec] fib_triple in
theorem fib_triple_attr : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  mvcgen'

attribute [local spec] fib_triple in
theorem fib_triple_erase : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  mvcgen' (errorOnMissingSpec := false) [-fib_triple]
  fail_if_success done
  admit

theorem fib_impl_vcs
    (Q : Nat → PostCond Nat PostShape.pure)
    (I : (n : Nat) → (_ : ¬n = 0) →
      Invariant [1:n].toList (Prod Nat Nat) PostShape.pure)
    (ret : ⊢ₛ (Q 0).fst 0)
    (loop_pre : ∀ n (hn : ¬n = 0), ⊢ₛ (I n hn).fst ⟨⟨[], [1:n].toList, rfl⟩, 0, 1⟩)
    (loop_post : ∀ n (hn : ¬n = 0) r, (I n hn).fst ⟨⟨[1:n].toList, [], by simp⟩, r⟩ ⊢ₛ (Q n).fst r.2)
    (loop_step : ∀ n (hn : ¬n = 0) r pref cur suff (h : [1:n].toList = pref ++ cur :: suff),
                  (I n hn).fst ⟨⟨pref, cur::suff, by simp[h]⟩, r⟩ ⊢ₛ (I n hn).1 ⟨⟨pref ++ [cur], suff, by simp[h]⟩, r.2, r.1+r.2⟩)
    : ⊢ₛ wp⟦fib_impl n⟧ (Q n) := by
  mvcgen' [fib_impl]
  case inv1 h => exact I n h
  case vc1 h => subst h; apply_rules [ret]
  case vc2 h => apply_rules [loop_pre]
  case vc3 => apply_rules [loop_step]
  case vc4 => apply_rules [loop_post]

@[spec]
theorem mkFreshNat_spec [Monad m] [WPMonad m sh] :
  ⦃fun s => ⌜s.1 = n ∧ s.2 = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r s => ⌜r = n ∧ s.1 = n + 1 ∧ s.2 = o⌝⦄ := by
  mvcgen' [mkFreshNat]
  simp_all +zetaDelta

theorem erase_unfold [Monad m] [WPMonad m sh] :
  ⦃fun s => ⌜s.1 = n ∧ s.2 = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r s => ⌜r = n ∧ s.1 = n + 1 ∧ s.2 = o⌝⦄ := by
  unfold mkFreshNat
  mvcgen' (errorOnMissingSpec := false) [-modify]
  simp_all [-WP.modify_MonadStateOf]
  fail_if_success done
  admit

theorem add_unfold [Monad m] [WPMonad m sh] :
  ⦃fun s => ⌜s.1 = n ∧ s.2 = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r s => ⌜r = n ∧ s.1 = n + 1 ∧ s.2 = o⌝⦄ := by
  mvcgen' [mkFreshNat]
  simp_all +zetaDelta

-- `mkFreshPair_triple` from doLogicTests uses `mvcgen -elimLets +trivial [mkFreshPair]`.
theorem mkFreshPair_triple : ⦃⌜True⌝⦄ mkFreshPair ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  mvcgen' [mkFreshPair]
  simp_all

theorem sum_loop_spec :
  ⦃⌜True⌝⦄
  sum_loop
  ⦃⇓r => ⌜r < 30⌝⦄ := by
  -- cf. `ByHand.sum_loop_spec`
  mintro -
  mvcgen' [sum_loop]
  case inv1 => exact (⇓ (xs, r) => ⌜r + xs.suffix.length * 5 ≤ 25⌝)
  all_goals simp_all; try grind

theorem throwing_loop_spec :
  ⦃fun s => ⌜s = 4⌝⦄
  throwing_loop
  ⦃post⟨fun _ _ => ⌜False⌝,
        fun e s => ⌜e = 42 ∧ s = 4⌝⟩⦄ := by
  mvcgen' [throwing_loop]
  case inv1 => exact post⟨fun (xs, r) s => ⌜r ≤ 4 ∧ s = 4 ∧ r + xs.suffix.sum > 4⌝,
                         fun e s => ⌜e = 42 ∧ s = 4⌝⟩
  all_goals mleave; try (subst_vars; grind)

theorem test_loop_break :
  ⦃fun s => ⌜s = 42⌝⦄
  breaking_loop
  ⦃⇓ r s => ⌜r > 4 ∧ s = 1⌝⦄ := by
  mvcgen' [breaking_loop]
  case inv1 => exact (⇓ (xs, r) s => ⌜(r ≤ 4 ∧ r = xs.prefix.sum ∨ r > 4) ∧ s = 42⌝)
  all_goals grind

theorem test_loop_early_return :
  ⦃fun s => ⌜s = 4⌝⦄
  returning_loop
  ⦃⇓ r s => ⌜r = 42 ∧ s = 4⌝⦄ := by
  mvcgen' [returning_loop]
  case inv1 => exact (⇓ (xs, r) s => ⌜(r.1 = none ∧ r.2 = xs.prefix.sum ∧ r.2 ≤ 4 ∨ r.1 = some 42 ∧ r.2 > 4) ∧ s = 4⌝)
  all_goals grind

theorem unfold_to_expose_match_spec :
  ⦃fun s => ⌜s = 4⌝⦄
  unfold_to_expose_match
  ⦃⇓ r => ⌜r = 4⌝⦄ := by
  mvcgen' [unfold_to_expose_match, Option.getD]
  simplifying_assumptions [SPred.pure_cons]

theorem test_match_splitting {m : Option Nat} (h : m = some 4) :
  ⦃⌜True⌝⦄
  (match m with
  | some n => (set n : StateM Nat PUnit)
  | none => set 0)
  ⦃⇓ _ s => ⌜s = 4⌝⦄ := by
  mvcgen' <;> simp_all

theorem test_sum :
  ⦃⌜True⌝⦄
  (do
    let mut x := 0
    for i in [1:5] do
      x := x + i
    pure x : Id _)
  ⦃⇓r => ⌜r < 30⌝⦄ := by
  mvcgen'
  case inv1 => exact (⇓ (xs, r) => ⌜r + xs.suffix.length * 5 ≤ 25⌝)
  all_goals simp_all; try grind

theorem mspec_forwards_mvars {n : Nat} :
  ⦃⌜True⌝⦄
  (do
    for i in [2:n] do
      if n < i * i then
        return 1
    return 1 : Id Nat)
  ⦃⇓ r => ⌜True⌝⦄ := by
  mvcgen'
  all_goals admit

def check_all (p : Nat → Prop) [DecidablePred p] (n : Nat) : Bool := Id.run do
  for i in [0:n] do
    if ¬ p i then
      return false
  return true

example (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ check_all p n := by
  generalize h : check_all p n = x
  apply Id.of_wp_run_eq h
  mvcgen'
  case inv1 =>
    exact Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
      (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
  all_goals simp_all [-Classical.not_forall]; try grind

end Automated

namespace VSTTE2010

namespace MaxAndSum

def max_and_sum (xs : Array Nat) : Id (Nat × Nat) := do
  let mut max := 0
  let mut sum := 0
  for h : i in [0:xs.size] do
    sum := sum + xs[i]
    if xs[i] > max then
      max := xs[i]
  return (max, sum)

theorem max_and_sum_spec (xs : Array Nat) :
    ⦃⌜∀ i, (h : i < xs.size) → xs[i] ≥ 0⌝⦄ max_and_sum xs ⦃⇓ (m, s) => ⌜s ≤ m * xs.size⌝⦄ := by
  mvcgen' [max_and_sum]
  case inv1 => exact (⇓ ⟨xs, m, s⟩ => ⌜s ≤ m * xs.pos⌝)
  all_goals simp_all +zetaDelta
  · rename_i h
    rw [Nat.left_distrib]
    simp +zetaDelta only [Nat.mul_one, Nat.add_le_add_iff_right]
    apply Nat.le_trans h
    apply Nat.mul_le_mul_right
    grind
  · rw [Nat.left_distrib]
    grind

end MaxAndSum

end VSTTE2010

namespace RishsConstApproxBug

@[spec]
theorem Spec.get_StateT' [Monad m] [WPMonad m psm] :
  ⦃fun s => Q.1 s s⦄ (MonadState.get : StateT σ m σ) ⦃Q⦄ := Spec.get_StateT

@[inline] def test : StateM Unit Unit := do
  let _ ← get
  if True then
    pure ()

theorem need_const_approx' :
   ⦃fun x => ⌜x = ()⌝⦄
   test
   ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen' [test]
  -- mvcgen' leaves trivial VCs that mvcgen would auto-discharge
  all_goals grind

end RishsConstApproxBug

namespace RishsTailContextBug

axiom Specs.get_StateT' [Monad m] [WPMonad m psm] :
  ⦃fun s => Q.1 s s⦄ (MonadState.get : StateT σ m σ) ⦃Q⦄
attribute [local spec] Specs.get_StateT'

axiom I : StateM Nat Unit
axiom F : StateM Nat Unit
axiom G : StateM Nat Unit
axiom P : Assertion (PostShape.arg Nat PostShape.pure)
axiom Q: PostCond Unit (PostShape.arg Nat PostShape.pure)
axiom hI : ⦃⌜True⌝⦄ I ⦃⇓ _ => P⦄
axiom hF : ⦃P⦄ F ⦃Q⦄
axiom hG : ⦃P⦄ G ⦃Q⦄
attribute [local spec] hI hF hG

@[inline] noncomputable def test_ite : StateM Nat Unit := do
  I
  let n ← get
  if n < 1 then
    F
  else
    G

theorem ex : ⦃⌜True⌝⦄ test_ite ⦃Q⦄ := by
  mvcgen' [test_ite]

end RishsTailContextBug

namespace KimsUnivPolyUseCase

open Std

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} [TransCmp cmp]

def mergeWithAll (m₁ m₂ : ExtTreeMap α β cmp) (f : α → Option β → Option β → Option β) : ExtTreeMap α β cmp :=
  Id.run do
    let mut r := ∅
    for (a, b₁) in m₁ do
      if let some b := f a (some b₁) m₂[a]? then
        r := r.insert a b
    for (a, b₂) in m₂ do
      if a ∉ m₁ then
        if let some b := f a none (some b₂) then
          r := r.insert a b
    return r

-- Originally a demo that `Id.of_wp_run_eq` applies despite universe polymorphism.
-- Neither `mvcgen` nor `mvcgen'` can find a triple spec for `forIn` on the
-- universe-polymorphic `ExtTreeMap`; both fall back to simp, which simplifies
-- the body but doesn't fully discharge. With `(errorOnMissingSpec := false)`,
-- `mvcgen'` matches legacy `mvcgen`'s behaviour of leaving an unsolved VC.
theorem mem_mergeWithAll [LawfulEqCmp cmp] {m₁ m₂ : ExtTreeMap α β cmp} {f : α → Option β → Option β → Option β} {a : α} :
    a ∈ mergeWithAll m₁ m₂ f ↔ (a ∈ m₁ ∨ a ∈ m₂) ∧ (f a m₁[a]? m₂[a]?).isSome := by
  generalize h : mergeWithAll m₁ m₂ f = x
  apply Id.of_wp_run_eq h
  mvcgen' (errorOnMissingSpec := false) [mergeWithAll]
  admit

end KimsUnivPolyUseCase

namespace Slices

def subarraySum (xs : Subarray Nat) : Nat := Id.run do
  let mut sum := 0
  for x in xs do
    sum := sum + x
  return sum

theorem subarraySum_correct {xs : Subarray Nat} : subarraySum xs = xs.toList.sum := by
  generalize h : subarraySum xs = r
  apply Id.of_wp_run_eq h
  mvcgen'
  case inv1 => exact ⇓⟨cursor, prefixSum⟩ => ⌜prefixSum = cursor.prefix.sum⌝
  all_goals simp_all +zetaDelta

end Slices

namespace PatricksFastExp

def naive_expo (x n : Nat) : Nat := Id.run do
  let mut y := 1
  for _ in [:n] do
    y := y*x
  return y

def fast_expo (x n : Nat) : Nat := Id.run do
  let mut x := x
  let mut y := 1
  let mut e := n
  for _ in [:n] do -- simulating a while loop running at most n times
    if e = 0 then break
    if e % 2 = 1 then
      y := x * y
      e := e - 1
    else
      x := x*x
      e := e/2

  return y

theorem naive_expo_correct (x n : Nat) : naive_expo x n = x^n := by
  generalize h : naive_expo x n = r
  apply Id.of_wp_run_eq h
  mvcgen'
  case inv1 => exact ⇓⟨xs, r⟩ => ⌜r = x^xs.pos⌝
  all_goals simp_all +zetaDelta [Nat.pow_add_one]

-- NOTE: mvcgen' leaves VCs with un-destructured tuples (`b.fst`, `b.snd.snd`),
-- so the proof manually `obtain`s them. The legacy mvcgen names the components.
theorem fast_expo_correct (x n : Nat) : fast_expo x n = x^n := by
  generalize h : fast_expo x n = r
  apply Id.of_wp_run_eq h
  mvcgen'
  case inv1 => exact ⇓⟨xs, x', y, e⟩ => ⌜x' ^ e * y = x ^ n ∧ e ≤ n - xs.pos⌝
  all_goals simp_all +zetaDelta
  case vc2 b _ _ _ _ _ _ _ _ ih =>
    obtain ⟨x', y, e⟩ := b
    simp at *
    constructor
    · rw [← Nat.mul_assoc, ← Nat.pow_add_one, ← ih.1]
      have : e - 1 + 1 = e := by grind
      rw [this]
    · grind
  case vc3 b _ _ _ _ _ _ _ ih _ =>
    obtain ⟨x', y, e⟩ := b
    simp at *
    constructor
    · rw [← Nat.pow_two, ← Nat.pow_mul]
      grind
    · grind
  case vc5 b _ _ ih =>
    obtain ⟨x', y, e⟩ := b
    simp at *
    rw [← ih.1, ih.2, Nat.pow_zero, Nat.one_mul]

theorem same_func (x n : Nat) : fast_expo x n = naive_expo x n := by
  rw [naive_expo_correct, fast_expo_correct]

end PatricksFastExp

section IteratorTests

variable {m} [Monad m]
open Std Std.Iterators

theorem forIn_eq_sum (xs : Array Nat) {m ps} [Monad m] [WPMonad m ps] :
    Triple (m := m) (do
      let mut sum : Nat := 0
      for n in xs.iter do
        sum := sum + n
      return sum) ⌜True⌝ (⇓r => ⌜r = xs.sum⌝) := by
  mvcgen'
  case inv1 => exact ⇓⟨cur, n⟩ => ⌜n = cur.prefix.sum⌝
  all_goals grind

theorem forIn_map_eq_sum_add_size (xs : Array Nat) {m ps} [Monad m] [LawfulMonad m]
    [WPMonad m ps] :
    Triple (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).map (· + 1) do
        sum := sum + n
      return sum) ⌜True⌝ (⇓r => ⌜r = xs.sum + xs.size⌝) := by
  mvcgen'
  case inv1 => exact ⇓⟨cur, n⟩ => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind


theorem forIn_map_eq_sum_add_size' (xs : Array Nat) {m ps} [Monad m] [LawfulMonad m]
    [WPMonad m ps] :
    Triple (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).map (· + 1) do
        sum := sum + n
      return sum) ⌜True⌝ (⇓r => ⌜r = xs.sum + xs.size⌝) := by
  mvcgen'
  case inv1 => exact ⇓⟨cur, n⟩ => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind

theorem forIn_mapM_eq_sum_add_size (xs : Array Nat) {m ps} [Monad m] [MonadAttach m]
    [LawfulMonad m] [WeaklyLawfulMonadAttach m] [WPMonad m ps] :
    Triple (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).mapM (pure (f := m) <| · + 1) do
        sum := sum + n
      return sum) ⌜True⌝ (⇓r => ⌜r = xs.sum + xs.size⌝) := by
  mvcgen'
  case inv1 => exact ⇓⟨cur, n⟩ => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind

theorem forIn_filterMapM_eq_sum_add_size (xs : Array Nat) {m ps}
    [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] [WPMonad m ps] :
    Triple (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).filterMapM (pure (f := m) <| some <| · + 1) do
        sum := sum + n
      return sum) ⌜True⌝ (⇓r => ⌜r = xs.sum + xs.size⌝) := by
  mvcgen'
  case inv1 => exact ⇓⟨cur, n⟩ => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind

theorem foldM_eq_sum (xs : Array Nat) {m ps} [Monad m] [LawfulMonad m]
    [WPMonad m ps] :
    Triple (m := m)
      (xs.iter.foldM (m := m) (init := 0) (pure <| · + ·))
      ⌜True⌝
      (⇓r => ⌜r = xs.sum⌝) := by
  mvcgen'
  case inv1 => exact ⇓⟨cur, n⟩ => ⌜n = cur.prefix.sum⌝
  all_goals grind

end IteratorTests

namespace ConfigSyntaxTests

/-! Tests for the ported `(config := …)` syntax. Implemented options change behavior
silently; `leave` and `jp` are accepted by the parser but warn that they are
currently ignored. -/

def trivial_test (n : Nat) : Id Nat := pure n

/-- An empty `(config := {})` matches the default `mvcgen'` behavior. -/
example : ⦃⌜True⌝⦄ trivial_test 0 ⦃⇓r => ⌜r = 0⌝⦄ := by
  mvcgen' (config := {}) [trivial_test]

-- `trivial := false` skips `repeatAndRfl`, leaving a residual entailment.
example : ⦃⌜True⌝⦄ trivial_test 0 ⦃⇓r => ⌜r = 0⌝⦄ := by
  mvcgen' (trivial := false) [trivial_test]
  trivial

-- `elimLets := false` is silently accepted (no preprocessing).
example : ⦃⌜True⌝⦄ trivial_test 0 ⦃⇓r => ⌜r = 0⌝⦄ := by
  mvcgen' (config := { elimLets := false }) [trivial_test]

-- `stepLimit` is accepted; with a positive limit, simple programs still discharge.
example : ⦃⌜True⌝⦄ trivial_test 0 ⦃⇓r => ⌜r = 0⌝⦄ := by
  mvcgen' (config := { stepLimit := some 100 }) [trivial_test]

/-- warning: mvcgen': the `leave` config option is currently ignored. -/
#guard_msgs in
example : ⦃⌜True⌝⦄ trivial_test 0 ⦃⇓r => ⌜r = 0⌝⦄ := by
  mvcgen' (config := { leave := false }) [trivial_test]

-- `jp := true` is accepted and wired through `Context.useJP`; the actual
-- shared-continuation construction (Phase 6 of the plan) is not yet ported,
-- so enabling it on a program containing `__do_jp` errors at the detection
-- point. Programs without `__do_jp` (like this trivial example) are unaffected.
example : ⦃⌜True⌝⦄ trivial_test 0 ⦃⇓r => ⌜r = 0⌝⦄ := by
  mvcgen' (config := { jp := true }) [trivial_test]

end ConfigSyntaxTests

namespace InvariantSyntaxTests

/-! Tests for the ported `invariants` syntax (bullet form and labelled form). -/

def check_all (p : Nat → Prop) [DecidablePred p] (n : Nat) : Bool := Id.run do
  for i in [0:n] do
    if ¬ p i then
      return false
  return true

-- Bullet form: `· …` per invariant. Uses the `with` clause to discharge the
-- emitted VCs in one go (preTac runs after all invariants are inline-elaborated,
-- so the `with` tactic sees the assigned invariant values).
example (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ check_all p n := by
  generalize h : check_all p n = x
  apply Id.of_wp_run_eq h
  mvcgen' invariants
    · Invariant.withEarlyReturnNewDo
        (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
        (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
  all_goals simp_all [-Classical.not_forall]; try grind

-- Labelled form: `| inv1 => …`.
example (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ check_all p n := by
  generalize h : check_all p n = x
  apply Id.of_wp_run_eq h
  mvcgen' invariants
    | inv1 => Invariant.withEarlyReturnNewDo
        (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
        (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
  all_goals simp_all [-Classical.not_forall]; try grind

end InvariantSyntaxTests

namespace RflReducibility

-- From `mvcgenRflReducibility.lean`. Asserts that decomposing `MyShl.shl a 32` does
-- not whnf at default reducibility, otherwise `UInt64.ofNat 32.toInt.toNat` would
-- unfold deeply and timeout. `mvcgen'` keeps reduction at `.instances` transparency
-- when stepping through class projections (`reduceProj?` in `Reduce.lean`), so this
-- example decomposes cleanly.

abbrev RustM := Except String

class MyAddU (Self : Type) (Rhs : Type) where
  add : (Self → Rhs → RustM Self)

instance : MyAddU UInt64 UInt64 := {
  add x y := if BitVec.uaddOverflow x.toBitVec y.toBitVec then Except.error "" else pure (x + y)
}

class MyShl (Self : Type) (Rhs : Type) where
  shl : (Self → Rhs → RustM Self)

instance : MyShl UInt64 Int32 := {
  shl x y := pure (x <<< (UInt64.ofNat y.toInt.toNat))
}

/--
error: unsolved goals
case vc1
a : UInt64
h✝ : (UInt64.toBitVec 0).uaddOverflow (a <<< UInt64.ofNat (Int32.toInt 32).toNat).toBitVec = true
⊢ ⊢ₛ wp⟦Except.error ""⟧ (fun r => ⌜True⌝, ExceptConds.false)
-/
#guard_msgs in
example (a : UInt64) :
    ⦃⌜True⌝⦄
      do
        let a ← MyShl.shl a (32: Int32)
        let a ← MyAddU.add (0 : UInt64) a
        pure a
    ⦃PostCond.noThrow fun r => ⌜True⌝⦄ := by
  mvcgen' (errorOnMissingSpec := false) [MyShl.shl, MyAddU.add]

end RflReducibility

namespace LocalSpec

def foo (x : Id Nat → Id Nat) : Id Nat := do
  let r₁ ← x (pure 42)
  let r₂ ← x (pure 26)
  pure (r₁ + r₂)

theorem foo_spec
    (x : Id Nat → Id Nat)
    (x_spec : ∀ (k : Id Nat) (_ : ⦃⌜True⌝⦄ k ⦃⇓r => ⌜r % 2 = 0⌝⦄), ⦃⌜True⌝⦄ x k ⦃⇓r => ⌜r % 2 = 0⌝⦄) :
    ⦃⌜True⌝⦄ foo x ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen' [foo, x_spec] with finish

def bar (k : Id Nat) : Id Nat := do
  let r ← k
  if r > 30 then return 12 else return r

example : ⦃⌜True⌝⦄ foo bar ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen' [foo_spec, bar] with finish

end LocalSpec
