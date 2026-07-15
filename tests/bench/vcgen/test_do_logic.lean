/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
import Lean
import Std.Internal
import Std.Tactic.Do

set_option mvcgen.warning false

/-!
# Do-logic tests for `vcgen`

Ported from `tests/elab/doLogicTests.lean`, keeping only `mvcgen`-specific test cases
and replacing `mvcgen` with `vcgen` where possible.

Tests that are not yet working with `vcgen` keep the original `mvcgen`-based proof.
The deprecation warning emitted by `mvcgen` indicates which tests still need migration.

Tests whose proofs do not mention `mvcgen`/`vcgen` (manual `mspec`/`mintro` proofs)
are intentionally not ported.
-/

open Lean Order Meta Elab Tactic Sym Std Internal.Do

set_option grind.warning false
set_option warn.sorry false
set_option backward.do.legacy false


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

theorem fib_triple : ⦃ True ⦄ fib_impl n ⦃ fun r => r = fib_spec n ⦄ := by
  unfold fib_impl
  vcgen
  case inv1 => exact fun xs ⟨a, b⟩ =>
    a = fib_spec xs.pos ∧ b = fib_spec (xs.pos + 1)
  all_goals grind

theorem fib_triple_finish : ⦃ True ⦄ fib_impl n ⦃ fun r => r = fib_spec n ⦄ := by
  vcgen [fib_impl] invariants
  | inv1 => fun xs ⟨a, b⟩ => a = fib_spec xs.pos ∧ b = fib_spec (xs.pos + 1)
  with finish

theorem fib_triple_step : ⦃ True ⦄ fib_impl n ⦃ fun r => r = fib_spec n ⦄ := by
  unfold fib_impl
  vcgen (stepLimit := some 14)
  case inv1 => exact fun xs ⟨a, b⟩ =>
    a = fib_spec xs.pos ∧ b = fib_spec (xs.pos + 1)
  all_goals grind

attribute [local spec] fib_triple in
theorem fib_triple_attr : ⦃ True ⦄ fib_impl n ⦃ fun r => r = fib_spec n ⦄ := by
  vcgen

attribute [local spec] fib_triple in
theorem fib_triple_erase : ⦃ True ⦄ fib_impl n ⦃fun r => r = fib_spec n⦄ := by
  vcgen (errorOnMissingSpec := false) [-fib_triple]
  fail_if_success done
  admit

theorem fib_impl_vcs
    (Q : Nat → Nat → Prop)
    (E : EPost.Nil)
    (I : (n : Nat) → (_ : ¬n = 0) →
      Invariant [1:n].toList (Prod Nat Nat) Prop)
    (ret : Q 0 0)
    (loop_pre : ∀ n (hn : ¬n = 0), (I n hn) ⟨[], [1:n].toList, rfl⟩ (0, 1))
    (loop_post : ∀ n (hn : ¬n = 0) r, (I n hn) ⟨[1:n].toList, [], by simp⟩ r ⊑ Q n r.2)
    (loop_step : ∀ n (hn : ¬n = 0) r pref cur suff (h : [1:n].toList = pref ++ cur :: suff),
                  (I n hn) ⟨pref, cur::suff, by simp[h]⟩ r ⊑ (I n hn) ⟨pref ++ [cur], suff, by simp[h]⟩ (r.2, r.1+r.2))
    : wp (fib_impl n) (Q n) E := by
  vcgen [fib_impl]
  case inv1 h => exact I n h
  case vc1 h => subst h; apply_rules [ret]
  case vc2 h => apply_rules [loop_pre]
  case vc3 => apply_rules [loop_step]
  case vc4 => apply_rules [loop_post]

@[spec]
theorem mkFreshNat_spec [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ fun s => ⌜s.1 = n ∧ s.2 = o⌝ ⦄
    (mkFreshNat : StateT AppState m Nat)
    ⦃ fun r s => ⌜r = n ∧ s.1 = n + 1 ∧ s.2 = o⌝ ⦄ := by
  vcgen [mkFreshNat] <;> simp_all

theorem erase_unfold [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
  ⦃fun s => ⌜s.1 = n ∧ s.2 = o⌝ ⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃fun r s => ⌜r = n ∧ s.1 = n + 1 ∧ s.2 = o⌝ ⦄ := by
  unfold mkFreshNat
  vcgen (errorOnMissingSpec := false) [-modify]
  simp_all [-WPMonad.wp_modify_StateT_apply_eq]
  fail_if_success done
  admit

theorem add_unfold [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ fun s => ⌜s.1 = n ∧ s.2 = o⌝ ⦄
    (mkFreshNat : StateT AppState m Nat)
    ⦃ fun r s => ⌜r = n ∧ s.1 = n + 1 ∧ s.2 = o⌝ ⦄ := by
  vcgen [mkFreshNat] <;> simp_all

theorem mkFreshPair_triple :
    ⦃ fun _ => True ⦄ mkFreshPair ⦃ fun (p : Nat × Nat) => ⌜p.1 ≠ p.2⌝ ⦄ := by
  vcgen [mkFreshPair] <;> simp_all

theorem sum_loop_spec : ⦃ True ⦄ sum_loop ⦃ fun r => r < 30 ⦄ := by
  vcgen [sum_loop]
  case inv1 => exact fun c x => x = c.«prefix».sum
  all_goals grind

theorem throwing_loop_spec :
  ⦃fun s => s = 4⦄
  throwing_loop
  ⦃fun _ _ => False;
  epost⟨fun e s => e = 42 ∧ s = 4⟩⦄ := by
  vcgen [throwing_loop]
  case inv1 => exact fun xs r s => r ≤ 4 ∧ s = 4 ∧ r + xs.suffix.sum > 4
  all_goals (simp_all; try grind)

theorem test_loop_break :
    ⦃ fun s => s = 42 ⦄ breaking_loop ⦃ fun r s => r > 4 ∧ s = 1 ⦄ := by
  vcgen [breaking_loop]
  case inv1 => exact fun xs r s => (r ≤ 4 ∧ r = xs.prefix.sum ∨ r > 4) ∧ s = 42
  all_goals grind

theorem test_loop_early_return :
    ⦃ fun s => s = 4 ⦄ returning_loop ⦃ fun r s => r = 42 ∧ s = 4 ⦄ := by
  vcgen [returning_loop]
  case inv1 => exact fun xs r s => (r.1 = none ∧ r.2 = xs.prefix.sum ∧ r.2 ≤ 4 ∨ r.1 = some 42 ∧ r.2 > 4) ∧ s = 4
  all_goals grind

theorem unfold_to_expose_match_spec :
  ⦃ fun s => s = 4 ⦄
  unfold_to_expose_match
  ⦃ fun r => ⌜r = 4⌝ ⦄ := by
  vcgen [unfold_to_expose_match, Option.getD]

theorem test_match_splitting {mo : Option Nat} (h : mo = some 4) :
    ⦃ fun _ => True ⦄
    (match mo with
     | some n => (set n : StateM Nat PUnit)
     | none => set 0)
    ⦃ fun _ s => s = 4 ⦄ := by
  vcgen <;> simp_all

theorem test_sum :
    ⦃ True ⦄
    (do
      let mut x := 0
      for i in [1:5] do
        x := x + i
      pure x : Id _)
    ⦃ fun r => r < 30 ⦄ := by
  vcgen
  case inv1 => exact fun c x => x = c.«prefix».sum
  all_goals grind

theorem mspec_forwards_mvars {n : Nat} :
  ⦃True⦄
  (do
    for i in [2:n] do
      if n < i * i then
        return 1
    return 1 : Id Nat)
  ⦃fun r => True⦄ := by
  vcgen
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
  vcgen
  case inv1 =>
    exact Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
      (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
  all_goals simp_all [-Classical.not_forall]; try grind

end Automated

namespace HimpSplit

-- A `⇨` (Heyting implication) in the postcondition exercises the `himp_complete` split, whose
-- subgoal carries a `⊓ ⊤` precondition that `meet_top_le_of_le` cancels. The abstract `Pred` keeps
-- `⇨` from collapsing to `→`.
theorem himp_post {m} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ ⊤ ⦄ (pure 4 : m Nat) ⦃ fun r => ⌜r = 4⌝ ⇨ ⌜r > 0⌝ ⦄ := by
  vcgen
  all_goals grind

end HimpSplit

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
    ⦃ ∀ i, (h : i < xs.size) → xs[i] ≥ 0 ⦄
    max_and_sum xs ⦃ fun (m, s) => s ≤ m * xs.size ⦄ := by
  vcgen [max_and_sum]
  case inv1 => exact fun c ⟨mx, s⟩ => s ≤ mx * c.pos
  all_goals simp_all +zetaDelta
  case vc3 =>
    rename_i hle hlt
    rw [Nat.left_distrib]
    simp only [Nat.mul_one]
    exact Nat.add_le_add (Nat.le_trans hle (Nat.mul_le_mul_right _ (Nat.le_of_lt hlt))) (Nat.le_refl _)
  case vc4 =>
    rw [Nat.left_distrib]
    grind

end MaxAndSum

end VSTTE2010

namespace RishsConstApproxBug

@[inline] def test : StateM Unit Unit := do
  let _ ← get
  if True then
    pure ()

theorem need_const_approx' :
    ⦃ fun x => x = () ⦄ test ⦃ fun _ _ => True ⦄ := by
  vcgen [test]

end RishsConstApproxBug

namespace RishsTailContextBug

axiom I : StateM Nat Unit
axiom F : StateM Nat Unit
axiom G : StateM Nat Unit
axiom P : Nat → Prop
axiom Q : Unit → Nat → Prop
axiom hI : ⦃ fun _ => True ⦄ I ⦃ fun _ => P ⦄
axiom hF : ⦃ P ⦄ F ⦃ Q ⦄
axiom hG : ⦃ P ⦄ G ⦃ Q ⦄
attribute [local spec] hI hF hG

@[inline] noncomputable def test_ite : StateM Nat Unit := do
  I
  let n ← get
  if n < 1 then
    F
  else
    G

theorem ex : ⦃ fun _ => True ⦄ test_ite ⦃ Q ⦄ := by
  vcgen [test_ite]

end RishsTailContextBug

namespace KimsUnivPolyUseCase

open Std

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} [TransCmp cmp]

def mergeWithAll (m₁ m₂ : ExtTreeMap α β cmp) (f : α → Option β → Option β → Option β) :
    ExtTreeMap α β cmp :=
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
-- Neither `mvcgen` nor `vcgen` can find a triple spec for `forIn` on the
-- universe-polymorphic `ExtTreeMap`; both fall back to simp, which simplifies
-- the body but doesn't fully discharge. With `(errorOnMissingSpec := false)`,
-- `vcgen` matches legacy `mvcgen`'s behaviour of leaving an unsolved VC.
theorem mem_mergeWithAll [LawfulEqCmp cmp] {m₁ m₂ : ExtTreeMap α β cmp}
    {f : α → Option β → Option β → Option β} {a : α} :
    a ∈ mergeWithAll m₁ m₂ f ↔ (a ∈ m₁ ∨ a ∈ m₂) ∧ (f a m₁[a]? m₂[a]?).isSome := by
  generalize h : mergeWithAll m₁ m₂ f = x
  apply Id.of_wp_run_eq h
  vcgen (errorOnMissingSpec := false) [mergeWithAll]
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
  vcgen
  case inv1 => exact fun c s => s = c.«prefix».sum
  all_goals simp_all +zetaDelta

end Slices

/-! ## PatricksFastExp -/

namespace PatricksFastExp

def naive_expo (x n : Nat) : Nat := Id.run do
  let mut y := 1
  for _ in [:n] do
    y := y * x
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

theorem naive_expo_correct (x n : Nat) : naive_expo x n = x ^ n := by
  generalize h : naive_expo x n = r
  apply Id.of_wp_run_eq h
  vcgen
  case inv1 => exact fun c y => y = x ^ c.pos
  all_goals simp_all +zetaDelta [Nat.pow_add_one]

theorem fast_expo_correct (x n : Nat) : fast_expo x n = x ^ n := by
  generalize h : fast_expo x n = r
  apply Id.of_wp_run_eq h
  vcgen
  case inv1 => exact fun xs ⟨x', y, e⟩ => x' ^ e * y = x ^ n ∧ e ≤ n - xs.pos
  all_goals simp_all +zetaDelta
  case vc2 ih =>
    rw [← ih.1, ih.2, Nat.pow_zero, Nat.one_mul]
  case vc4 =>
    constructor
    · rw [← Nat.mul_assoc, ← Nat.pow_add_one]
      grind
    · grind
  case vc5 =>
    constructor
    · rw [← Nat.pow_two, ← Nat.pow_mul]
      grind
    · grind

theorem same_func (x n : Nat) : fast_expo x n = naive_expo x n := by
  rw [naive_expo_correct, fast_expo_correct]

end PatricksFastExp

section IteratorTests

variable {m} [Monad m]
open Std Std.Iterators

theorem forIn_eq_sum (xs : Array Nat) {m} [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] :
    ⦃ ⊤ ⦄
    (do
      let mut sum : Nat := 0
      for n in xs.iter do
        sum := sum + n
      return sum : m _)
    ⦃ fun r => ⌜r = xs.sum⌝ ⦄ := by
  vcgen
  case inv1 => exact fun cur n => ⌜n = cur.prefix.sum⌝
  all_goals grind

theorem forIn_map_eq_sum_add_size' (xs : Array Nat) {m} [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] :
    ⦃ ⊤ ⦄ (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).map (· + 1) do
        sum := sum + n
      return sum) ⦃ fun r => ⌜r = xs.sum + xs.size⌝ ⦄ := by
  vcgen
  case inv1 => exact fun cur n => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind

theorem forIn_map_eq_sum_add_size (xs : Array Nat) {m} [Monad m] [Assertion Pred] [Assertion EPred]
    [WPMonad m Pred EPred] :
    ⦃ ⊤ ⦄ (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).map (· + 1) do
        sum := sum + n
      return sum) ⦃ fun r => ⌜r = xs.sum + xs.size⌝ ⦄ := by
  vcgen
  case inv1 => exact fun cur n => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind


theorem forIn_mapM_eq_sum_add_size (xs : Array Nat) {m} [Monad m] [MonadAttach m]
    [LawfulMonad m] [WeaklyLawfulMonadAttach m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ ⊤ ⦄ (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).mapM (pure (f := m) <| · + 1) do
        sum := sum + n
      return sum) ⦃ fun r => ⌜r = xs.sum + xs.size⌝ ⦄ := by
  vcgen
  case inv1 => exact fun cur n => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind

theorem forIn_filterMapM_eq_sum_add_size (xs : Array Nat) {m}
    [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ ⊤ ⦄ (m := m) (do
      let mut sum : Nat := 0
      for n in (xs.iterM Id).filterMapM (pure (f := m) <| some <| · + 1) do
        sum := sum + n
      return sum) ⦃ fun r => ⌜r = xs.sum + xs.size⌝ ⦄ := by
  vcgen
  case inv1 => exact fun cur n => ⌜n = cur.prefix.sum + cur.prefix.length⌝
  all_goals grind

theorem foldM_eq_sum (xs : Array Nat) {m} [Monad m] [LawfulMonad m]
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    ⦃ ⊤ ⦄ (xs.iter.foldM (m := m) (init := 0) (pure <| · + ·)) ⦃ fun r => ⌜r = xs.sum⌝ ⦄ := by
  vcgen
  case inv1 => exact fun cur n => ⌜n = cur.prefix.sum⌝
  all_goals grind

end IteratorTests

namespace ConfigSyntaxTests

/-! Tests for the ported `(config := …)` syntax. Implemented options change behavior
silently; `leave` and `jp` are accepted by the parser but warn that they are
currently ignored. -/

def trivial_test (n : Nat) : Id Nat := pure n

/-- An empty `(config := {})` matches the default `vcgen` behavior. -/
example : ⦃ True ⦄ trivial_test 0 ⦃fun r => r = 0⦄ := by
  vcgen (config := {}) [trivial_test]

-- `trivial := false` skips `repeatAndRfl`, leaving a residual entailment.
example : ⦃ True ⦄ trivial_test 0 ⦃fun r => r = 0⦄ := by
  vcgen (trivial := false) [trivial_test]
  trivial

-- `elimLets := false` skips the let-elimination pre-pass (now honored by `vcgen`).
example : ⦃ True ⦄ trivial_test 0 ⦃fun r => r = 0⦄ := by
  vcgen (config := { elimLets := false }) [trivial_test]

-- `stepLimit` is accepted; with a positive limit, simple programs still discharge.
example : ⦃ True ⦄ trivial_test 0 ⦃fun r => r = 0⦄ := by
  vcgen (config := { stepLimit := some 100 }) [trivial_test]

/-- warning: vcgen: the `leave` config option is currently ignored. -/
#guard_msgs in
example : ⦃ True ⦄ trivial_test 0 ⦃fun r => r = 0⦄ := by
  vcgen (config := { leave := false }) [trivial_test]

-- `jp := true` is accepted and wired through `Context.useJP`; the actual
-- shared-continuation construction (Phase 6 of the plan) is not yet ported,
-- so enabling it on a program containing `__do_jp` errors at the detection
-- point. Programs without `__do_jp` (like this trivial example) are unaffected.
example : ⦃ True ⦄ trivial_test 0 ⦃fun r => r = 0⦄ := by
  vcgen (config := { jp := true }) [trivial_test]


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
  vcgen invariants
    · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
      (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
  all_goals simp_all [-Classical.not_forall]; try grind

-- Labelled form: `| inv1 => …`.
example (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ check_all p n := by
  generalize h : check_all p n = x
  apply Id.of_wp_run_eq h
  vcgen invariants
    | inv1 => Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ⌜ret = false ∧ ¬ ∀ i < n, p i⌝)
      (onContinue := fun xs _ => ⌜∀ i, i ∈ xs.prefix → p i⌝)
  all_goals simp_all [-Classical.not_forall]; try grind

end InvariantSyntaxTests

namespace RflReducibility

-- From `mvcgenRflReducibility.lean`. Asserts that decomposing `MyShl.shl a 32` does
-- not whnf at default reducibility, otherwise `UInt64.ofNat 32.toInt.toNat` would
-- unfold deeply and timeout. `vcgen` keeps reduction at `.instances` transparency
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
⊢ wp (Except.error "") (fun x => True) ⊥
-/
#guard_msgs in
example (a : UInt64) :
    ⦃True⦄
      do
        let a ← MyShl.shl a (32: Int32)
        let a ← MyAddU.add (0 : UInt64) a
        pure a
    ⦃fun _ => True⦄ := by
  vcgen (errorOnMissingSpec := false) [MyShl.shl, MyAddU.add]

end RflReducibility

namespace LocalSpec

def foo (x : Id Nat → Id Nat) : Id Nat := do
  let r₁ ← x (pure 42)
  let r₂ ← x (pure 26)
  pure (r₁ + r₂)

theorem foo_spec
    (x : Id Nat → Id Nat)
    (x_spec : ∀ (k : Id Nat), ⦃ True ⦄ k ⦃ fun r => r % 2 = 0 ⦄ →
      ⦃ True ⦄ x k ⦃ fun r => r % 2 = 0 ⦄) :
    ⦃ True ⦄ foo x ⦃ fun r => r % 2 = 0 ⦄ := by
  vcgen [foo, x_spec] with finish

def bar (k : Id Nat) : Id Nat := do
  let r ← k
  if r > 30 then
    return 12
  else
    return r

example : ⦃ True ⦄ foo bar ⦃ fun r => r % 2 = 0 ⦄ := by
  vcgen [foo_spec, bar] with finish

end LocalSpec

namespace RawMonadLiftRegression

/-! A raw `monadLift` of an `Id` value into an outer monad, discharged by `Spec.monadLift_Id`. -/

def liftProg : StateT Nat Id Nat := do
  let x ← (pure 5 : Id Nat)
  return x

example : ⦃ fun _ => ⌜True⌝ ⦄ liftProg ⦃ fun r _ => ⌜r = 5⌝ ⦄ := by vcgen [liftProg] <;> grind

end RawMonadLiftRegression

namespace InvalidSpecRejection

/-! A `@[spec]` annotation whose conclusion is neither a Hoare triple nor an equation is rejected. -/

/-- error: Invalid 'spec': target was neither a Hoare triple specification nor a 'simp' lemma -/
#guard_msgs in
@[spec] theorem trivialSpec : True := trivial

end InvalidSpecRejection

namespace TopBetaReduction

variable {m : Type → Type u} {Pred EPred} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

def incr (n : Nat) : StateT Nat m PUnit := modify (· + n)

@[spec]
theorem Spec.incr
    (post : PUnit → Nat → Pred) (epost : EPred) (n : Nat) :
    ⦃ fun s => post ⟨⟩ (s + n) ⦄ (incr n : StateT Nat m PUnit) ⦃ post; epost ⦄ := by
  vcgen [TopBetaReduction.incr]; rfl

/--
error: unsolved goals
case vc1
amounts : List Nat
s✝ : Nat
⊢ ⊥
-/
#guard_msgs in
theorem incr_id (amounts : List Nat) :
  ⦃ ⊤ ⦄
    incr (m := Id) 1
  ⦃ fun _ _ => ⊥ ⦄ := by
  vcgen [incr]

/--
error: unsolved goals
case vc1
m : Type → Type u
Pred EPred : Type
inst✝³ : Monad m
inst✝² : Assertion Pred
inst✝¹ : Assertion EPred
inst✝ : WPMonad m Pred EPred
amounts : List Nat
s✝ : Nat
⊢ ⊤ ⊑ ⊥
-/
#guard_msgs in
theorem incr_poly (amounts : List Nat) :
  ⦃ ⊤ ⦄
    incr (m := m) 1
  ⦃ fun _ _ => ⊥ ⦄ := by
  vcgen [incr]


end TopBetaReduction

namespace RepeatInvariantOfInvariantAndBreak

/-! Verifies a `while` loop whose `vcgen` invariant is supplied via
`RepeatInvariant.ofInvariantAndBreak`: a loop invariant `inv` that holds after every iteration plus
an `onBreak` condition (here the negated loop condition) that additionally holds once the loop
exits. -/

/-- Counts `i` down from `n`, incrementing the state on each iteration, so the final state is `n`. -/
def countdown (n : Nat) : StateT Nat Id Unit := do
  let mut i := n
  while i > 0 do
    i := i - 1
    modify (· + 1)
  return

theorem countdown_spec (n : Nat) :
    ⦃ fun s => s = 0 ⦄ countdown n ⦃ fun _ s => s = n ⦄ := by
  vcgen [countdown]
  case inv1 => exact RepeatInvariant.ofInvariantAndBreak (fun i s => s + i = n) (fun i _ => i = 0)
  case inv2 => exact fun i => i
  any_goals simp at *
  all_goals grind

end RepeatInvariantOfInvariantAndBreak
namespace WithGrindError

/-! The `with` clause of `vcgen` only accepts a `grind`-mode step (e.g. `finish`, `intro`). A
general tactic such as `grind` parses but is rejected with a helpful error in the elaborator,
rather than a raw `unexpected identifier; expected grind` parser error. -/

def trivial_test (n : Nat) : Id Nat := pure n

/--
error: `vcgen … with` expects a `grind`-mode discharging step, not a general tactic

Hint: Examples: `vcgen … with finish`, `vcgen … with intro`.
-/
#guard_msgs in
example : ⦃ True ⦄ trivial_test 0 ⦃fun r => r = 0⦄ := by
  vcgen [trivial_test] with grind

end WithGrindError
