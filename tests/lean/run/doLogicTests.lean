/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/

import Std.Tactic.Do
import Std.Tactic.Do.Syntax
import Std

open Std.Do

set_option grind.warning false
set_option mvcgen.warning false

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

abbrev fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

def ifs (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := x + 1 else x := x + 2
  if n > 1 then x := x + 1 else x := x + 2
  return x

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

namespace ByHand

open Code

open Lean.Parser.Tactic

theorem sum_loop_spec :
  ⦃⌜True⌝⦄
  sum_loop
  ⦃⇓r => ⌜r < 30⌝⦄ := by
  mintro -
  unfold sum_loop
  mspec
  case inv => exact (⇓ (r, xs) => ⌜(∀ x, x ∈ xs.suff → x ≤ 5) ∧ r + xs.suff.length * 5 ≤ 25⌝)
  all_goals simp_all +decide; try omega
  intros
  mintro _
  mspec
  simp_all +decide
  omega

private abbrev fst : SVal ((Nat × Nat)::σs) Nat := fun s => SVal.pure s.1
private abbrev snd : SVal ((Nat × Nat)::σs) Nat := fun s => SVal.pure s.2

def mkFreshNat [Monad m] [MonadStateOf AppState m] : m Nat := do
  let n ← Prod.fst <$> get
  modify (fun s => (s.1 + 1, s.2))
  pure n

@[spec]
theorem mkFreshNat_spec [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT (Nat × Nat) m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  mintro _
  dsimp only [mkFreshNat, get, getThe, instMonadStateOfOfMonadLift, liftM, monadLift, modify, modifyGet]
  mspec
  mspec
  mspec
  mspec
  simp

def mkFreshPair : StateM (Nat × Nat) (Nat × Nat) := do
  let a ← mkFreshNat
  let b ← mkFreshNat
  pure (a, b)

theorem mkFreshPair_spec :
  ⦃⌜True⌝⦄
  mkFreshPair
  ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  mintro -
  mspec mkFreshNat_spec
  mintro ∀s
  mrename_i h
  mcases h with ⌜h₁⌝
  mspec mkFreshNat_spec
  mintro ∀s
  mrename_i h
  mcases h with ⌜h₂⌝
  simp_all

theorem mkFreshPair_spec_no_eta :
  ⦃⌜True⌝⦄
  mkFreshPair
  ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  unfold mkFreshPair
  mintro -
  mspec mkFreshNat_spec
  mspec mkFreshNat_spec
  mspec
  intro _; simp_all

example : PostCond (Nat × Std.List.Zipper (List.range' 1 3 1)) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  ⟨fun (r, xs) s => ⌜r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4⌝, fun e s => ⌜e = 42 ∧ s = 4⌝, ()⟩

example : PostCond (Nat × Std.List.Zipper (List.range' 1 3 1)) (PostShape.except Nat (PostShape.arg Nat PostShape.pure)) :=
  post⟨fun (r, xs) s => ⌜r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4⌝, fun e s => ⌜e = 42 ∧ s = 4⌝⟩

theorem throwing_loop_spec :
  ⦃fun s => ⌜s = 4⌝⦄
  throwing_loop
  ⦃post⟨fun _ _ => ⌜False⌝,
        fun e s => ⌜e = 42 ∧ s = 4⌝⟩⦄ := by
  mintro hs
  dsimp only [throwing_loop, get, getThe, instMonadStateOfOfMonadLift, liftM, monadLift]
  mspec
  mspec
  mspec
  case inv => exact post⟨fun (r, xs) s => ⌜r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4⌝, fun e s => ⌜e = 42 ∧ s = 4⌝⟩
  case post.success =>
    mspec
    mspec
    mspec
    simp_all only [List.sum_nil, Nat.add_zero, gt_iff_lt, SVal.curry_nil, SPred.entails_nil,
      imp_false, not_true_eq_false]
    omega
  case post.except => simp
  case pre1 => simp_all +decide
  case step =>
    simp_all
    intros
    mintro _
    split
    case isTrue => intro _; mintro _; mspec; mspec; intro _; simp_all
    case isFalse => intro _; mintro _; mspec; intro _; simp_all +arith

theorem beaking_loop_spec :
  ⦃⌜‹Nat›ₛ = 42⌝⦄
  breaking_loop
  ⦃⇓ r => ⌜r > 4 ∧ ‹Nat›ₛ = 1⌝⦄ := by
  mintro hs
  dsimp only [breaking_loop, get, getThe, instMonadStateOfOfMonadLift, liftM, monadLift]
  mspec
  mspec
  case inv => exact (⇓ (r, xs) s => ⌜(r ≤ 4 ∧ r = xs.rpref.sum ∨ r > 4) ∧ s = 42⌝)
  all_goals simp_all
  case post =>
    intro _ h
    conv at h in (List.sum _) => whnf
    simp at h
    simp
    grind
  case step =>
    intros
    mintro _
    split
    case isTrue => intro _; mintro _; mspec; simp_all
    case isFalse => intro _; mintro _; mspec; simp_all; omega

theorem returning_loop_spec :
  ⦃fun s => ⌜s = 4⌝⦄
  returning_loop
  ⦃⇓ r s => ⌜r = 42 ∧ s = 4⌝⦄ := by
  mintro hs
  dsimp only [returning_loop, get, getThe, instMonadStateOfOfMonadLift, liftM, monadLift]
  mspec
  mspec
  case inv => exact (⇓ (r, xs) s => ⌜(r.1 = none ∧ r.2 = xs.rpref.sum ∧ r.2 ≤ 4 ∨ r.1 = some 42 ∧ r.2 > 4) ∧ s = 4⌝)
  all_goals simp_all
  case post =>
    split
    · mspec
      mspec
      intro _ h
      conv at h in (List.sum _) => whnf
      simp at h
      grind
    · mspec
      intro _ h
      conv at h in (List.sum _) => whnf
      simp at h
      grind
  case step =>
    intros
    mintro _
    split
    case isTrue => intro _; mintro _; mspec; simp_all
    case isFalse => intro _; mintro _; mspec; simp_all; omega

section fib

def fib_impl (n : Nat) : Id Nat := do
  if n = 0 then return 0
  let mut a := 0
  let mut b := 1
  for _ in [1:n] do
    let a' := a
    a := b
    b := a' + b
  return b

abbrev fib_spec : Nat → Nat
| 0 => 0
| 1 => 1
| n+2 => fib_spec n + fib_spec (n+1)

-- Finally investigate why we do not see the error here.
-- Seems to be related to not being able to display metavariables.
--theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => r = fib_spec n⦄ := by
--  unfold fib_impl
--  dsimp
--  mintro _
--  if h : n = 0 then simp [h] else
--  simp only [h, reduceIte]
--  mspec
--  mspec_no_bind Spec.bind
--  set_option trace.Elab.Tactic.Do.spec true in
--  mspec_no_bind Spec.forIn_list ?inv ?step
--
--  case step => dsimp; intros; mintro _; simp_all
--  simp_all [Nat.sub_one_add_one]

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  unfold fib_impl
  dsimp
  mintro _
  if h : n = 0 then simp [h] else
  simp only [h, reduceIte]
  mspec -- Spec.pure
  mspec Spec.forIn_range (⇓ (⟨a, b⟩, xs) => ⌜a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)⌝) ?step
  case step => dsimp; intros; mintro _; simp_all
  simp_all [Nat.sub_one_add_one]

theorem fib_triple_cases : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  apply fib_impl.fun_cases n _ ?case1 ?case2
  case case1 => rintro rfl; mintro -; simp only [fib_impl, ↓reduceIte]; mspec
  intro h
  mintro -
  simp only [fib_impl, h, reduceIte]
  mspec
  mspec Spec.forIn_range (⇓ (⟨a, b⟩, xs) => ⌜a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)⌝) ?step
  case step => dsimp; intros; mintro _; mspec; mspec; simp_all
  simp_all [Nat.sub_one_add_one]

theorem fib_impl_vcs
    (Q : Nat → PostCond Nat PostShape.pure)
    (I : (n : Nat) → (_ : ¬n = 0) →
      PostCond (MProd Nat Nat × Std.List.Zipper [1:n].toList) PostShape.pure)
    (ret : ⊢ₛ (Q 0).1 0)
    (loop_pre : ∀ n (hn : ¬n = 0), ⊢ₛ (I n hn).1 (⟨0, 1⟩, Std.List.Zipper.begin _))
    (loop_post : ∀ n (hn : ¬n = 0) r, (I n hn).1 (r, Std.List.Zipper.end _) ⊢ₛ (Q n).1 r.snd)
    (loop_step : ∀ n (hn : ¬n = 0) r rpref x suff (h : [1:n].toList = rpref.reverse ++ x :: suff),
                  (I n hn).1 (r, ⟨rpref, x::suff, by simp[h]⟩) ⊢ₛ (I n hn).1 (⟨r.2, r.1+r.2⟩, ⟨x::rpref, suff, by simp[h]⟩))
    : ⊢ₛ wp⟦fib_impl n⟧ (Q n) := by
  apply fib_impl.fun_cases n _ ?case1 ?case2
  case case1 => intro h; simp only [fib_impl, h, ↓reduceIte]; mstart; mspec
  intro hn
  simp only [fib_impl, hn, ↓reduceIte]
  mstart
  mspec
  mspec
  case pre1 => exact loop_pre n hn
  case post.success => mspec; mpure_intro; apply_rules [loop_post]
  case step =>
    intro _ _ _ _ h;
    mintro _;
    mspec
    mspec
    mpure_intro
    apply_rules [loop_step]

theorem fib_triple_vcs : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  apply fib_impl_vcs
  case I => intro n hn; exact (⇓ (⟨a, b⟩, xs) => ⌜a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)⌝)
  case ret => mpure_intro; rfl
  case loop_pre => intros; mpure_intro; trivial
  case loop_post => simp_all [Nat.sub_one_add_one]
  case loop_step => simp_all

theorem fib_correct {n} : (fib_impl n).run = fib_spec n := by
  generalize h : (fib_impl n).run = x
  apply Id.by_wp h
  apply fib_triple

end fib

section KimsBabySteps

/-- Add `n` random even numbers to `k`. -/
def addRandomEvens (n : Nat) (k : Nat) : IO Nat := do
  let mut r := k
  for _ in List.range n do
    r := r + 2 * (← IO.rand 0 37)
  pure r

def program (n : Nat) (k : Nat) : IO Nat := do
  let r₁ ← addRandomEvens n k
  let r₂ ← addRandomEvens n k
  return r₁ + r₂

open scoped Std.Do.IO.Bare

axiom IO.rand_spec {n : Nat} : ⦃⌜True⌝⦄ (IO.rand 0 n : IO Nat) ⦃⇓r => ⌜r < n⌝⦄

/-- The result has the same parity as the input. -/
@[spec]
theorem addRandomEvens_spec (n k) : ⦃⌜True⌝⦄ (addRandomEvens n k) ⦃⇓r => ⌜r % 2 = k % 2⌝⦄ := by
  unfold addRandomEvens
  mintro -
  mspec Spec.forIn_list_const_inv
  intro n r
  mintro ⌜h⌝
  mspec IO.rand_spec
  simp_all

/-- Since we're adding even numbers to our number twice, and summing,
the entire result is even. -/
theorem program_spec (n k) : ⦃⌜True⌝⦄ program n k ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  unfold program
  mintro -
  mspec (addRandomEvens_spec n k)
  mrename_i h
  mpure h
  mspec /- registered spec is taken -/
  mrename_i h
  mpure h
  mspec
  mpure_intro
  grind

end KimsBabySteps

section WeNeedAProofMode

private abbrev theNat : SVal [Nat, Bool] Nat := fun n _ => n
private def test (P Q : Assertion (.arg Nat (.arg Bool .pure))) : Assertion (.arg Char (.arg Nat (.arg Bool .pure))) :=
  spred(fun n => ((∀ y, if y = n then ⌜‹Nat›ₛ + #theNat = 4⌝ else Q) ∧ Q) → P → (∃ x, P → if (x : Bool) then Q else P))

abbrev M := StateT Nat (StateT Char (StateT Bool (StateT String Id)))
axiom op : Nat → M Nat
noncomputable def prog (n : Nat) : M Nat := do
  let a ← op n
  let b ← op a
  let c ← op b
  return (a + b + c)

axiom isValid : Nat → Char → Bool → String → ULift Prop

axiom op.spec {n} : ⦃isValid⦄ op n ⦃⇓r => ⌜r > 42⌝ ∧ isValid⦄

theorem prog.spec : ⦃isValid⦄ prog n ⦃⇓r => ⌜r > 100⌝ ∧ isValid⦄ := by
  unfold prog
  mintro h
  mspec op.spec
  mrename_i h
  mcases h with ⟨⌜hr₁⌝, □h⟩
  /-
  n r : Nat
  hr₁ : r > 42
  ⊢
  h : isValid
  ⊢ₛ
  wp⟦do
      let b ← op r
      let c ← op b
      pure (r + b + c)⟧
    (⇓r => ⌜r > 100⌝ ∧ isValid)
  -/
  mspec op.spec
  mrename_i h
  mcases h with ⟨⌜hr₂⌝, □h⟩
  mspec op.spec
  mrename_i h
  mcases h with ⟨⌜hr₃⌝, □h⟩
  mspec
  mrefine ⟨?_, h⟩
  mpure_intro
  omega

end WeNeedAProofMode

end ByHand

namespace Automated

open Code

theorem fib_triple : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  unfold fib_impl
  mvcgen
  case inv => exact ⇓ (⟨a, b⟩, xs) =>
    ⌜a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)⌝
  all_goals simp_all +zetaDelta [Nat.sub_one_add_one]

theorem fib_triple_step : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  unfold fib_impl
  mvcgen_step 14 -- 13 still has a wp⟦·⟧
  case inv => exact ⇓ (⟨a, b⟩, xs) =>
    ⌜a = fib_spec xs.rpref.length ∧ b = fib_spec (xs.rpref.length + 1)⌝
  all_goals simp_all +zetaDelta [Nat.sub_one_add_one]

attribute [local spec] fib_triple in
theorem fib_triple_attr : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  mvcgen

attribute [local spec] fib_triple in
theorem fib_triple_erase : ⦃⌜True⌝⦄ fib_impl n ⦃⇓ r => ⌜r = fib_spec n⌝⦄ := by
  mvcgen [-fib_triple] -- should not make any progress
  fail_if_success done
  admit

theorem fib_impl_vcs
    (Q : Nat → PostCond Nat PostShape.pure)
    (I : (n : Nat) → (_ : ¬n = 0) →
      PostCond (MProd Nat Nat × Std.List.Zipper [1:n].toList) PostShape.pure)
    (ret : ⊢ₛ (Q 0).1 0)
    (loop_pre : ∀ n (hn : ¬n = 0), ⊢ₛ (I n hn).1 (⟨0, 1⟩, Std.List.Zipper.begin _))
    (loop_post : ∀ n (hn : ¬n = 0) r, (I n hn).1 (r, Std.List.Zipper.end _) ⊢ₛ (Q n).1 r.snd)
    (loop_step : ∀ n (hn : ¬n = 0) r rpref x suff (h : [1:n].toList = rpref.reverse ++ x :: suff),
                  (I n hn).1 (r, ⟨rpref, x::suff, by simp[h]⟩) ⊢ₛ (I n hn).1 (⟨r.2, r.1+r.2⟩, ⟨x::rpref, suff, by simp[h]⟩))
    : ⊢ₛ wp⟦fib_impl n⟧ (Q n) := by
  unfold fib_impl
  mvcgen
  case inv h => exact I n h
  case isTrue h => subst h; exact ret
  case isFalse h => mpure_intro; apply_rules [loop_pre]
  case step => mpure_intro; apply_rules [loop_step]
  case post.success => mpure_intro; apply_rules [loop_post]

-- TODO: Use strongest post
theorem ifs_triple : ⦃⌜True⌝⦄ ifs n ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold ifs
  mvcgen_no_trivial <;> try (mpure_intro; trivial) -- this is the default for mvcgen

private abbrev fst : SVal (AppState::σs) Nat := fun s => SVal.pure s.1
private abbrev snd : SVal (AppState::σs) Nat := fun s => SVal.pure s.2

@[spec]
theorem mkFreshNat_spec [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  mvcgen [mkFreshNat]
  simp_all

theorem erase_unfold [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  unfold mkFreshNat
  mvcgen [-modify]
  simp_all [-WP.modify_MonadStateOf]
  fail_if_success done
  admit

theorem add_unfold [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT AppState m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄ := by
  mvcgen [mkFreshNat]

theorem mkFreshPair_triple : ⦃⌜True⌝⦄ mkFreshPair ⦃⇓ (a, b) => ⌜a ≠ b⌝⦄ := by
  mvcgen [mkFreshPair]
  simp_all [SPred.entails_cons]

theorem sum_loop_spec :
  ⦃⌜True⌝⦄
  sum_loop
  ⦃⇓r => ⌜r < 30⌝⦄ := by
  -- cf. `ByHand.sum_loop_spec`
  mintro -
  mvcgen [sum_loop]
  case inv => exact (⇓ (r, xs) => ⌜(∀ x, x ∈ xs.suff → x ≤ 5) ∧ r + xs.suff.length * 5 ≤ 25⌝)
  all_goals simp_all +decide; try grind

theorem throwing_loop_spec :
  ⦃fun s => ⌜s = 4⌝⦄
  throwing_loop
  ⦃post⟨fun _ _ => ⌜False⌝,
        fun e s => ⌜e = 42 ∧ s = 4⌝⟩⦄ := by
  mvcgen [throwing_loop]
  case inv => exact post⟨fun (r, xs) s => ⌜r ≤ 4 ∧ s = 4 ∧ r + xs.suff.sum > 4⌝,
                         fun e s => ⌜e = 42 ∧ s = 4⌝⟩
  case pre1 => simp_all only [SVal.curry_nil, SPred.entails_nil]; decide
  case post.success => simp_all only [SVal.curry_nil, SPred.entails_nil]; grind
  case post.except => simp_all
  case isTrue => intro _; simp_all
  case isFalse => intro _; simp_all only [SVal.curry_nil, SPred.entails_nil]; grind

theorem test_loop_break :
  ⦃⌜‹Nat›ₛ = 42⌝⦄
  breaking_loop
  ⦃⇓ r => ⌜r > 4 ∧ ‹Nat›ₛ = 1⌝⦄ := by
  mvcgen [breaking_loop]
  case inv => exact (⇓ (r, xs) s => ⌜(r ≤ 4 ∧ r = xs.rpref.sum ∨ r > 4) ∧ s = 42⌝)
  case pre1 => simp_all
  case isTrue => intro _; simp_all
  case isFalse => intro _; simp_all only [SVal.curry_nil, SPred.entails_nil]; grind
  case post.success =>
    simp_all
    rename_i h
    conv at h in (List.sum _) => whnf
    simp at h
    grind

theorem test_loop_early_return :
  ⦃fun s => ⌜s = 4⌝⦄
  returning_loop
  ⦃⇓ r s => ⌜r = 42 ∧ s = 4⌝⦄ := by
  mvcgen [returning_loop]
  case inv => exact (⇓ (r, xs) s => ⌜(r.1 = none ∧ r.2 = xs.rpref.sum ∧ r.2 ≤ 4 ∨ r.1 = some 42 ∧ r.2 > 4) ∧ s = 4⌝)
  case isTrue => intro _; simp_all
  case isFalse => intro _; simp_all only [SVal.curry_nil, SPred.entails_nil]; grind
  case pre1 => simp_all
  case h_1 =>
    simp_all
    rename_i h
    conv at h in (List.sum _) => whnf
    simp at h
    grind
  case h_2 => simp_all

theorem unfold_to_expose_match_spec :
  ⦃fun s => ⌜s = 4⌝⦄
  unfold_to_expose_match
  ⦃⇓ r => ⌜r = 4⌝⦄ := by
  -- should unfold `Option.getD`, reduce the `match (some get) with | some e => e`
  -- and then apply the spec for `get`.
  mvcgen [unfold_to_expose_match, Option.getD]

theorem test_match_splitting {m : Option Nat} (h : m = some 4) :
  ⦃⌜True⌝⦄
  (match m with
  | some n => (set n : StateM Nat PUnit)
  | none => set 0)
  ⦃⇓ r s => ⌜s = 4⌝⦄ := by
  mvcgen
  simp_all

theorem test_sum :
  ⦃⌜True⌝⦄
  do
    let mut x := 0
    for i in [1:5] do
      x := x + i
    pure (f := Id) x
  ⦃⇓r => ⌜r < 30⌝⦄ := by
  mvcgen
  case inv => exact (⇓ (r, xs) => ⌜(∀ x, x ∈ xs.suff → x ≤ 5) ∧ r + xs.suff.length * 5 ≤ 25⌝)
  case step =>
    simp_all
    omega
  case post.success => simp_all; omega
  simp_all +decide

/--
  The main point about this test is that `mSpec` should return all unassigned MVars it creates.
  This used to be untrue because `mkForallFVars` etc. would instantiate MVars and introduce new
  unassigned MVars in turn. It is important for `mSpec` to return these new MVars, otherwise
  we get `(kernel) declaration has metavariables 'MPL.Test.VC.mspec_forwards_mvars'`
-/
theorem mspec_forwards_mvars {n : Nat} :
  ⦃⌜True⌝⦄
  (do
    for i in [2:n] do
      if n < i * i then
        return 1
    return 1 : Id Nat)
  ⦃⇓ r => ⌜True⌝⦄ := by
  mvcgen
  all_goals admit

def check_all (p : Nat → Prop) [DecidablePred p] (n : Nat) : Bool := Id.run do
  for i in [0:n] do
    if ¬ p i then
      return false
  return true

@[simp]
theorem Std.Range.mem_toList {x} {r : Std.Range} :
    x ∈ r.toList ↔ x ∈ r := sorry

@[simp]
theorem Nat.mod_one {n : Nat} : n % 1 = 0 := by omega

/--
VC generation is normally not useful to massage hypotheses such as `ht`, but in this example
we manage to prove a contradiction `hf` using the VC generator.
-/
example (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (∀ i, i < n → p i) ↔ check_all p n := by
  constructor
  · intro h
    apply Id.by_wp (P := (· = true)) rfl
    mvcgen
    case inv => exact (⇓ (r, xs) => ⌜r.1 = none ∧ ∀ x, x ∈ xs.suff → p x⌝)
    case pre1 => simp; intro a ha; apply h a ha.upper
    all_goals simp_all
  · intro ht i hin
    apply Classical.byContradiction
    intro h'
    have hf : check_all p n = false := by
      have hin : i ∈ [0:n] := by simp [Std.instMembershipNatRange, hin]
      apply Id.by_wp (P := (· = false)) rfl
      mvcgen
      case inv => exact (⇓ (r, xs) =>
        match r.1 with
        | none => ⌜i ∈ xs.suff⌝
        | some b => ⌜b = false ∧ xs.suff = []⌝)
      all_goals simp_all; try grind
    simp [ht] at hf

end Automated

namespace Aeneas

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq

open Error

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

instance : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance : LawfulMonad Result := sorry

instance Result.instWP : WP Result (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure := by intros; ext Q; simp [wp, PredTrans.pure, pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [instWP, bind]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const]

/-- Kinds of unsigned integers -/
inductive UScalarTy where
| Usize
| U8
| U16
| U32
| U64
| U128

def UScalarTy.numBits (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => System.Platform.numBits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128

/-- Signed integer -/
structure UScalar (ty : UScalarTy) where
  /- The internal representation is a bit-vector -/
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

def UScalar.val {ty} (x : UScalar ty) : Nat := x.bv.toNat

def UScalar.ofNatCore {ty : UScalarTy} (x : Nat) (_ : x < 2^ty.numBits) : UScalar ty :=
  { bv := BitVec.ofNat _ x }

instance (ty : UScalarTy) : CoeOut (UScalar ty) Nat where
  coe := λ v => v.val

def UScalar.tryMk (ty : UScalarTy) (x : Nat) : Result (UScalar ty) :=
  sorry

def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.val + y.val)

instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd x y := UScalar.add x y

@[irreducible]
def UScalar.max (ty : UScalarTy) : Nat := 2^ty.numBits-1

theorem UScalar.add_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  ∃ z, x + y = Result.ok z ∧ (↑z : Nat) = ↑x + ↑y := sorry

abbrev U32 := UScalar .U32
abbrev U32.max   : Nat := UScalar.max .U32

theorem U32.add_spec {x y : U32} (hmax : x.val + y.val ≤ U32.max) :
  ∃ z, x + y = Result.ok z ∧ (↑z : Nat) = ↑x + ↑y :=
  UScalar.add_spec sorry -- (by scalar_tac)

abbrev PCond (α : Type) := PostCond α (PostShape.except Error PostShape.pure)

@[spec]
theorem U32.add_spec' {x y : U32} {Q : PCond U32} (hmax : ↑x + ↑y ≤ U32.max):
  ⦃Q.1 (UScalar.ofNatCore (↑x + ↑y) sorry)⦄ (x + y) ⦃Q⦄ := by
    mintro h
    have ⟨z, ⟨hxy, hz⟩⟩ := U32.add_spec hmax
    simp [hxy, hz.symm, wp]
    sorry -- show Q.1 z ↔ Q.1 (ofNatCore z.val ⋯)

@[simp]
theorem UScalar.ofNatCore_val_eq : (ofNatCore x h).val = x := sorry

def mul2_add1 (x : U32) : Result U32 :=
  do
  let i ← x + x
  i + (UScalar.ofNatCore 1 sorry : U32)

theorem mul2_add1_spec' (x : U32) (h : 2 * x.val + 1 ≤ U32.max)
  : ⦃Q.1 (UScalar.ofNatCore (2 * ↑x + (1 : Nat)) sorry)⦄ (mul2_add1 x) ⦃Q⦄ := by
  mvcgen [mul2_add1]
  all_goals simp_all +arith; try omega

end Aeneas

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
  mvcgen [max_and_sum]
  case inv => exact (⇓ (⟨m, s⟩, xs) => ⌜s ≤ m * xs.rpref.length⌝)
  all_goals simp_all
  · rw [Nat.left_distrib]
    simp
    rename_i h
    apply Nat.le_trans h
    apply Nat.mul_le_mul_right
    omega
  · rw [Nat.left_distrib]
    omega

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

theorem need_const_approx :
   ⦃fun x => ⌜x = ()⌝⦄
   test
   ⦃⇓ _ => ⌜True⌝⦄ := by
  unfold test
  mintro _
  mspec
  split <;> mspec

theorem need_const_approx' :
   ⦃fun x => ⌜x = ()⌝⦄
   test
   ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen [test]

end RishsConstApproxBug

namespace RishsTailContextBug

@[spec]
theorem Specs.get_StateT' [Monad m] [WPMonad m psm] :
  ⦃fun s => Q.1 s s⦄ (MonadState.get : StateT σ m σ) ⦃Q⦄ := by sorry

axiom I : StateM Nat Unit
axiom F : StateM Nat Unit
axiom G : StateM Nat Unit
axiom P : Assertion (PostShape.arg Nat PostShape.pure)
axiom Q: PostCond Unit (PostShape.arg Nat PostShape.pure)
@[spec]
axiom hI : ⦃⌜True⌝⦄ I ⦃⇓ _ => P⦄
@[spec]
axiom hF : ⦃P⦄ F ⦃Q⦄
@[spec]
axiom hG : ⦃P⦄ G ⦃Q⦄


@[inline] noncomputable def test_ite : StateM Nat Unit := do
  I
  let n ← get
  if n < 1 then
    F
  else
    G

theorem ex : ⦃⌜True⌝⦄ test_ite ⦃Q⦄ := by
  mvcgen [test_ite]
  -- We used to get
  --   s✝ : Nat
  --   h : P s✝
  --   a✝ : s✝ < 1
  --   ⊢
  --   h✝ : fun s => ⌜True⌝
  --   ⊢ₛ P
  -- and this is unsatisfiable. We need to remember the tail context `· s✝`.
  -- The simplest way to do so is to use `split` in `mvcgen`, which we do now.

-- Same with explicit `split` and `mspec`
theorem ex': ⦃⌜True⌝⦄ test_ite ⦃Q⦄ := by
  unfold test_ite
  mintro _
  mspec
  mspec
  mintro ∀ s
  split <;> mspec

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

theorem mem_mergeWithAll [LawfulEqCmp cmp] {m₁ m₂ : ExtTreeMap α β cmp} {f : α → Option β → Option β → Option β} {a : α} :
    a ∈ mergeWithAll m₁ m₂ f ↔ (a ∈ m₁ ∨ a ∈ m₂) ∧ (f a m₁[a]? m₂[a]?).isSome := by
  generalize h : mergeWithAll m₁ m₂ f = x
  apply Id.by_wp h
  mvcgen
  -- this was only to demonstrate that `Id.by_wp` and `mvcgen` applies here despite the universe polymorphism
  admit

end KimsUnivPolyUseCase
