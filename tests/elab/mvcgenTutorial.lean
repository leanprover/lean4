import Std.Tactic.Do
import Std.Tactic.BVDecide
import Std.Data.HashSet
set_option backward.do.legacy false

set_option grind.warning false
set_option mvcgen.warning false

open Std Do

namespace Nodup

-- Inspired by Markus' `pairsSumToZero`.

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    exact Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun traversalState seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ traversalState.prefix) ∧ traversalState.prefix.Nodup⌝)
  all_goals mleave; grind

theorem nodup_correct_directly (l : List Int) : nodup l ↔ l.Nodup := by
  rw [nodup]
  generalize hseen : (∅ : Std.HashSet Int) = seen
  change ?lhs ↔ l.Nodup
  suffices h : ?lhs ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen by grind
  clear hseen
  induction l generalizing seen with grind [Id.run_pure, Id.run_bind]

end Nodup

namespace Fresh

structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

namespace Noncompositional

theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  mvcgen [mkFreshN, mkFresh]
  case inv1 => exact ⇓⟨xs, acc⟩ state => ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

theorem mkFreshN_correct_directly (n : Nat) : ((mkFreshN n).run' s).run.Nodup := by
  simp [mkFreshN, mkFresh]
  generalize hacc : #[] = acc
  change ?prog.Nodup
  suffices h : acc.toList.Nodup → (∀ x ∈ acc, x < s.counter) → ?prog.Nodup by grind
  clear hacc
  induction List.range' 0 n generalizing acc s with (simp_all; try grind)

end Noncompositional

namespace Compositional

@[spec]
theorem mkFresh_spec (c : Nat) : ⦃fun state => ⌜state.counter = c⌝⦄ mkFresh ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  mvcgen [mkFresh]
  grind

@[spec]
theorem mkFreshN_spec (n : Nat) : ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  mvcgen [mkFreshN]
  case inv1 => exact ⇓⟨xs, acc⟩ state => ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup :=
  mkFreshN_spec n s True.intro

end Compositional

end Fresh

namespace FreshStack

structure Supply where
  counter : Nat

def mkFresh [Monad m] : StateT Supply m Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

abbrev AppM := StateT Bool (StateT Supply (StateM String))
abbrev liftCounterM : StateT Supply (StateM String) α → AppM α := liftM

def mkFreshN (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← liftCounterM mkFresh
    acc := acc.push n
  return acc.toList

theorem mkFreshN_spec_noncompositional (n : Nat) : ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  mvcgen [mkFreshN, mkFresh, liftCounterM]
  case inv1 => exact ⇓⟨xs, acc⟩ _ state => ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

@[spec]
theorem mkFresh_spec [Monad m] [WPMonad m ps] (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄ mkFresh (m := m) ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  mvcgen [mkFresh]
  grind

@[spec]
theorem mkFreshN_spec (n : Nat) : ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- This is a great test case for `applyRflAndAndIntro` because it requires
  -- reducing `(⌜s₁.counter = ?c⌝ s).down` to `s₁ = ?c`.
  mvcgen [mkFreshN, liftCounterM]
  case inv1 => exact ⇓⟨xs, acc⟩ _ state => ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

theorem mkFreshN_correct (n : Nat) : (((StateT.run' (mkFreshN n) b).run' c).run' s).Nodup :=
  mkFreshN_spec n _ _ _ True.intro

end FreshStack

namespace FreshBounded

structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFresh : EStateM String Supply Nat := do
  let supply ← get
  if h : supply.counter = supply.limit then
    throw s!"Supply exhausted: {supply.counter} = {supply.limit}"
  else
    let n := supply.counter
    have := supply.property
    set {supply with counter := n + 1, property := by omega}
    pure n

def mkFreshN (n : Nat) : EStateM String Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃post⟨fun r state => ⌜r = c ∧ c < state.counter⌝, fun _msg state => ⌜c = state.counter ∧ c = state.limit⌝⟩⦄ := by
  mvcgen [mkFresh]
  all_goals grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄
    mkFreshN n
    ⦃post⟨fun r => ⌜r.Nodup⌝, fun _msg state => ⌜state.counter = state.limit⌝⟩⦄ := by
  mvcgen [mkFreshN]
  case inv1 => exact post⟨fun ⟨xs, acc⟩ state => ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝,
                          fun _msg state => ⌜state.counter = state.limit⌝⟩
  all_goals mleave; try grind

theorem mkFreshN_correct (n : Nat) :
    match (mkFreshN n).run s with
    | .ok    l _  => l.Nodup
    | .error _ s' => s'.counter = s'.limit := by
  generalize h : (mkFreshN n).run s = x
  apply EStateM.of_wp_run_eq h
  mvcgen

end FreshBounded

namespace Aeneas

inductive Error where
  | integerOverflow: Error
  -- ... more error kinds ...

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div

instance : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance : LawfulMonad Result :=
  LawfulMonad.mk' _
    (by dsimp only [Functor.map]; grind)
    (by dsimp only [bind, pure]; grind)
    (by dsimp only [bind, pure]; grind)

instance Result.instWP : WP Result (.except Error .pure) where
  wp
    | .ok v => PredTrans.pure v
    | .fail e => PredTrans.throw e
    | .div => PredTrans.const ⌜False⌝

theorem Result.apply_wp_pure {α} {a : α} {Q : PostCond α (.except Error .pure)} :
  wp⟦pure (f := Result) a⟧ Q = Q.1 a := by rfl

theorem Result.apply_wp_bind {α β} {x : Result α} {f : α → Result β} {Q : PostCond β (.except Error .pure)} :
  wp⟦do let a ← x; f a⟧ Q = wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2) := by
  simp only [wp, bind]
  grind

instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure _ := by ext Q : 1; apply Result.apply_wp_pure
  wp_bind x f := by ext Q : 1; apply Result.apply_wp_bind

theorem Result.of_wp {α} {x : Result α} (P : Result α → Prop) :
  (⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P (.ok a)⌝, fun e => ⌜P (.fail e)⌝⟩) → P x := by
    intro hspec
    match x with
    | .ok a => simpa [wp] using hspec
    | .fail e => simpa [wp] using hspec
    | .div => simp [wp] at hspec

instance : MonadExcept Error Result where
  throw e := .fail e
  tryCatch x h := match x with
  | .ok v => pure v
  | .fail e => h e
  | .div => .div

def addOp (x y : UInt32) : Result UInt32 :=
  if x.toNat + y.toNat ≥ UInt32.size then
    throw .integerOverflow
  else
    pure (x + y)

@[spec]
theorem Result.throw_spec (e : Error) :
    ⦃Q.2.1 e⦄ throw (m := Result) (α := α) e ⦃Q⦄ := id

@[spec]
theorem addOp_noOverflow_spec (x y : UInt32) (h : x.toNat + y.toNat < UInt32.size) :
    ⦃⌜True⌝⦄ addOp x y ⦃⇓ r => ⌜r = x + y ∧ (x + y).toNat = x.toNat + y.toNat⌝⦄ := by
  mvcgen [addOp] <;> simp_all; try grind

example :
  ⦃⌜True⌝⦄
  do let mut x ← addOp 1 3
     for _ in [:4] do
        x ← addOp x 5
     return x
  ⦃⇓ r => ⌜r.toNat = 24⌝⦄ := by
  mvcgen
  case inv1 => exact ⇓⟨xs, x⟩ => ⌜x.toNat = 4 + 5 * xs.prefix.length⌝
  all_goals simp_all [UInt32.size]; try grind

end Aeneas

section PostCond

variable (α σ ε : Type)
example : PostCond α (.arg σ .pure) = ((α → σ → ULift Prop) × PUnit) := rfl
example : PostCond α (.except ε .pure) = ((α → ULift Prop) × (ε → ULift Prop) × PUnit) := rfl
example : PostCond α (.arg σ (.except ε .pure)) = ((α → σ → ULift Prop) × (ε → ULift Prop) × PUnit) := rfl
example : PostCond α (.except ε (.arg σ .pure)) = ((α → σ → ULift Prop) × (ε → σ → ULift Prop) × PUnit) := rfl

end PostCond
