/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.PredTrans
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Internal.Do

/-!
# Weakest Precondition Interpretation

This module defines the weakest precondition interpretation `WPMonad` of monadic programs
in terms of predicate transformers `PredTrans`.

An instance `WPMonad m Pred EPred` determines a function `wpTrans : m α → PredTrans Pred EPred α` that
interprets a program `x : m α` as a predicate transformer. The function `wp` is the
user-facing wrapper: `wp x post epost` computes the weakest precondition for `x` to
satisfy normal postcondition `post` and exception postcondition `epost`.

## Assertion Language Classes

`Assertion` is an alias type class for `CompleteLattice`.
We use `Assertion Pred` for the assertion language of normal postconditions
and `Assertion EPred` for exception postconditions.

## Pre-defined instances

* `WPMonad Id Prop EPost.Nil` — pure computations.
* `WPMonad (StateT σ m) (σ → Pred) EPred` — stateful computations.
* `WPMonad (ExceptT ε m) Pred (EPost.Cons (ε → Pred) EPred)` — computations with exceptions.
* `WPMonad (ReaderT ρ m) (ρ → Pred) EPred` — reader computations.
* `WPMonad (Except ε) Prop EPost⟨ε → Prop⟩` — concrete exception type.
* `WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop)` — concrete error-state monad.
-/

namespace Std.Internal.Do

variable {m : Type u → Type z}

/-!
## WP and WPMonad Typeclasses

The `WP` typeclass interprets a program type `Prog` whose results have type `Value` as a monotone
predicate transformer `wpTrans : Prog → PredTrans Pred EPred Value`.

The `WPMonad` typeclass adds soundness of the weakest precondition interpretation for the monadic
`pure` and `bind` of a monad `m`, on top of a `WP (m α) α Pred EPred` interpretation for every
result type `α`.
-/

/-- Weakest precondition interpretation of a program type `Prog` whose results have type `Value`,
as a monotone predicate transformer over assertion language `Pred` with exception postconditions
`EPred`. -/
class WP (Prog : Type u) (Value : outParam (Type v)) (Pred : outParam (Type w))
    (EPred : outParam (Type w')) [Assertion Pred] [Assertion EPred] where
  /-- The weakest precondition transformer for a program. -/
  wpTrans : Prog → PredTrans Pred EPred Value
  /-- Monotonicity: weaker postconditions yield weaker preconditions. -/
  wp_trans_monotone (x : Prog) : wpTrans x |>.monotone

/-- Weakest precondition of `x` for normal postcondition `post` and exception postcondition `epost`.
The `WP` interpretation can be supplied explicitly via dot notation (`inst.wp x post epost`). -/
def WP.wp {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type w'}
    [Assertion Pred] [Assertion EPred] [self : WP Prog Value Pred EPred]
    (x : Prog) (post : Value → Pred) (epost : EPred) : Pred :=
  (self.wpTrans x).apply post epost

/-- Weakest precondition monad: a monad `m` whose weakest precondition interpretation is sound for
`pure` and `bind`. The interpretation for every result type is carried as the `toWP` field; an
instance exposes it as a `WP (m α) …` interpretation. -/
class WPMonad (m : Type u → Type v) (Pred : outParam (Type w)) (EPred : outParam (Type w'))
    [Monad m] [Assertion Pred] [Assertion EPred] extends LawfulMonad m where
  /-- The weakest precondition interpretation of `m` at every result type. -/
  toWP : ∀ α, WP (m α) α Pred EPred
  /-- Soundness of `pure`: the postcondition applied to `x` implies the weakest precondition of
  `pure x`. -/
  pure_le_wp_pure (x : α) (post : α → Pred) (epost : EPred) :
    post x ⊑ (toWP α).wp (pure (f := m) x) post epost
  /-- Soundness of `bind`: composing weakest preconditions is at least as strong as the weakest
  precondition of `>>=`. -/
  bind_le_wp_bind (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    (toWP α).wp x (fun a => (toWP β).wp (f a) post epost) epost ⊑ (toWP β).wp (x >>= f) post epost

/-- A monadic `WP` interpretation is sourced from the monad's `WPMonad` instance. Low priority so a
program type with a bespoke `WP` instance (e.g. a non-monadic one) is preferred. -/
instance (priority := low)
    {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} {α : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [inst : WPMonad m Pred EPred] :
    WP (m α) α Pred EPred :=
  inst.toWP α

-- `wp x post epost` computes the weakest precondition; it is `WP.wp` with the interpretation
-- synthesised as an instance.
export Std.Internal.Do.WP (wp)

@[simp, grind =] theorem WP.wpTrans_apply_eq {Prog : Type u} {Value : Type v}
    [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred] (x : Prog) :
  (WP.wpTrans x).apply = wp x := rfl

/-!
## Derived WP Lemmas

Monotonicity and weakening consequences of the `WP` monotonicity axiom.
-/

namespace WP

variable {Prog : Type u} {Value : Type v} [Assertion Pred] [Assertion EPred]
  [WP Prog Value Pred EPred]

theorem wp_consequence (x : Prog)
  (post post' : Value → Pred) (epost : EPred) (h : post ⊑ post') :
    wp x post epost ⊑ wp x post' epost :=
  wp_trans_monotone x post post' epost epost PartialOrder.rel_refl h

theorem wp_consequence_econs (x : Prog)
  (post post' : Value → Pred) (epost epost' : EPred) (h : post ⊑ post') (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post' epost' :=
  wp_trans_monotone x post post' epost epost' h' h

theorem wp_econs (x : Prog)
  (post : Value → Pred) (epost epost' : EPred) (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post epost' :=
  wp_trans_monotone x post post epost epost' h' PartialOrder.rel_refl

theorem wp_econs_bot (x : Prog)
  (post : Value → Pred) (epost : EPred) :
    wp x post ⊥ ⊑ wp x post epost := by
  solve_by_elim [wp_econs, bot_le]

theorem wp_consequence_le (x : Prog)
  (post post' : Value → Pred) (epost : EPred) (h : post ⊑ post') {pre : Pred}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post' epost :=
  PartialOrder.rel_trans h' (wp_consequence x post post' epost h)

theorem wp_econs_le (x : Prog)
  (post : Value → Pred) (epost epost' : EPred) (h : epost ⊑ epost') {pre : Pred}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post epost' :=
  PartialOrder.rel_trans h' (wp_econs x post epost epost' h)

theorem wp_econs_bot_le (x : Prog)
  (post : Value → Pred) (epost : EPred) {pre : Pred} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post epost :=
  PartialOrder.rel_trans h (wp_econs_bot x post epost)

end WP

/-- Rewriting the program of a weakest precondition along an equation `x = y` weakens it:
the precondition of `y` entails the precondition of `x`. -/
theorem wp_le_wp_of_eq {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
    [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    {x y : Prog} (h : x = y) (post : Value → Pred) (epost : EPred) :
    wp y post epost ⊑ wp x post epost := by
  subst h; exact PartialOrder.rel_refl

/-!
## Derived WPMonad Lemmas

One-directional consequences of the `WPMonad` axioms for `pure`, `bind`, `map`, and `seq`.
-/

namespace WPMonad

variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- Soundness of `Functor.map`: mapping `f` over `x` preserves the WP. -/
theorem map_le_wp_map (f : α → β) (x : m α) :
  ∀ post epost, wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost := by
  intro post epost
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left
  exact bind_le_wp_bind x (pure <| f ·) post epost
  apply WP.wp_consequence
  intro a; exact pure_le_wp_pure (f a) post epost

/-- Variant of `map_le_wp_map` with an explicit postcondition equality hypothesis. -/
theorem map_le_wp_map' (f : α → β) (x : m α) :
  ∀ post post' epost (_ : post = fun a => post' (f a)),
    wp x post epost ⊑ wp (f <$> x) post' epost := by
  intro post post' epost h
  subst h
  apply map_le_wp_map

/-- Soundness of `Seq.seq`: sequencing `f <*> x` preserves the WP. -/
theorem seq_le_wp_seq (f : m (α → β)) (x : m α) :
  ∀ post epost,
    wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑
      wp (f <*> x) post epost := by
  intro post epost
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (bind_le_wp_bind f (fun g => g <$> x) post epost)
  apply WP.wp_consequence; intro g; exact map_le_wp_map g x post epost

end WPMonad

/-!
## WPMonad Instances
-/

/-- `Id`'s `WP` interpretation: `Prop` assertions and no exceptions. -/
@[instance_reducible] def Id.wpInst {α : Type u} : WP (Id α) α Prop EPost.Nil where
  wpTrans x := ⟨fun post _epost => post x⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x

/-- `Id` is a WPMonad with `Prop` assertions and no exceptions. -/
instance Id.instWPMonad : WPMonad Id.{u} Prop EPost.Nil where
  toWP _ := Id.wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl

@[simp, grind =]
theorem PredTrans.apply_pushExcept {α ε Pred EPred}
    (x : PredTrans Pred EPred (Except ε α)) (post : α → Pred)
    (epost : EPost.Cons (ε → Pred) EPred) :
    (PredTrans.pushExcept x).apply post epost = x.apply (epost.pushExcept post) epost.tail := rfl

/-- `ExceptT`'s `WP` interpretation: lift the base interpretation by adding an exception
postcondition layer. -/
@[instance_reducible] def ExceptT.wpInst {Pred : Type v}
  [Assertion Pred] [Assertion EPred] [WP (m (Except ε α)) (Except ε α) Pred EPred] :
    WP (ExceptT ε m α) α Pred (EPost.Cons (ε → Pred) EPred) where
  wpTrans x := PredTrans.pushExcept (WP.wpTrans x.run)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    change wp x.run (epost.pushExcept post) epost.tail ⊑
           wp x.run (epost'.pushExcept post') epost'.tail
    have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
      simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
    let hhead := hepost'.1
    let htail := hepost'.2
    apply WP.wp_consequence_econs (x := x.run)
    · intro r
      cases r with
      | ok a => exact hpost a
      | error el => exact hhead el
    · exact htail

/-- `ExceptT` lifts a `WPMonad` instance by adding an exception postcondition layer. -/
instance ExceptT.instWPMonad {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (ExceptT ε m) Pred (EPost.Cons (ε → Pred) EPred) where
  toWP _ := ExceptT.wpInst
  pure_le_wp_pure x := fun post epost =>
    WPMonad.pure_le_wp_pure (m := m) (Except.ok x) (epost.pushExcept post) epost.tail
  bind_le_wp_bind x f := fun post epost => by
    show wp x.run _ epost.tail ⊑ wp (x >>= f).run (epost.pushExcept post) epost.tail
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (epost.pushExcept post) epost.tail)
    apply WP.wp_consequence
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error el =>
      exact WPMonad.pure_le_wp_pure (m := m) (Except.error el) (epost.pushExcept post) epost.tail

@[simp, grind =]
theorem ExceptT.wp_apply_eq {α ε Pred EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : ExceptT ε m α)
  (post : α → Pred) (epost : EPost.Cons (ε → Pred) EPred) :
    wp x post epost = wp x.run (epost.pushExcept post) epost.tail := rfl

/-- `OptionT`'s `WP` interpretation: lift the base interpretation by adding a `PUnit` exception
postcondition layer. -/
@[instance_reducible] def OptionT.wpInst {Pred : Type u}
  [Assertion Pred] [Assertion EPred] [WP (m (Option α)) (Option α) Pred EPred] :
    WP (OptionT m α) α Pred (EPost.Cons Pred EPred) where
  wpTrans x := PredTrans.pushOption (WP.wpTrans x.run)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    change wp x.run (epost.pushOption post) epost.tail ⊑
           wp x.run (epost'.pushOption post') epost'.tail
    have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := hepost
    apply WP.wp_consequence_econs (x := x.run)
    · intro r; cases r with
      | some a => exact hpost a
      | none => exact hepost'.1
    · exact hepost'.2

/-- `OptionT` lifts a `WPMonad` instance by adding a `PUnit` exception postcondition layer. -/
instance OptionT.instWPMonad {Pred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (OptionT m) Pred (EPost.Cons Pred EPred) where
  toWP _ := OptionT.wpInst
  pure_le_wp_pure x := fun post epost =>
    WPMonad.pure_le_wp_pure (m := m) (some x) (epost.pushOption post) epost.tail
  bind_le_wp_bind x f := fun post epost => by
    show wp x.run _ epost.tail ⊑ wp (x >>= f).run (epost.pushOption post) epost.tail
    apply PartialOrder.rel_trans _ (WPMonad.bind_le_wp_bind (m := m) x.run _ (epost.pushOption post) epost.tail)
    apply WP.wp_consequence
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact WPMonad.pure_le_wp_pure (m := m) none (epost.pushOption post) epost.tail

@[simp, grind =]
theorem OptionT.wp_apply_eq {α : Type u} {Pred : Type u} {EPred}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : OptionT m α)
  (post : α → Pred) (epost : EPost.Cons Pred EPred) :
    wp x post epost = wp x.run (epost.pushOption post) epost.tail := rfl

/-- `StateT`'s `WP` interpretation: lift the base interpretation by adding a state argument. -/
@[instance_reducible] def StateT.wpInst {EPred : Type v} {σ : Type u} {Pred : Type w}
  [Assertion Pred] [Assertion EPred] [WP (m (α × σ)) (α × σ) Pred EPred] :
    WP (StateT σ m α) α (σ → Pred) EPred where
  wpTrans x := pushArg (WP.wpTrans <| x.run ·)
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    apply WP.wp_consequence_econs (x := x.run s)
    · intro ⟨a, s'⟩
      exact hpost a s'
    · exact hepost

/-- `StateT` lifts a `WPMonad` instance by adding a state argument. -/
instance (priority := low) StateT.instWPMonad {EPred : Type v} {σ : Type u} {Pred : Type w}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (StateT σ m) (σ → Pred) EPred where
  toWP _ := StateT.wpInst
  pure_le_wp_pure x := fun post epost s =>
    WPMonad.pure_le_wp_pure (m := m) (x, s) (fun p => post p.1 p.2) epost
  bind_le_wp_bind x f := fun post epost s => by
    apply WPMonad.bind_le_wp_bind

@[simp, grind =]
theorem StateT.wp_apply_eq {σ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : StateT σ m α)
  (post : α → σ → Pred) (epost : EPred) (s : σ) :
    wp x post epost s = wp (x.run s) (fun (a, s) => post a s) epost := rfl

/-- `ReaderT`'s `WP` interpretation: lift the base interpretation by adding a reader argument. -/
@[instance_reducible] def ReaderT.wpInst {Pred : Type v}
  [Assertion Pred] [Assertion EPred] [WP (m α) α Pred EPred] :
    WP (ReaderT ρ m α) α (ρ → Pred) EPred where
  wpTrans x := ⟨fun post epost r => wp (x.run r) (fun a => post a r) epost⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost r => by
    apply WP.wp_consequence_econs (x := x.run r)
    · intro a
      exact hpost a r
    · exact hepost

/-- `ReaderT` lifts a `WPMonad` instance by adding a reader argument. -/
instance ReaderT.instWPMonad {Pred : Type v}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
    WPMonad (ReaderT ρ m) (ρ → Pred) EPred where
  toWP _ := ReaderT.wpInst
  pure_le_wp_pure x := fun post epost r =>
    WPMonad.pure_le_wp_pure (m := m) x (fun a => post a r) epost
  bind_le_wp_bind x f := fun post epost r => by
    apply PartialOrder.rel_trans
    · apply WP.wp_consequence
      intro a; exact PartialOrder.rel_refl
    · apply WPMonad.bind_le_wp_bind

@[simp, grind =]
theorem ReaderT.wp_apply_eq {ρ : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (x : ReaderT ρ m α)
  (post : α → ρ → Pred) (epost : EPred) (r : ρ) :
    wp x post epost r = wp (x.run r) (fun a => post a r) epost := rfl

/-!
## Type Alias Instances

`WPMonad` instances for concrete monads that are type aliases for transformer stacks.
-/

/-- `Option`'s `WP` interpretation: `Prop` assertions and a single `Prop` exception postcondition. -/
@[instance_reducible] def Option.wpInst {α : Type u} : WP (Option α) α Prop Prop where
  wpTrans x := ⟨fun post epost => x.elim epost post⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | none => exact hepost
    | some a => exact hpost a

/-- `Option` is a WPMonad with `Prop` assertions and a single `Prop` exception postcondition. -/
instance Option.instWPMonad : WPMonad Option.{u} Prop Prop where
  toWP _ := Option.wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost => by cases x <;> exact id

/-- `Except ε`'s `WP` interpretation: `Prop` assertions and a single exception postcondition. -/
@[instance_reducible] def Except.wpInst {α : Type u} : WP (Except ε α) α Prop EPost⟨ε → Prop⟩ where
  wpTrans x := ⟨fun post epost => match x with
    | .ok a => post a
    | .error el => epost.head el⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | ok a => exact hpost a
    | error el =>
      have hhead : epost.head ⊑ epost'.head := by
        have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
          simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
        exact hepost'.1
      exact hhead el

/-- `Except ε` is a WPMonad with `Prop` assertions and a single exception postcondition. -/
instance Except.instWPMonad : WPMonad (Except ε) Prop EPost⟨ε → Prop⟩ where
  toWP _ := Except.wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost => by cases x <;> exact id

/-- `EStateM ε σ`'s `WP` interpretation combining state and exceptions. -/
@[instance_reducible] def EStateM.wpInst {α : Type} : WP (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop) where
  wpTrans x := ⟨fun post epost s => match x s with
    | .ok a s' => post a s'
    | .error el s' => epost el s'⟩
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    cases hxs : x s with
    | ok a s' =>
      simpa [hxs] using hpost a s'
    | error el s' =>
      simpa [hxs] using hepost el s'

/-- `EStateM ε σ` is a WPMonad combining state and exceptions. -/
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  toWP _ := EStateM.wpInst
  pure_le_wp_pure x := fun post epost s => PartialOrder.rel_refl
  bind_le_wp_bind x f := fun post epost s => by
    simp only [WP.wp, WP.wpTrans, bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl

/-!
## Soundness Lemmas

These lemmas bridge `wp` reasoning to concrete program properties. Each one says:
if `wp prog ...` holds, then a property `P` holds of the program's result.
-/

/-- Soundness for `Id`: if `wp prog P` holds, then `P` holds of the result. -/
theorem Id.of_wp_run_eq {α : Type u} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P EPost.Nil.mk) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `Option`: if `wp prog P` holds, then `P` holds of the result. -/
theorem Option.of_wp_eq {α : Type u} {x prog : Option α}
  (h : prog = x) (P : Option α → Prop)
  (hwp : wp prog (fun a => P (some a)) (P none)) : P x := by
  subst h
  cases prog with
  | none => exact hwp
  | some a => exact hwp

/-- Soundness for `StateM`: if `wp prog P s` holds, then `P` holds of `(prog.run s)`. -/
theorem StateM.of_wp_run_eq {x : α × σ} {prog : StateM σ α} {s : σ}
  (h : StateT.run prog s = x) (P : α × σ → Prop)
  (hwp : wp prog (fun a s' => P (a, s')) EPost.Nil.mk s) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `StateM` (discarding final state). -/
theorem StateM.of_wp_run'_eq {α σ : Type} {x : α} {prog : StateM σ α} {s : σ}
  (h : StateT.run' prog s = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.Nil.mk s) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `ReaderM`: if `wp prog P r` holds, then `P` holds of `(prog.run r)`. -/
theorem ReaderM.of_wp_run_eq {α ρ : Type} {x : α} {prog : ReaderM ρ α} {r : ρ}
  (h : ReaderT.run prog r = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.Nil.mk r) : P x := by
  rw [← h]
  exact hwp

/-- Soundness for `Except`: if `wp prog P` holds, then `P` holds of the result. -/
theorem Except.of_wp_eq {ε α : Type} {x prog : Except ε α}
  (h : prog = x) (P : Except ε α → Prop)
  (hwp : wp prog (fun a => P (.ok a)) epost⟨fun e => P (.error e)⟩) : P x := by
  subst h
  cases prog with
  | ok a => simpa only [wp] using! hwp
  | error e => simpa only [wp] using! hwp

/-- Soundness for `EStateM`: if `wp prog P s` holds, then `P` holds of `(prog.run s)`. -/
theorem EStateM.of_wp_run_eq {ε σ α : Type} {x : EStateM.Result ε σ α}
  {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) :
    P x := by
  rw [← h]
  change P (prog s)
  cases heq : prog s with
  | ok a s' =>
    simpa [wp, WP.wpTrans, heq] using hwp
  | error e s' =>
    simpa [wp, WP.wpTrans, heq] using hwp

end Std.Internal.Do
