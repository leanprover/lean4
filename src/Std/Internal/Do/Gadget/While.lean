/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.SpecLemmas

/-!
# `while` loop-invariant gadget

`Loop.forInWithInvariant` annotates a `while` loop with its termination measure, its loop invariant
and the negation of its loop condition, so that `vcgen` reads all three from the program. The gadget
comes first, then the `@[spec]` specification that restates `Spec.forIn_loop` for the annotation.
-/

@[expose] public section

namespace Std.Internal.Do

open Lean.Order

universe u v uₚ uₑ
variable {β : Type u} {m : Type u → Type v} {Pred : Type uₚ} {EPred : Type uₑ}
variable [Monad m] [MonadTail m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

set_option linter.unusedVariables false in
/-- A `while` loop annotated with the data `vcgen` needs to verify it: a `Nat`-valued termination
`measure` that strictly decreases on every iteration, the loop invariant `inv` that holds before
every test of the loop condition, and `onExit`, the negated loop condition that holds once the loop
is left. It is definitionally `forIn l init f`, so the annotation is erased at runtime. -/
@[inline] def Loop.forInWithInvariant (l : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β))
    (measure : RepeatVariant β) (inv : β → Pred) (onExit : β → Prop) : m β :=
  forIn l init f

/-- Specification for an annotated `while` loop. The step `Triple` either continues with a strictly
smaller measure and the invariant restored, or leaves the loop with the invariant and `onExit`. -/
@[spec]
theorem Spec.forInWithInvariant_loop {l : Lean.Loop} {init : β} {f : Unit → β → m (ForInStep β)}
    (measure : RepeatVariant β) (inv : β → Pred) (onExit : β → Prop)
    (einv : EPred)
    (step : ∀ b,
      Triple
        (f () b)
        (inv b)
        (fun r => match r with
          | .yield b' => ⌜measure b' < measure b⌝ ⊓ inv b'
          | .done b' => inv b' ⊓ ⌜onExit b'⌝)
        einv) :
    Triple
      (Loop.forInWithInvariant l init f measure inv onExit)
      (inv init)
      (fun b => inv b ⊓ ⌜onExit b⌝)
      einv := by
  unfold Loop.forInWithInvariant
  exact Spec.forIn_loop measure
    (fun c => match c with | .inl b => inv b | .inr b => inv b ⊓ ⌜onExit b⌝) einv step

end Std.Internal.Do
