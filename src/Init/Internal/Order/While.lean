/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.While
import all Init.While
public import Init.Internal.Order.MonadTail

set_option linter.missingDocs true

/-!
# Order-theoretic unfolding for `whileM`

This module exposes the user-facing one-step unfolding lemma `whileM_eq_of_monadTail`,
which holds for any monad with a `Lean.Order.MonadTail` instance. It works by exhibiting
the order-theoretic least fixed point `Lean.Order.fix (whileM.body f)` and feeding it to
the module-internal `whileM_eq`.

The lemma does not appear in `Init.While` itself to keep that module's import closure
small; clients that want to unfold `whileM`/`Loop.forIn` should import this file.
-/

variable {α : Type u} {m : Type u → Type v} [Monad m]

/-- `whileM.body f` is monotone in its `recur` argument whenever `m` admits `MonadTail`. -/
private theorem whileM.body_monotone_of_monadTail [Lean.Order.MonadTail m] [Nonempty β]
    (f : α → m (α ⊕ β)) :
    Lean.Order.monotone (whileM.body f) :=
  fun _ _ h _ => Lean.Order.MonadTail.bind_mono_right fun
    | .inl a' => h a'
    | .inr _ => Lean.Order.PartialOrder.rel_refl

/-- One-step unfolding of `whileM` for any `MonadTail m`. -/
public theorem whileM_eq_of_monadTail [Lean.Order.MonadTail m] [Nonempty β]
    {f : α → m (α ⊕ β)} (a : α) :
    whileM f a = whileM.body f (whileM f) a :=
  have hMono := whileM.body_monotone_of_monadTail f
  whileM_eq a ⟨Lean.Order.fix (whileM.body f) hMono, (Lean.Order.fix_eq hMono).symm⟩

namespace Lean

/-- One-step unfolding of `Lean.Loop.forIn` for any `MonadTail m`. -/
public theorem Loop.forIn_eq_of_monadTail [LawfulMonad m] [Lean.Order.MonadTail m]
    {l : Loop} {b : β} {f : Unit → β → m (ForInStep β)} :
    Loop.forIn l b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => Loop.forIn l val f) := by
  haveI : Nonempty β := ⟨b⟩
  show whileM _ b = _
  rw [whileM_eq_of_monadTail]; unfold whileM.body; rw [bind_assoc]
  exact bind_congr fun
    | .done _  => by simp
    | .yield _ => by simp [Loop.forIn]

end Lean
