/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Core

public section

/-!
# Notation for `while` and `repeat` loops.
-/

namespace Lean

/-! # `repeat` and `while` notation -/

inductive Loop where
  | mk

private def LoopSpec (m : Type u → Type v) (σ : Type u) (loop : ∀ {β}, (Unit → (σ → m β) → σ → m β) → (σ → m β) → σ → m β) :=
  ∀ {β γ} (k : m β → m γ) (s : σ)
    (knil : σ → m β)
    (kcons₁ : Unit → (kcontinue : σ → m β) → σ → m β)
    (kcons₂ : Unit → (kcontinue : σ → m γ) → σ → m γ)
    (_ : ∀ kcontinue s, k (kcons₁ () kcontinue s) = kcons₂ () (fun s => k (kcontinue s)) s),
    k (loop kcons₁ knil s) = loop kcons₂ (fun s => k (knil s)) s

private local instance : Inhabited (Subtype (LoopSpec m σ)) :=
  ⟨fun kcons knil s => knil s, by (repeat intro); rfl⟩

private partial def Loop.forInNew.loop {m : Type u → Type v} {σ} : Subtype (LoopSpec m σ) where
  val {β} kcons knil s :=
    -- This is the actual definition of the loop:
    haveI : Nonempty (m β) := ⟨knil s⟩
    kcons () (loop.val kcons knil) s
  property := by
    intro β γ k s knil kcons₁ kcons₂ h;
    simp [h]
    congr
    apply funext
    intro s
    simp [loop.property k s knil kcons₁ kcons₂ h]
    rfl

@[specialize]
private unsafe def Loop.forInNewUnsafe {m : Type u → Type v} {β σ : Type u} (init : σ)
    (kcons : Unit → (σ → m β) → σ → m β) (knil : σ → m β) : m β :=
  kcons () (forInNewUnsafe · kcons knil) init

@[implemented_by Loop.forInNewUnsafe]
def Loop.forInNew {m : Type u → Type v} {β σ : Type u} (init : σ)
    (kcons : Unit → (σ → m β) → σ → m β) (knil : σ → m β) : m β :=
  Loop.forInNew.loop.val kcons knil init

instance : ForInNew m Loop Unit where
  forInNew _ := Loop.forInNew
  forInNew_tail := by
    intros _ _ _ _ _ _ _ _ _ h
    apply Loop.forInNew.loop.property _ _ _ _ _ (h ())

@[inline]
partial def Loop.forIn {β : Type u} {m : Type u → Type v} [Monad m] (_ : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  loop init

instance [Monad m] : ForIn m Loop Unit where
  forIn := Loop.forIn

syntax "repeat " doSeq : doElem

macro_rules
  | `(doElem| repeat $seq) => `(doElem| for _ in Loop.mk do $seq)

syntax "while " ident " : " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $h : $cond do $seq) => `(doElem| repeat if $h:ident : $cond then $seq else break)

syntax "while " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $cond do $seq) => `(doElem| repeat if $cond then $seq else break)

syntax "repeat " doSeq ppDedent(ppLine) "until " term : doElem

macro_rules
  | `(doElem| repeat $seq until $cond) => `(doElem| repeat do $seq:doSeq; if $cond then break)

end Lean
