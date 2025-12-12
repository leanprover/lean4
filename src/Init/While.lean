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

@[inline]
partial def Loop.forInNew {m : Type u → Type v} {β σ} (_ : Loop) (init : σ)
    (kcons : Unit → (σ → m β) → σ → m β) (knil : σ → m β) : m β :=
  let rec @[specialize] loop [Nonempty (m β)] (s : σ) : m β := kcons () loop s
  haveI : Nonempty (m β) := ⟨knil init⟩
  loop init

instance : ForInNew m Loop Unit where
  forInNew := Loop.forInNew

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
