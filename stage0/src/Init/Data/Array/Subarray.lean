/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic

universes u v w

structure Subarray (α : Type u)  :=
  (as : Array α)
  (start : Nat)
  (stop : Nat)
  (h₁ : start ≤ stop)
  (h₂ : stop ≤ as.size)

namespace Subarray

@[inline] unsafe def forInUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (s : Subarray α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  let sz := USize.ofNat s.stop
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := s.as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop (USize.ofNat s.start) b

-- TODO: provide reference implementation
@[implementedBy Subarray.forInUnsafe]
constant forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (s : Subarray α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  pure b

end Subarray

namespace Array
variables {α : Type u}

def toSubarray (as : Array α) (start stop : Nat) : Subarray α :=
  if h₂ : stop ≤ as.size then
     if h₁ : start ≤ stop then
       { as := as, start := start, stop := stop, h₁ := h₁, h₂ := h₂ }
     else
       { as := as, start := stop, stop := stop, h₁ := Nat.leRefl _, h₂ := h₂ }
  else
     if h₁ : start ≤ as.size then
       { as := as, start := start, stop := as.size, h₁ := h₁, h₂ := Nat.leRefl _ }
     else
       { as := as, start := as.size, stop := as.size, h₁ := Nat.leRefl _, h₂ := Nat.leRefl _ }

def ofSubarray (s : Subarray α) : Array α := do
  let as := mkEmpty (s.stop - s.start)
  for a in s do
    as := as.push a
  return as

def extract (as : Array α) (start stop : Nat) : Array α :=
  ofSubarray (as.toSubarray  start stop)

instance : Coe (Subarray α) (Array α) := ⟨ofSubarray⟩

end Array
