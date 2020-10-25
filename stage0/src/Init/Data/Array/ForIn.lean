/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic

namespace Array
universes u v w

/-
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.

  This kind of low level trick can be removed with a little bit of compiler support. For example, if the compiler simplifies `as.size < usizeSz` to true. -/
@[inline] unsafe def forInUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  let sz := USize.ofNat as.size
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

-- Move?
private theorem zeroLtOfLt : {a b : Nat} → a < b → 0 < b
  | 0,   _, h => h
  | a+1, b, h =>
    have a < b from Nat.ltTrans (Nat.ltSuccSelf _) h
    zeroLtOfLt this

/- Reference implementation for `Array.forIn` -/
@[implementedBy Array.forInUnsafe]
def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size          from Nat.ltOfLtOfLe (Nat.ltSuccSelf i) h
      have as.size - 1 < as.size     from Nat.subLt (zeroLtOfLt h') (decide! : 0 < 1)
      have as.size - 1 - i < as.size from Nat.ltOfLeOfLt (Nat.subLe (as.size - 1) i) this
      match (← f (as.get ⟨as.size - 1 - i, this⟩) b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.leOfLt h') b
  loop as.size (Nat.leRefl _) b

end Array
