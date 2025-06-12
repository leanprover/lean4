module

prelude
import Init.Data.Iterators.Internal.Termination
import Init.Data.Iterators.Consumers.Loop
import Init.Data.Iterators.Consumers.Collect

open Std.Iterators

namespace Std.Iterators.Types

@[unbox]
structure RangeIterator (α : Type u) (succ? : α → Option α) (P : α → Bool) where
  next : Option α

variable {α : Type u} {succ? : α → Option α} {P : α → Bool}

@[always_inline, inline]
def RangeIterator.step (it : IterM (α := RangeIterator α succ? P) Id α) :
    IterStep (IterM (α := RangeIterator α succ? P) Id α) α :=
  match it.internalState.next with
  | none => .done
  | some a => if P a then .yield ⟨⟨succ? a⟩⟩ a else .done

@[always_inline, inline]
instance : Iterator (RangeIterator α succ? P) Id α where
  IsPlausibleStep it step := step = RangeIterator.step it
  step it := pure ⟨RangeIterator.step it, rfl⟩

@[always_inline, inline]
instance RepeatIterator.instIteratorLoop {n : Type u → Type w} [Monad n] :
    IteratorLoop (RangeIterator α succ? P) Id n where
  forIn lift γ plausible_forInStep wf it init f :=
    let rec @[specialize] loop (a : α) (c : γ) : n γ := do
      if P a then
        match ← f a sorry c with
        | ⟨.yield c', _⟩ => match (succ? a) with
          | none => pure c'
          | some a' => loop a' c'
        | ⟨.done c', _⟩ => pure c'
      else
        return init
    termination_by a
    decreasing_by all_goals sorry
    match it.internalState.next with
    | none => pure init
    | some a => loop a init

instance RepeatIterator.instIteratorLoopPartial {n : Type u → Type w}
    [Monad n] : IteratorLoopPartial (RangeIterator α succ? P) Id n :=
  .defaultImplementation

instance RepeatIterator.instIteratorCollect {n : Type u → Type w}
    [Monad n] : IteratorCollect (RangeIterator α succ? P) Id n :=
  .defaultImplementation

instance RepeatIterator.instIteratorCollectPartial {n : Type u → Type w}
    [Monad n] : IteratorCollectPartial (RangeIterator α succ? P) Id n :=
  .defaultImplementation

instance RepeatIterator.instFinite : Finite (RangeIterator α succ? P) Id := sorry

abbrev test : ForIn Id (Iter (α := RangeIterator α succ? p) α) α :=
  inferInstance

@[always_inline, inline]
def test' : ForIn Id.{u} (Iter (α := RangeIterator α succ? P) α) α where
  forIn {γ _} it init f :=
    let rec @[specialize] loop (a : α) (c : γ) : Id γ := do
      if P a then
        match ← f a c with
        | .yield c' => match succ? a with
          | none => pure c'
          | some a' => loop a' c'
        | .done c' => pure c'
      else
        pure c
    termination_by a
    decreasing_by all_goals sorry
    match it.internalState.next with
    | none => pure init
    | some a => loop a init

@[csimp]
theorem aaa : @test = @test' := sorry

@[always_inline, inline]
instance test'' :
    ForIn Id.{u} (Iter (α := RangeIterator α succ? p) α) α :=
  test

def it := (⟨⟨some 0⟩⟩ : Iter (α := RangeIterator Nat (some <| · + 1) (· < 5)) Nat)

set_option trace.compiler.ir true in
set_option compiler.small 1000 in
def f (it : Iter (α := RangeIterator Nat (some <| · + 1) (· < 5)) Nat) : Nat := Id.run do
  let mut acc := 0
  for x in it do
    acc := acc + x
  return acc

#eval! f it

#eval! it.toList

end Std.Iterators.Types
