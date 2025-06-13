module

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Iterators
import Init.Data.Range.New.Classes

import Init.Data.Range.New.RangeIterator

open Std.Iterators

inductive BoundShape where
  | «open» : BoundShape
  | closed : BoundShape
  | none : BoundShape

structure RangeShape where
  lower : BoundShape
  upper : BoundShape

abbrev Bound (shape : BoundShape) (α : Type u) : Type u :=
  match shape with
  | .open | .closed => α
  | .none => PUnit

structure PRange (shape : RangeShape) (α : Type u) where
  lower : Bound shape.lower α
  upper : Bound shape.upper α

syntax:max (term ",," term) : term
syntax:max (",," term) : term
syntax:max (term ",,") : term
syntax:max (",,") : term
syntax:max (term "<,," term) : term
syntax:max (term "<,,") : term
syntax:max (term ",,<" term) : term
syntax:max (",,<" term) : term
syntax:max (term "<,,<" term) : term

macro_rules
  | `($a,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.closed) $a $b)
  | `(,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.closed) PUnit.unit $b)
  | `($a,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.none) $a PUnit.unit)
  | `(,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.none) PUnit.unit PUnit.unit)
  | `($a<,,$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.closed) $a $b)
  | `($a<,,) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.none) $a PUnit.unit)
  | `($a,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.closed BoundShape.open) $a $b)
  | `(,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.none BoundShape.open) PUnit.unit $b)
  | `($a<,,<$b) => ``(PRange.mk (shape := RangeShape.mk BoundShape.open BoundShape.open) $a $b)

class RangeIter (shape : RangeShape) (α : Type u) where
  State : PRange shape α → Type u
  iter : (r : PRange shape α) → Iter (α := State r) α

@[always_inline, inline, expose]
def RangeIter.of {State : PRange shape α → Type u}
    (iter : (r : PRange shape α) → Iter (α := State r) α) :
    RangeIter shape α where
  State := State
  iter := iter

instance {State : PRange shape α → Type u}
    {r : PRange shape α} [Iterator (State r) Id α]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    Iterator (RangeIter.State (shape := shape) (α := α) r) Id α :=
  inferInstanceAs <| Iterator (State r) Id α

instance {State : PRange shape α → Type u} {r : PRange shape α}
    [Iterator (State r) Id α]
    [Finite (State r) Id]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    Finite (RangeIter.State (shape := shape) (α := α) r) Id :=
  inferInstanceAs <| Finite (State r) Id

instance {State : PRange shape α → Type u} {r : PRange shape α}
    [Iterator (State r) Id α] [IteratorCollect (State r) Id m]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    IteratorCollect (RangeIter.State r) Id m :=
  inferInstanceAs <| IteratorCollect (State r) Id m

instance {State : PRange shape α → Type u} {r : PRange shape α}
    [Iterator (State r) Id α] [IteratorCollectPartial (State r) Id m]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    IteratorCollectPartial (RangeIter.State r) Id m :=
  inferInstanceAs <| IteratorCollectPartial (State r) Id m

instance {State : PRange shape α → Type u} {r : PRange shape α}
    [Iterator (State r) Id α] [IteratorLoop (State r) Id m]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    IteratorLoop (RangeIter.State r) Id m :=
  inferInstanceAs <| IteratorLoop (State r) Id m

instance {State : PRange shape α → Type u} {r : PRange shape α}
    [Iterator (State r) Id α] [IteratorLoopPartial (State r) Id m]
    {iter : (r : PRange shape α) → Iter (α := State r) α} :
    letI : RangeIter shape α := RangeIter.of iter
    IteratorLoopPartial (RangeIter.State r) Id m :=
  inferInstanceAs <| IteratorLoopPartial (State r) Id m

@[always_inline, inline]
def PRange.iter [RangeIter shape α] (r : PRange shape α) :=
  (RangeIter.iter r : Iter α)

@[always_inline, inline]
def PRange.size [RangeIter shape α] (r : PRange shape α)
    [Iterator (RangeIter.State r) Id α] [IteratorSize (RangeIter.State r) Id] :
    Nat :=
  r.iter.size

instance [i : RangeIter shape α] [∀ r, ForIn m (Iter (α := i.State r) α) α] :
    ForIn m (PRange shape α) α where
  forIn r := forIn r.iter

instance : Membership α (PRange ⟨.none, .none⟩ α) where
  mem _ _ := True

instance (r : PRange ⟨.none, .none⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable True

instance [LT α] : Membership α (PRange ⟨.none, .open⟩ α) where
  mem r a := a < r.upper

instance [LT α] [DecidableLT α] (r : PRange ⟨.none, .open⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (a < r.upper)

instance [LE α] : Membership α (PRange ⟨.none, .closed⟩ α) where
  mem r a := a ≤ r.upper

instance [LE α] [DecidableLE α] (r : PRange ⟨.none, .closed⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (a ≤ r.upper)

instance [LT α] : Membership α (PRange ⟨.open, .none⟩ α) where
  mem r a := r.lower < a

instance [LT α] [DecidableLT α] (r : PRange ⟨.open, .none⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (r.lower < a)

instance [LT α] : Membership α (PRange ⟨.open, .open⟩ α) where
  mem r a := r.lower < a ∧ a < r.upper

instance [LT α] [DecidableLT α] (r : PRange ⟨.open, .open⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (r.lower < a ∧ _)

instance [LT α] [LE α] : Membership α (PRange ⟨.open, .closed⟩ α) where
  mem r a := r.lower < a ∧ a ≤ r.upper

instance [LT α] [DecidableLT α] [LE α] [DecidableLE α] (r : PRange ⟨.open, .closed⟩ α) :
    Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)

instance [LE α] : Membership α (PRange ⟨.closed, .none⟩ α) where
  mem r a := r.lower ≤ a

instance [LE α] [DecidableLE α] (r : PRange ⟨.closed, .none⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (r.lower ≤ a)

instance [LE α] [LT α] : Membership α (PRange ⟨.closed, .open⟩ α) where
  mem r a := r.lower ≤ a ∧ a < r.upper

instance [LT α] [DecidableLT α] [LE α] [DecidableLE α] (r : PRange ⟨.closed, .open⟩ α) :
    Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)

instance [LE α] : Membership α (PRange ⟨.closed, .closed⟩ α) where
  mem r a := r.lower ≤ a ∧ a ≤ r.upper

instance [LE α] [DecidableLE α] (r : PRange ⟨.closed, .closed⟩ α) : Decidable (a ∈ r) :=
  inferInstanceAs <| Decidable (_ ∧ _)


section Iterator

@[always_inline, inline]
def Range.succIterator [Succ? α] (init : Option α) (Predicate : α → Bool) :
    (Iter (α := Types.RangeIterator α inferInstance Predicate) α) :=
  ⟨⟨init⟩⟩

-- @[always_inline, inline]
-- def Range.SuccIterator.next [Succ? α] (stepSize : Nat) (Predicate : α → Bool)
--     {h : stepSize > 0} (it : SuccIterator stepSize Predicate h) : α :=
--   it.inner.internalState.next

-- @[no_expose]
-- instance [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     Iterator (Range.SuccIterator stepSize Predicate h) Id α := by
--   unfold Range.SuccIterator
--   infer_instance

-- @[no_expose]
-- instance [Monad m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorCollect (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- @[no_expose]
-- instance [Monad m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorCollectPartial (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- @[no_expose]
-- instance [Monad m] [MonadLiftT Id m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorLoop (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- @[no_expose]
-- instance [Monad m] [MonadLiftT Id m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorLoopPartial (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- TODO: Should we hide the ≤ or < predicates behind some identifier to avoid accidental rewriting?
@[expose]
instance [Succ? α] [LE α] [DecidableLE α] : RangeIter ⟨.closed, .closed⟩ α :=
  .of fun r => Range.succIterator (some r.lower) (fun a => a ≤ r.upper)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.closed, .open⟩ α :=
  .of fun r => Range.succIterator (some r.lower) (fun a => a < r.upper)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.closed, .none⟩ α :=
  .of fun r => Range.succIterator (some r.lower) (fun _ => True)

instance [Succ? α] [LE α] [DecidableLE α] : RangeIter ⟨.open, .closed⟩ α :=
  .of fun r => Range.succIterator (Succ?.succ? r.lower) (fun a => a ≤ r.upper)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .open⟩ α :=
  .of fun r => Range.succIterator (Succ?.succ? r.lower) (fun a => a < r.upper)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .none⟩ α :=
  .of fun r => Range.succIterator (Succ?.succ? r.lower) (fun _ => True)

instance [Succ? α] [LE α] [DecidableLE α] [HasDownwardUnboundedRanges α] :
    RangeIter ⟨.none, .closed⟩ α :=
  .of fun r => Range.succIterator (some HasDownwardUnboundedRanges.min) (· ≤ r.upper)

-- TODO: iterators for ranges that are unbounded downwards

-- theorem Range.SuccIterator.succ?_eq_some_of_isPlausibleSuccessorOf [Succ? α] [LE α] [DecidableLE α]
--     {it' it : Iter (α := Types.RangeIterator α inferInstance P) α}
--     [Finite (Types.RangeIterator α inferInstance P) Id]
--     (h' : it'.IsPlausibleSuccessorOf it) :
--     Succ?.succ? 1 it.internalState.next = some it'.internalState.next :=
--   h' |>
--     TakeWhile.isPlausibleSuccessorOf_inner_of_isPlausibleSuccessorOf |>
--     RepeatIterator.Monadic.next_eq_some_of_isPlausibleSuccessorOf

@[no_expose]
instance [Succ? α] [LE α] [DecidableLE α] [LawfulLESucc? α] [Monad m]
    [∀ a, Finite (Types.RangeIterator α inferInstance (· ≤ a)) Id] :
    ForIn' m (PRange ⟨.closed, .closed⟩ α) α inferInstance where
  forIn' r init f := by
    haveI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
    refine ForIn'.forIn' (α := α) r.iter init (fun a ha acc => f a ?_ acc)
    sorry
    -- have hle : r.lower ≤ r.iter.internalState.next := by exact LawfulLESucc?.le_rfl (α := α)
    -- generalize r.iter = it at ha hle
    -- induction ha with
    -- | direct =>
    --   rename_i it out h
    --   rcases h with ⟨it', h, h'⟩
    --   refine ⟨?_, ?_⟩
    --   · rcases h with ⟨rfl, _⟩
    --     exact hle
    --   · simpa [← PostconditionT.pure_eq_pure] using h'
    -- | indirect =>
    --   rename_i it it' it'' out h h' ih
    --   apply ih
    --   replace h := Range.SuccIterator.succ?_eq_some_of_isPlausibleSuccessorOf h
    --   exact LawfulLESucc?.le_succAtIdx?_of_le (α := α) hle h

@[no_expose]
instance [Succ? α] [LT α] [DecidableLT α] [LE α] [DecidableLE α] [LawfulLESucc? α] [Monad m]
    [∀ a, Finite (Types.RangeIterator α inferInstance (· < a)) Id] :
    ForIn' m (PRange ⟨.closed, .open⟩ α) α inferInstance where
  forIn' r init f := by
    haveI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
    refine ForIn'.forIn' (α := α) r.iter init (fun a ha acc => f a ?_ acc)
    sorry
    -- have hle : r.lower ≤ r.iter.internalState.next := by exact LawfulLESucc?.le_rfl (α := α)
    -- generalize r.iter = it at ha hle
    -- induction ha with
    -- | direct =>
    --   rename_i it out h
    --   rcases h with ⟨it', h, h'⟩
    --   refine ⟨?_, ?_⟩
    --   · rcases h with ⟨rfl, _⟩
    --     exact hle
    --   · simpa [← PostconditionT.pure_eq_pure] using h'
    -- | indirect =>
    --   rename_i it it' it'' out h h' ih
    --   apply ih
    --   replace h := Range.SuccIterator.succ?_eq_some_of_isPlausibleSuccessorOf h
    --   exact LawfulLESucc?.le_succAtIdx?_of_le (α := α) hle h

-- instance [Succ? α] [LE α] [DecidableLE α] [LawfulLESucc? α]
--     [HasDownwardUnboundedRanges α] [Monad m]
--     [∀ a h, Finite (Range.SuccIterator (α := α) 1  (· ≤ a) h) Id] :
--     ForIn' m (PRange ⟨.none, .closed⟩ α) α inferInstance where
--   forIn' r init f :=
--     ForIn'.forIn' (HasDownwardUnboundedRanges.min,,r.upper) init
--       fun out h acc => f out (by exact h.2) acc

end Iterator

theorem Range.mem.upper [LE α] {i : α} {r : PRange ⟨.none, .closed⟩ α} (h : i ∈ r) : i ≤ r.upper :=
  h

-- theorem Range.mem.lower [LE α] {i : α} {r : PRange ⟨.none, .closed⟩ α} (h : i ∈ r) : r.lower ≤ i := h.1

-- theorem Range.mem.step {i : Nat} {r : PRange shape α} (h : i ∈ r) : (i - r.start) % r.step = 0 := h.2.2

theorem Range.get_elem_helper {i n : Nat} {r : PRange ⟨.closed, .open⟩ Nat} (h₁ : i ∈ r) (h₂ : r.upper = n) :
    i < n := h₂ ▸ h₁.2

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| apply Range.get_elem_helper; assumption; rfl)
