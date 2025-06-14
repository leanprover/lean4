module

prelude
import Init.Data.Range.New.RangeIterator

open Std.Iterators

@[always_inline, inline]
def PRange.iterInternal [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    (r : PRange shape α) :=
  (⟨⟨UpwardEnumerableRange.init r.lower, r.upper⟩⟩ : Iter (α := Types.RangeIterator shape α) α)

@[always_inline, inline]
def PRange.iter [RangeIter shape α] (r : PRange shape α) :=
  (RangeIter.iter r : Iter α)

@[always_inline, inline]
def PRange.size [RangeIter shape α] (r : PRange shape α)
    [Iterator (RangeIter.State r) Id α] [IteratorSize (RangeIter.State r) Id] :
    Nat :=
  r.iter.size

@[always_inline, inline]
def PRange.toList [RangeIter shape α] (r : PRange shape α)
    [Iterator (RangeIter.State r) Id α] [Finite (RangeIter.State r) Id]
    [IteratorCollect (RangeIter.State r) Id Id] :
    List α :=
  r.iterInternal.toList

instance [i : RangeIter shape α] [∀ r, ForIn m (Iter (α := i.State r) α) α] :
    ForIn m (PRange shape α) α where
  forIn r := forIn r.iter

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

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.closed, .unbounded⟩ α :=
  .of fun r => Range.succIterator (some r.lower) (fun _ => True)

instance [Succ? α] [LE α] [DecidableLE α] : RangeIter ⟨.open, .closed⟩ α :=
  .of fun r => Range.succIterator (Succ?.succ? r.lower) (fun a => a ≤ r.upper)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .open⟩ α :=
  .of fun r => Range.succIterator (Succ?.succ? r.lower) (fun a => a < r.upper)

instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .unbounded⟩ α :=
  .of fun r => Range.succIterator (Succ?.succ? r.lower) (fun _ => True)

instance [Succ? α] [LE α] [DecidableLE α] [HasDownwardUnboundedRanges α] :
    RangeIter ⟨.unbounded, .closed⟩ α :=
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
--     ForIn' m (PRange ⟨.unbounded, .closed⟩ α) α inferInstance where
--   forIn' r init f :=
--     ForIn'.forIn' (HasDownwardUnboundedRanges.min,,r.upper) init
--       fun out h acc => f out (by exact h.2) acc

end Iterator

theorem Range.mem.upper [LE α] {i : α} {r : PRange ⟨.unbounded, .closed⟩ α} (h : i ∈ r) : i ≤ r.upper :=
  h

-- theorem Range.mem.lower [LE α] {i : α} {r : PRange ⟨.unbounded, .closed⟩ α} (h : i ∈ r) : r.lower ≤ i := h.1

-- theorem Range.mem.step {i : Nat} {r : PRange shape α} (h : i ∈ r) : (i - r.start) % r.step = 0 := h.2.2

theorem Range.get_elem_helper {i n : Nat} {r : PRange ⟨.closed, .open⟩ Nat} (h₁ : i ∈ r) (h₂ : r.upper = n) :
    i < n := h₂ ▸ h₁.2

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| apply Range.get_elem_helper; assumption; rfl)
