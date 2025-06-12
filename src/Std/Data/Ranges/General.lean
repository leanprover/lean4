prelude
-- import Std.Data.Ranges.Basic
-- import Std.Data.Ranges.Slice
-- open Std.Iterators

-- class Succ? (α : Type u) where
--   succ? : α → Option α
--   succAtIdx? (n : Nat) (a : α) : Option α := Nat.repeat (· >>= succ?) n (some a)

-- class LawfulLESucc? (α : Type u) [LE α] [Succ? α] where
--   le_rfl : {a : α} → a ≤ a
--   le_succ?_of_le : {a b c : α} → a ≤ b → (h : Succ?.succ? b = some c) → a ≤ c
--   le_succAtIdx?_of_le : {a b c : α} → {n : Nat} → a ≤ b → (h : Succ?.succAtIdx? n b = some c) → a ≤ c

-- class LawfulLTSucc? [LT α] [Succ? α] where
--   lt_succ? : {a b : α} → (h : Succ?.succ? a = some b) → a < b
--   lt_succ?_of_lt : {a b c : α} → a < b → (h : Succ?.succ? b = some c) → a < c

-- class HasDownwardUnboundedRanges (α : Type u) where
--   min : α

-- instance : Membership α (PRange ⟨.none, .none⟩ α) where
--   mem _ _ := True

-- instance (r : PRange ⟨.none, .none⟩ α) : Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable True

-- instance [LT α] : Membership α (PRange ⟨.none, .open⟩ α) where
--   mem r a := a < r.upper

-- instance [LT α] [DecidableLT α] (r : PRange ⟨.none, .open⟩ α) : Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (a < r.upper)

-- instance [LE α] : Membership α (PRange ⟨.none, .closed⟩ α) where
--   mem r a := a ≤ r.upper

-- instance [LE α] [DecidableLE α] (r : PRange ⟨.none, .closed⟩ α) : Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (a ≤ r.upper)

-- instance [LT α] : Membership α (PRange ⟨.open, .none⟩ α) where
--   mem r a := r.lower < a

-- instance [LT α] [DecidableLT α] (r : PRange ⟨.open, .none⟩ α) : Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (r.lower < a)

-- instance [LT α] : Membership α (PRange ⟨.open, .open⟩ α) where
--   mem r a := r.lower < a ∧ a < r.upper

-- instance [LT α] [DecidableLT α] (r : PRange ⟨.open, .open⟩ α) : Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (r.lower < a ∧ _)

-- instance [LT α] [LE α] : Membership α (PRange ⟨.open, .closed⟩ α) where
--   mem r a := r.lower < a ∧ a ≤ r.upper

-- instance [LT α] [DecidableLT α] [LE α] [DecidableLE α] (r : PRange ⟨.open, .closed⟩ α) :
--     Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (_ ∧ _)

-- instance [LE α] : Membership α (PRange ⟨.closed, .none⟩ α) where
--   mem r a := r.lower ≤ a

-- instance [LE α] [DecidableLE α] (r : PRange ⟨.closed, .none⟩ α) : Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (r.lower ≤ a)

-- instance [LE α] [LT α] : Membership α (PRange ⟨.closed, .open⟩ α) where
--   mem r a := r.lower ≤ a ∧ a < r.upper

-- instance [LT α] [DecidableLT α] [LE α] [DecidableLE α] (r : PRange ⟨.closed, .open⟩ α) :
--     Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (_ ∧ _)

-- instance [LE α] : Membership α (PRange ⟨.closed, .closed⟩ α) where
--   mem r a := r.lower ≤ a ∧ a ≤ r.upper

-- instance [LE α] [DecidableLE α] (r : PRange ⟨.closed, .closed⟩ α) : Decidable (a ∈ r) :=
--   inferInstanceAs <| Decidable (_ ∧ _)


-- section Iterator

-- def Range.succIteratorInternal [Succ? α] (init : α) (stepSize : Nat) (Predicate : α → Bool) :=
--   Iter.repeatUntilNone (init := init) (Succ?.succAtIdx? stepSize) |>.takeWhile Predicate

-- def Range.SuccIterator [Succ? α] (stepSize : Nat) (Predicate : α → Bool)
--     (_ : stepSize > 0) :=
--   type_of% (succIteratorInternal (_ : α) stepSize Predicate).internalState

-- def Range.succIterator [Succ? α] (init : α) (stepSize : Nat) (Predicate : α → Bool) (h) :
--     (Iter (α := SuccIterator stepSize Predicate h) α) :=
--   Iter.repeatUntilNone (init := init) (Succ?.succAtIdx? stepSize) |>.takeWhile Predicate

-- @[always_inline, inline]
-- def Range.SuccIterator.next [Succ? α] (stepSize : Nat) (Predicate : α → Bool)
--     {h : stepSize > 0} (it : SuccIterator stepSize Predicate h) : α :=
--   it.inner.internalState.next

-- instance [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     Iterator (Range.SuccIterator stepSize Predicate h) Id α := by
--   unfold Range.SuccIterator
--   infer_instance

-- instance [Monad m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorCollect (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- instance [Monad m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorCollectPartial (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- instance [Monad m] [MonadLiftT Id m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorLoop (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- instance [Monad m] [MonadLiftT Id m] [Succ? α] (stepSize : Nat) (Predicate : α → Bool) (h) :
--     IteratorLoopPartial (Range.SuccIterator stepSize Predicate h) Id m := by
--   unfold Range.SuccIterator
--   infer_instance

-- -- TODO: Should we hide the ≤ or < predicates behind some identifier to avoid accidental rewriting?
-- instance [Succ? α] [LE α] [DecidableLE α] : RangeIter ⟨.closed, .closed⟩ α :=
--   .of fun r => Range.succIterator r.lower 1 (fun a => a ≤ r.upper) (by omega)

-- instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.closed, .open⟩ α :=
--   .of fun r => Range.succIterator r.lower 1 (fun a => a < r.upper) (by omega)

-- instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.closed, .none⟩ α :=
--   .of fun r => Range.succIterator r.lower 1 (fun _ => True) (by omega)

-- instance [Succ? α] [LE α] [DecidableLE α] : RangeIter ⟨.open, .closed⟩ α :=
--   .of fun r => Range.succIterator r.lower 1 (fun a => a ≤ r.upper) (by omega) |>.drop 1

-- instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .open⟩ α :=
--   .of fun r => Range.succIterator r.lower 1 (fun a => a < r.upper) (by omega) |>.drop 1

-- instance [Succ? α] [LT α] [DecidableLT α] : RangeIter ⟨.open, .none⟩ α :=
--   .of fun r => Range.succIterator r.lower 1 (fun _ => True) (by omega) |>.drop 1

-- instance [Succ? α] [LE α] [DecidableLE α] [HasDownwardUnboundedRanges α] :
--     RangeIter ⟨.none, .closed⟩ α :=
--   .of fun r => Range.succIterator HasDownwardUnboundedRanges.min 1 (· ≤ r.upper) (by omega)

-- -- TODO: iterators for ranges that are unbounded downwards

-- theorem Range.SuccIterator.succ?_eq_some_of_isPlausibleSuccessorOf [Succ? α] [LE α] [DecidableLE α]
--     [∀ a h, Finite (Range.SuccIterator (α := α) 1 (· ≤ a) h) Id]
--     {it' it : Iter (α := Range.SuccIterator (α := α) 1 (· ≤ a) h) α}
--     (h' : it'.IsPlausibleSuccessorOf it) :
--     Succ?.succAtIdx? 1 it.internalState.next = some it'.internalState.next :=
--   h' |>
--     TakeWhile.isPlausibleSuccessorOf_inner_of_isPlausibleSuccessorOf |>
--     RepeatIterator.Monadic.next_eq_some_of_isPlausibleSuccessorOf

-- instance [Succ? α] [LE α] [DecidableLE α] [LawfulLESucc? α] [Monad m]
--     [∀ a h, Finite (Range.SuccIterator (α := α) 1  (· ≤ a) h) Id] :
--     ForIn' m (PRange ⟨.closed, .closed⟩ α) α inferInstance where
--   forIn' r init f := by
--     haveI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
--     refine ForIn'.forIn' (α := α) r.iter init (fun a ha acc => f a ?_ acc)
--     have hle : r.lower ≤ r.iter.internalState.next := LawfulLESucc?.le_rfl
--     generalize r.iter = it at ha hle
--     induction ha with
--     | direct =>
--       rename_i it out h
--       rcases h with ⟨it', h, h'⟩
--       refine ⟨?_, ?_⟩
--       · rcases h with ⟨rfl, _⟩
--         exact hle
--       · simpa [PostconditionT.pure] using h'
--     | indirect =>
--       rename_i it it' it'' out h h' ih
--       apply ih
--       replace h := Range.SuccIterator.succ?_eq_some_of_isPlausibleSuccessorOf h
--       exact LawfulLESucc?.le_succAtIdx?_of_le (α := α) hle h

-- instance [Succ? α] [LE α] [DecidableLE α] [LawfulLESucc? α]
--     [HasDownwardUnboundedRanges α] [Monad m]
--     [∀ a h, Finite (Range.SuccIterator (α := α) 1  (· ≤ a) h) Id] :
--     ForIn' m (PRange ⟨.none, .closed⟩ α) α inferInstance where
--   forIn' r init f := by
--     haveI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
--     refine ForIn'.forIn' (α := α) r.iter init (fun a ha acc => f a ?_ acc)
--     generalize r.iter = it at ha
--     induction ha with
--     | direct =>
--       sorry
--     | indirect =>
--       sorry

-- end Iterator

-- section Examples

-- end Examples
