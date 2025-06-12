module

prelude
import all Init.Data.Range.New.Basic

open Std.Iterators

instance : Succ? Nat where
  succ? n := some (n + 1)
  succAtIdx? k n := some (n + k)

instance : LawfulLESucc? Nat where
  le_rfl := Nat.le_refl _
  le_succ?_of_le hle h := by
    simp only [Succ?.succ?, Option.some.injEq] at h
    omega
  le_succAtIdx?_of_le {a b c n} hle h := by
    simp only [Succ?.succAtIdx?, Option.some.injEq] at h
    omega
    -- simp only [Succ?.succAtIdx?, Option.bind_eq_bind] at h
    -- induction n generalizing b c with
    -- | zero => simp_all [Nat.repeat]
    -- | succ n ih =>
    --   simp only [Nat.repeat, Option.bind_eq_some_iff] at h ih
    --   rcases h with ⟨c', hc', h⟩
    --   cases h
    --   specialize ih hle hc'
    --   omega

instance (stepSize : Nat) (h) :
    Finite (Range.SuccIterator (α := Nat) stepSize (· ≤ n) h) Id := by
  unfold Range.SuccIterator
  sorry

instance (stepSize : Nat) (h) :
    Finite (Range.SuccIterator (α := Nat) stepSize (· < n) h) Id := by
  unfold Range.SuccIterator
  sorry

instance (stepSize : Nat) (h) :
    IteratorSize (Range.SuccIterator (α := Nat) stepSize (· ≤ n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next) / stepSize

instance (stepSize : Nat) (h) :
    IteratorSizePartial (Range.SuccIterator (α := Nat) stepSize (· ≤ n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next) / stepSize

instance (stepSize : Nat) (h) :
    IteratorSize (Range.SuccIterator (α := Nat) stepSize (· < n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next - 1) / stepSize

instance (stepSize : Nat) (h) :
    IteratorSizePartial (Range.SuccIterator (α := Nat) stepSize (· < n) h) Id where
  size it := pure <| .up <| (n + stepSize - it.internalState.next - 1) / stepSize
