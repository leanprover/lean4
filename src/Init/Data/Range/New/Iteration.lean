module

prelude
import Init.Data.Range.New.RangeIterator

open Std.Iterators

@[always_inline, inline]
def PRange.iterInternal [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    (r : PRange shape α) : Iter (α := Types.RangeIterator shape α) α :=
  ⟨⟨UpwardEnumerableRange.init r.lower, r.upper⟩⟩

@[always_inline, inline]
def PRange.size [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    (r : PRange shape α) [IteratorSize (Types.RangeIterator shape α) Id] : Nat :=
  r.iterInternal.size

@[always_inline, inline]
def PRange.toList [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    (r : PRange shape α)
    [Iterator (Types.RangeIterator shape α) Id α] [Finite (Types.RangeIterator shape α) Id]
    [IteratorCollect (Types.RangeIterator shape α) Id Id] : List α :=
  r.iterInternal.toList

-- instance [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
--     [ForIn' m (Iter (α := Types.RangeIterator shape α) α) α inferInstance] :
--     ForIn' m (PRange shape α) α where
--   forIn r := forIn r.iter

section Iterator

-- theorem Range.SuccIterator.succ?_eq_some_of_isPlausibleSuccessorOf [Succ? α] [LE α] [DecidableLE α]
--     {it' it : Iter (α := Types.RangeIterator α inferInstance P) α}
--     [Finite (Types.RangeIterator α inferInstance P) Id]
--     (h' : it'.IsPlausibleSuccessorOf it) :
--     Succ?.succ? 1 it.internalState.next = some it'.internalState.next :=
--   h' |>
--     TakeWhile.isPlausibleSuccessorOf_inner_of_isPlausibleSuccessorOf |>
--     RepeatIterator.Monadic.next_eq_some_of_isPlausibleSuccessorOf

private theorem RangeIterator.isPlausibleIndirectOutput_iff.aux
    [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    {r : PRange shape α} {it : Iter (α := Types.RangeIterator shape α) α} {a : α}
    (h : ∃ next, it.internalState.next = some next ∧ HasRange.SatisfiesLowerBound r.lower next)
    (h' : it.IsPlausibleIndirectOutput a)
    (hu : it.internalState.upperBound = r.upper) :
    a ∈ r := by
  induction h'
  case direct it out h' =>
    simp only [Types.RangeIterator.isPlausibleOutput_iff, hu] at h'
    obtain ⟨next, hn, hl⟩ := h
    simp only [h'.1, Option.some.injEq] at hn
    cases hn
    exact ⟨hl, h'.2⟩
  case indirect it it' out  hs ho ih =>
    rw [Types.RangeIterator.isPlausibleSuccessorOf_iff] at hs
    obtain ⟨next, hn, h₁, h₂, hs⟩ := hs
    apply ih
    · rw [← hs] at hu
      have ho' := Types.RangeIterator.isSome_next_of_isPlausibleIndirectOutput ho
      rw [Option.isSome_iff_exists] at ho'
      obtain ⟨a, ha⟩ := ho'
      rw [ha] at h₂
      refine ⟨a, ha, ?_⟩
      apply LawfulUpwardEnumerableRange.satisfiesLowerBound_of_le r.lower next a
      · obtain ⟨_, hn', hl⟩ := h
        simp only [hn] at hn'
        cases hn'
        exact hl
      · refine ⟨1, ?_⟩
        simp [LawfulUpwardEnumerable.succMany?_succ, LawfulUpwardEnumerable.succMany?_zero, h₂]
    · simp [*]

theorem RangeIterator.isPlausibleIndirectOutput_iff'
    [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    {it : Iter (α := Types.RangeIterator shape α) α} {out : α} :
    it.IsPlausibleIndirectOutput out ↔
      ∃ n, it.internalState.next.bind (UpwardEnumerable.succMany? n ·) = some out ∧
        HasRange.SatisfiesUpperBound it.internalState.upperBound out := by
  constructor
  · intro h
    induction h
    case direct h =>
      rw [Types.RangeIterator.isPlausibleOutput_iff] at h
      refine ⟨0, by simp [h, LawfulUpwardEnumerable.succMany?_zero]⟩
    case indirect h _ ih =>
      rw [Types.RangeIterator.isPlausibleSuccessorOf_iff] at h
      obtain ⟨n, hn⟩ := ih
      obtain ⟨a, ha, h₁, h₂, h₃⟩ := h
      refine ⟨n + 1, ?_⟩
      simp [ha, ← h₃, hn.2, LawfulUpwardEnumerable.succMany?_succ_eq_succ_bind_succMany, h₂, hn]
  · rintro ⟨n, hn, hu⟩
    induction n generalizing it
    case zero =>
      apply Iter.IsPlausibleIndirectOutput.direct
      rw [Types.RangeIterator.isPlausibleOutput_iff]
      exact ⟨by simpa [LawfulUpwardEnumerable.succMany?_zero] using hn, hu⟩
    case succ ih =>
      cases hn' : it.internalState.next
      · simp [hn'] at hn
      rename_i a
      simp [hn'] at hn
      have hle : UpwardEnumerable.le a out := ⟨_, hn⟩
      rw [LawfulUpwardEnumerable.succMany?_succ_eq_succ_bind_succMany] at hn
      cases hn' : UpwardEnumerable.succ? a
      · simp [hn'] at hn
      rename_i a'
      simp [hn'] at hn
      specialize ih (it := ⟨some a', it.internalState.upperBound⟩) hn hu
      refine Iter.IsPlausibleIndirectOutput.indirect ?_ ih
      rw [Types.RangeIterator.isPlausibleSuccessorOf_iff]
      refine ⟨a, ‹_›, ?_, hn', rfl⟩
      apply LawfulUpwardEnumerableRange.satisfiesUpperBound_of_le _ a out
      · exact hu
      · exact hle

private theorem RangeIterator.isPlausibleIndirectOutput_iff
    [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    {r : PRange shape α} {a : α} :
    r.iterInternal.IsPlausibleIndirectOutput a ↔ a ∈ r := by
  rw [isPlausibleIndirectOutput_iff']
  constructor
  · rintro ⟨n, hn, hu⟩
    refine ⟨?_, hu⟩
    rw [LawfulUpwardEnumerableRange.satisfiesLowerBound_iff]
    cases hr : r.iterInternal.internalState.next
    · simp [hr] at hn
    rw [hr, Option.bind_some] at hn
    exact ⟨_, hr, n, hn⟩
  · rintro ⟨hl, hu⟩
    rw [LawfulUpwardEnumerableRange.satisfiesLowerBound_iff] at hl
    obtain ⟨_, hr, n, hn⟩ := hl
    exact ⟨n, by simp [PRange.iterInternal, hr, hn], hu⟩

@[no_expose]
instance [UpwardEnumerable α] [HasRange shape α] [UpwardEnumerableRange shape α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableRange shape α]
    [Monad m] [Finite (Types.RangeIterator shape α) Id] :
    ForIn' m (PRange shape α) α inferInstance where
  forIn' r init f := by
    haveI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
    refine ForIn'.forIn' (α := α) r.iterInternal init (fun a ha acc => f a ?_ acc)
    simp only [Membership.mem] at ha
    rwa [RangeIterator.isPlausibleIndirectOutput_iff] at ha

end Iterator

theorem Range.mem.upper [LE α] [DecidableLE α] {i : α} {r : PRange ⟨.unbounded, .closed⟩ α} (h : i ∈ r) : i ≤ r.upper :=
  h.2

-- theorem Range.mem.lower [LE α] {i : α} {r : PRange ⟨.unbounded, .closed⟩ α} (h : i ∈ r) : r.lower ≤ i := h.1

-- theorem Range.mem.step {i : Nat} {r : PRange shape α} (h : i ∈ r) : (i - r.start) % r.step = 0 := h.2.2

theorem Range.get_elem_helper {i n : Nat} {r : PRange ⟨.closed, .open⟩ Nat} (h₁ : i ∈ r) (h₂ : r.upper = n) :
    i < n := h₂ ▸ h₁.2

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| apply Range.get_elem_helper; assumption; rfl)
