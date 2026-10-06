import rc_model

/-!
Shared reference counting with separately scheduled guards and atomic updates. Retains may borrow
through the same owning field; its source token stays live until pending retains finish. The sticky
bounds require at most 4094 pending increments of at most `LEAN_RC_INC_MAX` and fewer pending
releases than the width of the sticky band. These bounds are assumptions, not runtime limits.
-/

namespace RcConcurrent

abbrev limit : Nat := 4094
abbrev dropLimit : Nat := 0x0fffffff
abbrev chunk : Nat := 0x10000
abbrev sticky : Int := -0x70000000
abbrev dropSticky : Int := -0x60000000
abbrev floor : Int := sticky - limit * chunk
abbrev ceiling : Int := sticky + dropLimit

structure State where
  count : Int
  owners : Nat
  copies : List Nat := []
  drops : Nat := 0
  skipped : Nat := 0
  frozen : Bool := false
  deriving DecidableEq

def State.references (s : State) : Nat :=
  s.owners + s.drops + s.skipped

/--
Pending increments reserve room below the counter. Once an increment is skipped, pending drops
reserve room above it. Without skipped increments the counter conservatively covers every token.
-/
structure Safe (s : State) : Prop where
  copiesBound : s.copies.length ≤ limit
  chunksBound : ∀ n ∈ s.copies, n ≤ chunk
  dropsBound : s.drops + s.skipped ≤ dropLimit
  lowerCredit : floor ≤ s.count - (s.copies.sum : Int)
  accounting : s.frozen = false → s.count + (s.references : Int) ≤ 0
  upperCredit : s.frozen = true → s.count + (s.drops : Int) ≤ ceiling
  sourceLive : s.copies ≠ [] → 0 < s.owners

/-- Guards and updates are different steps; updates can finish in any order. -/
inductive Step : State → State → Prop where
  | copyStart (s : State) (n : Nat) (owned : 0 < s.owners)
      (enabled : sticky < s.count) (small : n ≤ chunk) (room : s.copies.length < limit) :
      Step s { s with copies := n :: s.copies }
  | copySkip (s : State) (n : Nat) (owned : 0 < s.owners) (disabled : s.count ≤ sticky) :
      Step s { s with owners := s.owners + n, frozen := true }
  | copyFinish (s : State) (before after : List Nat) (n : Nat)
      (pending : s.copies = before ++ n :: after) :
      Step s { s with
        count := s.count - n
        owners := s.owners + n
        copies := before ++ after }
  | dropStart (s : State) (owned : 0 < s.owners) (enabled : dropSticky < s.count)
      (sourceLive : s.copies = [] ∨ 1 < s.owners)
      (room : s.drops + s.skipped < dropLimit) :
      Step s { s with owners := s.owners - 1, drops := s.drops + 1 }
  | dropSkip (s : State) (owned : 0 < s.owners) (disabled : s.count ≤ dropSticky)
      (sourceLive : s.copies = [] ∨ 1 < s.owners)
      (room : s.drops + s.skipped < dropLimit) :
      Step s { s with owners := s.owners - 1, skipped := s.skipped + 1 }
  | dropFinish (s : State) (pending : 0 < s.drops) :
      Step s { s with count := s.count + 1, drops := s.drops - 1 }
  | skipFinish (s : State) (pending : 0 < s.skipped) :
      Step s { s with skipped := s.skipped - 1 }

private theorem sum_bound (xs : List Nat) (h : ∀ n ∈ xs, n ≤ chunk) :
    xs.sum ≤ xs.length * chunk := by
  induction xs with
  | nil => simp
  | cons n xs ih =>
    have hn := h n (by simp)
    have ht := ih (by intro m hm; exact h m (by simp [hm]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    simp only [chunk] at *
    omega

theorem Step.preserves {s t : State} (h : Step s t) (hs : Safe s) : Safe t := by
  rcases hs with ⟨hc, hn, hd, hl, ha, hu, hp⟩
  cases h with
  | copyStart n owned enabled small room =>
    have hb := sum_bound (n :: s.copies) (by
      intro m hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact small
      · exact hn m hm)
    refine ⟨by simp only [List.length_cons]; omega, ?_, hd, ?_, ha, hu,
      by intro _; exact owned⟩
    · intro m hm; simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact small
      · exact hn m hm
    · simp only [List.sum_cons, List.length_cons] at hb ⊢
      simp only [floor, sticky, limit, chunk] at *
      omega
  | copySkip n owned disabled =>
    refine ⟨hc, hn, hd, hl, by simp, ?_, by intro _; dsimp only; omega⟩
    intro _
    simp only [ceiling, sticky, dropLimit] at *
    omega
  | copyFinish before after n pending =>
    have hb : ∀ m ∈ before ++ after, m ≤ chunk := by
      intro m hm
      apply hn m
      simp only [pending, List.mem_append, List.mem_cons] at *
      grind
    simp only [pending, List.length_append, List.length_cons, List.sum_append,
      List.sum_cons, Int.natCast_add] at hc hl
    refine ⟨?_, hb, hd, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp only [List.sum_append, Int.natCast_add]; omega
    · intro hf
      have := ha hf
      simp only [State.references] at *
      omega
    · intro hf; have := hu hf; dsimp only; omega
    · intro remaining
      have nonempty : s.copies ≠ [] := by
        intro empty
        have : n ∈ s.copies := by simp [pending]
        simp [empty] at this
      have := hp nonempty
      dsimp only
      omega
  | dropStart owned enabled sourceLive room =>
    have hf : s.frozen = false := by
      cases h : s.frozen with
      | false => rfl
      | true =>
        have := hu h
        simp only [ceiling, sticky, dropSticky, dropLimit] at *
        omega
    refine ⟨hc, hn, by dsimp only; omega, hl, ?_, ?_, ?_⟩
    · intro _
      have := ha hf
      simp only [State.references] at *
      omega
    · simp [hf]
    · intro nonempty
      dsimp only at nonempty ⊢
      rcases sourceLive with empty | owned
      · exact (nonempty empty).elim
      · omega
  | dropSkip owned disabled sourceLive room =>
    refine ⟨hc, hn, by dsimp only; omega, hl, ?_, hu, ?_⟩
    · intro hf
      have := ha hf
      simp only [State.references] at *
      omega
    · intro nonempty
      dsimp only at nonempty ⊢
      rcases sourceLive with empty | owned
      · exact (nonempty empty).elim
      · omega
  | dropFinish pending =>
    refine ⟨hc, hn, by dsimp only; omega, by dsimp only; omega, ?_, ?_, hp⟩
    · intro hf
      have := ha hf
      simp only [State.references] at *
      omega
    · intro hf; have := hu hf; dsimp only; omega
  | skipFinish pending =>
    refine ⟨hc, hn, by dsimp only; omega, hl, ?_, hu, hp⟩
    intro hf
    have := ha hf
    simp only [State.references] at *
    omega

inductive History : State → State → Prop where
  | nil (s : State) : History s s
  | next {s t u : State} : History s t → Step t u → History s u

theorem history_preserves {s t : State} (h : History s t)
    (hs : Safe s) : Safe t := by
  induction h with
  | nil => exact hs
  | next _ step ih => exact step.preserves ih

/-- Sharing uses the native encoding, including an already overflowed single-threaded count. -/
def initial (rc : Int32) (owners : Nat) : State :=
  { count := (markMtRc rc).toInt, owners, frozen := markMtRc rc == LEAN_RC_STICKY }

theorem initial_safe (rc : Int32) (owners : Nat) (unshared : isUnshared rc)
    (tracked : tracks (some rc) (some owners)) : Safe (initial rc owners) := by
  by_cases frozen : markMtRc rc = LEAN_RC_STICKY
  · constructor <;>
      simp [initial, frozen, State.references, floor, ceiling, sticky, limit, dropLimit, chunk]
  · have sharing := markMtRc_spec rc
    have live : rc > 0 ∧ markMtRc rc = -rc ∧ LEAN_RC_STICKY_DROP < -rc := by
      simp only [isSt, isStuckSt, LEAN_RC_STUCK_ST_eq] at sharing
      simp only [isUnshared, LEAN_RC_STUCK_ST_eq] at unshared
      simp only [markMtRc, isUnshared, LEAN_RC_STUCK_ST_eq] at frozen ⊢
      split at frozen <;> (try split at frozen) <;> bv_decide
    have positive : 0 < rc.toInt := by
      simpa only [Int32.lt_iff_toInt_lt, Int32.toInt_zero] using live.1
    have counted : rc.toInt = (owners : Int) := by
      have permanent : isNeverFreed rc = false := by bv_decide
      simp only [tracks, permanent, Bool.false_or, beq_iff_eq] at tracked
      simp only [refCountNat, refCount, isSt, live.1, decide_true, ↓reduceIte,
        Int64.toNatClampNeg, Int32.toInt_toInt64] at tracked
      omega
    have neg : (-rc).toInt = -rc.toInt := by
      rw [Int32.toInt_neg]
      apply Int.bmod_eq_of_le <;> have := rc.toInt_lt <;> omega
    have lower : dropSticky < (markMtRc rc).toInt := by
      have := live.2.2
      have drop : LEAN_RC_STICKY_DROP.toInt = dropSticky := by decide
      simpa only [Int32.lt_iff_toInt_lt, live.2.1, drop] using this
    rw [live.2.1, neg, counted] at lower
    have encoded : (markMtRc rc).toInt = -(owners : Int) := by
      rw [live.2.1, neg, counted]
    have stickyFalse : (markMtRc rc == LEAN_RC_STICKY) = false := by
      exact beq_eq_false_iff_ne.mpr frozen
    constructor <;>
      simp [initial, encoded, stickyFalse, State.references, floor, sticky, limit, chunk] <;>
      simp only [dropSticky] at lower ⊢ <;> omega

theorem Safe.live_shared {s : State} (h : Safe s) (owned : 0 < s.references) :
    LEAN_RC_STUCK_ST.toInt < s.count ∧ s.count < 0 := by
  have hl := h.lowerCredit
  have hn : (0 : Int) ≤ s.copies.sum := Int.natCast_nonneg _
  have hst : LEAN_RC_STUCK_ST.toInt = -0x7fff0000 := by
    rw [LEAN_RC_STUCK_ST_eq]; decide
  rw [hst]
  simp only [floor, sticky, limit, chunk] at hl
  cases hf : s.frozen
  · have := h.accounting hf
    omega
  · have := h.upperCredit hf
    simp only [ceiling, sticky, dropLimit] at this
    omega

/-- The atomic old count can be `-1` only while the releasing caller owns the sole token. -/
theorem Safe.last_exclusive {s : State} (h : Safe s) (pending : 0 < s.drops)
    (last : s.count = -1) : s.references = 1 := by
  cases hf : s.frozen
  · have := h.accounting hf
    simp only [State.references] at *
    omega
  · have := h.upperCredit hf
    have := h.dropsBound
    simp only [ceiling, sticky, dropLimit] at *
    omega

theorem Safe.last_quiescent {s : State} (h : Safe s) (pending : 0 < s.drops)
    (last : s.count = -1) : s.references = 1 ∧ s.copies = [] ∧ s.owners = 0 := by
  have exclusive := h.last_exclusive pending last
  have owners : s.owners = 0 := by
    simp only [State.references] at exclusive
    omega
  refine ⟨exclusive, ?_, owners⟩
  by_cases copies : s.copies = []
  · exact copies
  · have := h.sourceLive copies
    omega

theorem Safe.counter_encoding {s : State} (h : Safe s) (owned : 0 < s.references) :
    (Int32.ofInt s.count).toInt = s.count := by
  obtain ⟨hl, hu⟩ := h.live_shared owned
  have hst : LEAN_RC_STUCK_ST.toInt = -0x7fff0000 := by
    rw [LEAN_RC_STUCK_ST_eq]; decide
  rw [hst] at hl
  apply Int32.toInt_ofInt_of_le <;> omega

theorem constants_match :
    sticky = LEAN_RC_STICKY.toInt ∧ dropSticky = LEAN_RC_STICKY_DROP.toInt ∧
      chunk = LEAN_RC_INC_MAX.toNat := by
  refine ⟨by decide, by decide, ?_⟩
  cases System.Platform.numBits_eq <;>
    simp [chunk, LEAN_RC_INC_MAX, USize.toNat_ofNat, *]

/-- The native increment guard agrees with the modeled guard predicate. -/
theorem Safe.copy_guard {s : State} (h : Safe s) (owned : 0 < s.references) :
    decide ((Int32.ofInt s.count).toUInt32 > LEAN_RC_STICKY.toUInt32) =
      decide (sticky < s.count) := by
  have he := h.counter_encoding owned
  have hn := (h.live_shared owned).2
  rw [isUnstuckMt_unsigned]
  simp [isUnstuckMt, isMt, isStuck, Int32.lt_iff_toInt_lt,
    Int32.le_iff_toInt_le, he, ← constants_match.1, hn, ← Int.not_lt]

theorem Safe.drop_guard {s : State} (h : Safe s) (owned : 0 < s.references) :
    decide ((Int32.ofInt s.count).toUInt32 ≤ LEAN_RC_STICKY_DROP.toUInt32) =
      decide (s.count ≤ dropSticky) := by
  have he := h.counter_encoding owned
  have hn := (h.live_shared owned).2
  rw [isNeverFreed_unsigned _ (by
    simp [isSt, Int32.lt_iff_toInt_lt, he]; omega)]
  simp [isNeverFreed, isPersistent, isDropStopped, Int32.le_iff_toInt_le,
    ← Int32.toInt_inj, he, ← constants_match.2.1, Int.ne_of_lt hn]

theorem copy_update_encoding {s : State} (h : Safe s) (before after : List Nat) (n : Nat)
    (pending : s.copies = before ++ n :: after) :
    (Int32.ofInt s.count - Int32.ofNat n).toInt = s.count - n := by
  have ht := (Step.copyFinish s before after n pending).preserves h
  have nonempty : s.copies ≠ [] := by
    intro empty
    have : n ∈ s.copies := by simp [pending]
    simp [empty] at this
  have owned := h.sourceLive nonempty
  have he := ht.counter_encoding (by
    simp only [State.references]; omega)
  dsimp only at he
  rw [← Int32.ofInt_eq_ofNat, ← Int32.ofInt_sub]
  exact he

/-- Even the last update, which leaves zero tokens, cannot wrap the machine counter. -/
theorem drop_update_encoding {s : State} (h : Safe s) (pending : 0 < s.drops) :
    (Int32.ofInt s.count + 1).toInt = s.count + 1 := by
  obtain ⟨hl, hu⟩ := h.live_shared (by simp only [State.references]; omega)
  have hst : LEAN_RC_STUCK_ST.toInt = -0x7fff0000 := by
    rw [LEAN_RC_STUCK_ST_eq]; decide
  rw [hst] at hl
  change (Int32.ofInt s.count + Int32.ofInt 1).toInt = _
  rw [← Int32.ofInt_add]
  apply Int32.toInt_ofInt_of_le <;> omega

example : initial LEAN_RC_STUCK_ST 1 = { count := sticky, owners := 1, frozen := true } := by
  rw [LEAN_RC_STUCK_ST_eq]
  have parked : markMtRc (Int32.minValue + 65536) = LEAN_RC_STICKY := by
    cases System.Platform.numBits_eq <;> bv_decide
  simp only [initial, parked, beq_self_eq_true]
  decide

example : History { count := -1, owners := 1 }
    { count := -1, owners := 1, copies := [1, 1] } := by
  exact History.next
    (History.next (History.nil _) (Step.copyStart _ 1 (by decide) (by decide)
      (by decide) (by decide)))
    (Step.copyStart _ 1 (by decide) (by decide) (by decide) (by decide))

end RcConcurrent
