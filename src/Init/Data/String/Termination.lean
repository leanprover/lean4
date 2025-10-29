/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.String.Lemmas.Splits

/-!
# Helpers for termination arguments about functions operating on strings
-/

public section

namespace String

namespace Slice.Pos

/-- The number of bytes between `p` and the end position. This number decreases as `p` advances. -/
def remainingBytes {s : Slice} (p : s.Pos) : Nat :=
  p.offset.byteDistance s.endPos.offset

theorem remainingBytes_eq_byteDistance {s : Slice} {p : s.Pos} :
    p.remainingBytes = p.offset.byteDistance s.endPos.offset := (rfl)

theorem remainingBytes_eq {s : Slice} {p : s.Pos} :
    p.remainingBytes = s.utf8ByteSize - p.offset.byteIdx := by
  simp [remainingBytes_eq_byteDistance, Pos.Raw.byteDistance_eq]

theorem remainingBytes_inj {s : Slice} {p q : s.Pos} :
    p.remainingBytes = q.remainingBytes ↔ p = q := by
  have := p.isValidForSlice.le_utf8ByteSize
  have := q.isValidForSlice.le_utf8ByteSize
  simp only [remainingBytes_eq, Pos.ext_iff, Pos.Raw.ext_iff]
  omega

theorem le_iff_remainingBytes_le {s : Slice} (p q : s.Pos) :
    p ≤ q ↔ q.remainingBytes ≤ p.remainingBytes := by
  have := p.isValidForSlice.le_utf8ByteSize
  have := q.isValidForSlice.le_utf8ByteSize
  simp only [remainingBytes_eq, Slice.Pos.le_iff, Pos.Raw.le_iff]
  omega

theorem lt_iff_remainingBytes_lt {s : Slice} (p q : s.Pos) :
    p < q ↔ q.remainingBytes < p.remainingBytes := by
  have := p.isValidForSlice.le_utf8ByteSize
  have := q.isValidForSlice.le_utf8ByteSize
  simp only [remainingBytes_eq, Slice.Pos.lt_iff, Pos.Raw.lt_iff]
  omega

theorem wellFounded_lt {s : Slice} : WellFounded (fun (p : s.Pos) q => p < q) := by
  simpa [lt_iff, Pos.Raw.lt_iff] using
    InvImage.wf (Pos.Raw.byteIdx ∘ Slice.Pos.offset) Nat.lt_wfRel.wf

theorem wellFounded_gt {s : Slice} : WellFounded (fun (p : s.Pos) q => q < p) := by
  simpa [lt_iff_remainingBytes_lt] using
    InvImage.wf Slice.Pos.remainingBytes Nat.lt_wfRel.wf

instance {s : Slice} : WellFoundedRelation s.Pos where
  rel p q := q < p
  wf := Slice.Pos.wellFounded_gt

/-- Type alias for `String.Slice.Pos` representing that the given position is expected to decrease
in recursive calls. -/
structure Down (s : Slice) : Type where
  inner : s.Pos

/-- Use `termination_by pos.down` to signify that in a recursive call, the parameter `pos` is
expected to decrease. -/
def down {s : Slice} (p : s.Pos) : Pos.Down s where
  inner := p

@[simp]
theorem inner_down {s : Slice} {p : s.Pos} : p.down.inner = p := (rfl)

instance {s : Slice} : WellFoundedRelation (Pos.Down s) where
  rel p q := p.inner < q.inner
  wf := InvImage.wf Down.inner wellFounded_lt

theorem ne_endPos_of_next?_eq_some {s : Slice} {p q : s.Pos} :
    p.next? = some q → p ≠ s.endPos := by
  simpa [next?] using fun h _ => h

theorem eq_next_of_next?_eq_some {s : Slice} {p q : s.Pos} :
    (h : p.next? = some q) → q = p.next (ne_endPos_of_next?_eq_some h) := by
  simpa [next?] using fun _ h => h.symm

theorem ne_startPos_of_prev?_eq_some {s : Slice} {p q : s.Pos} :
    p.prev? = some q → p ≠ s.startPos := by
  simpa [prev?] using fun h _ => h

theorem eq_prev_of_prev?_eq_some {s : Slice} {p q : s.Pos} :
    (h : p.prev? = some q) → q = p.prev (ne_startPos_of_prev?_eq_some h) := by
  simpa [prev?] using fun _ h => h.symm

@[simp]
theorem le_refl {s : Slice} (p : s.Pos) : p ≤ p := by
  simp [le_iff]

theorem lt_trans {s : Slice} {p q r : s.Pos} : p < q → q < r → p < r := by
  simpa [Pos.lt_iff, Pos.Raw.lt_iff] using Nat.lt_trans

@[simp]
theorem lt_next_next {s : Slice} {p : s.Pos} {h h'} : p < (p.next h).next h' :=
  lt_trans p.lt_next (p.next h).lt_next

@[simp]
theorem prev_prev_lt {s : Slice} {p : s.Pos} {h h'} : (p.prev h).prev h' < p :=
  lt_trans (p.prev h).prev_lt p.prev_lt

end Slice.Pos

namespace ValidPos

/-- The number of bytes between `p` and the end position. This number decreases as `p` advances. -/
def remainingBytes {s : String} (p : s.ValidPos) : Nat :=
  p.toSlice.remainingBytes

@[simp]
theorem remainingBytes_toSlice {s : String} {p : s.ValidPos} :
    p.toSlice.remainingBytes = p.remainingBytes := (rfl)

theorem remainingBytes_eq_byteDistance {s : String} {p : s.ValidPos} :
    p.remainingBytes = p.offset.byteDistance s.endValidPos.offset := (rfl)

theorem remainingBytes_eq {s : String} {p : s.ValidPos} :
    p.remainingBytes = s.utf8ByteSize - p.offset.byteIdx := by
  simp [remainingBytes_eq_byteDistance, Pos.Raw.byteDistance_eq]

theorem remainingBytes_inj {s : String} {p q : s.ValidPos} :
    p.remainingBytes = q.remainingBytes ↔ p = q := by
  simp [← remainingBytes_toSlice, ValidPos.toSlice_inj, Slice.Pos.remainingBytes_inj]

theorem le_iff_remainingBytes_le {s : String} (p q : s.ValidPos) :
    p ≤ q ↔ q.remainingBytes ≤ p.remainingBytes := by
  simp [← remainingBytes_toSlice, ← Slice.Pos.le_iff_remainingBytes_le]

theorem lt_iff_remainingBytes_lt {s : String} (p q : s.ValidPos) :
    p < q ↔ q.remainingBytes < p.remainingBytes := by
  simp [← remainingBytes_toSlice, ← Slice.Pos.lt_iff_remainingBytes_lt]

theorem wellFounded_lt {s : String} : WellFounded (fun (p : s.ValidPos) q => p < q) := by
  simpa [lt_iff, Pos.Raw.lt_iff] using
    InvImage.wf (Pos.Raw.byteIdx ∘ ValidPos.offset) Nat.lt_wfRel.wf

theorem wellFounded_gt {s : String} : WellFounded (fun (p : s.ValidPos) q => q < p) := by
  simpa [lt_iff_remainingBytes_lt] using
    InvImage.wf ValidPos.remainingBytes Nat.lt_wfRel.wf

instance {s : String} : WellFoundedRelation s.ValidPos where
  rel p q := q < p
  wf := ValidPos.wellFounded_gt

/-- Type alias for `String.ValidPos` representing that the given position is expected to decrease
in recursive calls. -/
structure Down (s : String) : Type where
  inner : s.ValidPos

/-- Use `termination_by pos.down` to signify that in a recursive call, the parameter `pos` is
expected to decrease. -/
def down {s : String} (p : s.ValidPos) : ValidPos.Down s where
  inner := p

@[simp]
theorem inner_down {s : String} {p : s.ValidPos} : p.down.inner = p := (rfl)

instance {s : String} : WellFoundedRelation (ValidPos.Down s) where
  rel p q := p.inner < q.inner
  wf := InvImage.wf ValidPos.Down.inner ValidPos.wellFounded_lt

theorem map_toSlice_next? {s : String} {p : s.ValidPos} :
    p.next?.map ValidPos.toSlice = p.toSlice.next? := by
  simp [next?]

theorem map_toSlice_prev? {s : String} {p : s.ValidPos} :
    p.prev?.map ValidPos.toSlice = p.toSlice.prev? := by
  simp [prev?]

theorem ne_endValidPos_of_next?_eq_some {s : String} {p q : s.ValidPos}
    (h : p.next? = some q) : p ≠ s.endValidPos :=
  ne_of_apply_ne ValidPos.toSlice (Slice.Pos.ne_endPos_of_next?_eq_some
    (by simpa only [ValidPos.map_toSlice_next?, Option.map_some] using congrArg (·.map toSlice) h))

theorem eq_next_of_next?_eq_some {s : String} {p q : s.ValidPos} (h : p.next? = some q) :
    q = p.next (ne_endValidPos_of_next?_eq_some h) := by
  simpa only [← toSlice_inj, toSlice_next] using Slice.Pos.eq_next_of_next?_eq_some
    (by simpa [ValidPos.map_toSlice_next?] using congrArg (·.map toSlice) h)

theorem ne_startValidPos_of_prev?_eq_some {s : String} {p q : s.ValidPos}
    (h : p.prev? = some q) : p ≠ s.startValidPos :=
  ne_of_apply_ne ValidPos.toSlice (Slice.Pos.ne_startPos_of_prev?_eq_some
    (by simpa only [ValidPos.map_toSlice_prev?, Option.map_some] using congrArg (·.map toSlice) h))

theorem eq_prev_of_prev?_eq_some {s : String} {p q : s.ValidPos} (h : p.prev? = some q) :
    q = p.prev (ne_startValidPos_of_prev?_eq_some h) := by
  simpa only [← toSlice_inj, toSlice_prev] using Slice.Pos.eq_prev_of_prev?_eq_some
    (by simpa [ValidPos.map_toSlice_prev?] using congrArg (·.map toSlice) h)

@[simp]
theorem le_refl {s : String} (p : s.ValidPos) : p ≤ p := by
  simp [ValidPos.le_iff]

theorem lt_trans {s : String} {p q r : s.ValidPos} : p < q → q < r → p < r := by
  simpa [ValidPos.lt_iff, Pos.Raw.lt_iff] using Nat.lt_trans

@[simp]
theorem lt_next_next {s : String} {p : s.ValidPos} {h h'} : p < (p.next h).next h' :=
  lt_trans p.lt_next (p.next h).lt_next

@[simp]
theorem prev_prev_lt {s : String} {p : s.ValidPos} {h h'} : (p.prev h).prev h' < p :=
  lt_trans (p.prev h).prev_lt p.prev_lt

theorem Splits.remainingBytes_eq {s : String} {p : s.ValidPos} {t₁ t₂}
    (h : p.Splits t₁ t₂) : p.remainingBytes = t₂.utf8ByteSize := by
  simp [ValidPos.remainingBytes_eq, h.eq_append, h.offset_eq_rawEndPos]

end ValidPos

namespace Slice.Pos

@[simp]
theorem remainingBytes_toCopy {s : Slice} {p : s.Pos} :
    p.toCopy.remainingBytes = p.remainingBytes := by
  simp [remainingBytes_eq, ValidPos.remainingBytes_eq, Slice.utf8ByteSize_eq]

theorem Splits.remainingBytes_eq {s : Slice} {p : s.Pos} {t₁ t₂} (h : p.Splits t₁ t₂) :
    p.remainingBytes = t₂.utf8ByteSize := by
  simpa using h.toCopy.remainingBytes_eq

end Slice.Pos

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (with_reducible change (_ : Slice.Pos _) < _
   simp [
    Slice.Pos.eq_next_of_next?_eq_some (by assumption),
  ]) <;> done)
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (with_reducible change (_ : Slice.Pos _) < _
   simp [
    Slice.Pos.eq_prev_of_prev?_eq_some (by assumption),
  ]) <;> done)
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (with_reducible change (_ : String.ValidPos _) < _
   simp [
    ValidPos.eq_next_of_next?_eq_some (by assumption),
  ]) <;> done)
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (with_reducible change (_ : String.ValidPos _) < _
   simp [
    ValidPos.eq_prev_of_prev?_eq_some (by assumption),
  ]) <;> done)

end String
