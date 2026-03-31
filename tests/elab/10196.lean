/-!
# Abstracting nested proofs hid 'sorry' warnings
https://github.com/leanprover/lean4/issues/10196
-/

/-!
Simplified version. The second `g'` did not use to have a warning.
It re-used the `g._proof_1` proof.
-/

def f (n : Nat) (_ : n ≠ 0) : Nat := n
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def g (m : Nat) := f m sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def g' (m : Nat) := f m sorry

/-!
Examples from the issue. The `ByteString.Pos.next` definition did not use to have a warning.
-/
structure ByteString where
structure ByteString.Pos (s : ByteString) where
structure ByteString.Slice where
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ByteString.toSlice (s : ByteString) : ByteString.Slice :=
  sorry
structure ByteString.Slice.Pos (s : ByteString.Slice) where
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ByteString.Slice.endPos (s : ByteString.Slice) : s.Pos :=
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ByteString.Slice.Pos.get {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : Char :=
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ByteString.Pos.toSlice {s : ByteString} (pos : s.Pos) : s.toSlice.Pos :=
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ByteString.Slice.Pos.next {s : ByteString.Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : s.Pos :=
  sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ByteString.Pos.get {s : ByteString} (pos : s.Pos) : Char :=
  pos.toSlice.get sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ByteString.Pos.next {s : ByteString} (pos : s.Pos) (h : True) : s.toSlice.Pos :=
  pos.toSlice.next sorry
