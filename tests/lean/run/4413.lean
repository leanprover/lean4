structure Note where
  pitch : UInt64
  start : Nat

def Note.containsNote (n1 n2 : Note) : Prop :=
  n1.start ≤ n2.start

def Note.lowerSemitone (n : Note) : Note :=
  { n with pitch := n.pitch - 1 }

theorem Note.self_containsNote_lowerSemitone_self (n : Note) :
    n.containsNote (Note.lowerSemitone n) := by
  simp [Note.containsNote, Note.lowerSemitone]

/--
error: type mismatch
  rfl
has type
  n = n : Prop
but is expected to have type
  n = n - 1 : Prop
-/
#guard_msgs in
set_option maxRecDepth 100 in
set_option maxHeartbeats 100 in
example (n : UInt64) : n = n - 1 :=
  rfl
