/-!
Tests that `GuessLex` considers measures that use the parameter's own `WellFoundedRelation`
instance (here: `String.Pos` and `String.Slice.Pos`, which increase in recursive calls), not just
`sizeOf`.
-/

set_option showInferredTerminationBy true

/--
info: Inferred termination measure:
termination_by p
-/
#guard_msgs in
def countA (s : String) (p : s.Pos) (acc : Nat) : Nat :=
  if h : p = s.endPos then acc
  else countA s (p.next h) (if p.get h = 'a' then acc + 1 else acc)

/--
info: Inferred termination measure:
termination_by p
-/
#guard_msgs in
def sliceCount (s : String.Slice) (p : s.Pos) : Nat :=
  if h : p = s.endPos then 0
  else sliceCount s (p.next h) + 1

/--
info: Inferred termination measure:
termination_by pos
-/
#guard_msgs in
def viaNext? (word : String) (pos : word.Pos) (count : Nat) : Nat :=
  match h : pos.next? with
  | some next => viaNext? word next (count + 1)
  | none => count

/--
info: Inferred termination measure:
termination_by (n, p)
-/
#guard_msgs in
def restart (s : String) (n : Nat) (p : s.Pos) : Nat :=
  if h : p = s.endPos then
    match n with
    | 0 => 0
    | n + 1 => restart s n s.startPos
  else restart s n (p.next h)

/--
info: Inferred termination measure:
termination_by (p, n)
-/
#guard_msgs in
def posThenNat (s : String) (p : s.Pos) (n : Nat) : Nat :=
  if h : p = s.endPos then 0
  else match n with
    | 0 => posThenNat s (p.next h) 10
    | n + 1 => posThenNat s p n

/-! Walking backwards goes against the `String.Pos` instance, so it still needs `p.down`. -/

/--
error: fail to show termination for
  back
with errors
failed to infer structural recursion:
Not considering parameter s of back:
  it is unchanged in the recursive calls
Cannot use parameter p:
  the type s.Pos does not have a `.brecOn` recursor


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           #1 p
1) 86:7-24  ? ?

#1: sizeOf p

Please use `termination_by` to specify a decreasing measure.
-/
#guard_msgs in
def back (s : String) (p : s.Pos) : Nat :=
  if h : p = s.startPos then 0
  else back s (p.prev h) + 1
