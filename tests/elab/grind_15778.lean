module

/-!
Regression test for #15778: `grind?` dropped `List.mem_cons` from its `grind only [...]`
suggestion although the proof used it. The extensionality witnesses of `h`, `ha`, and `hb` are all
named `w✝`, so their case-split anchors collided and the generated script did not replay.
-/

/--
info: Try these:
  [apply] grind only [List.mem_cons, #b5b7, #42fd, #563a, #793c, #86fb, #1bd1, #577c, #7324]
  [apply] grind only [List.mem_cons]
  [apply] grind =>
    cases #b5b7 <;>
      cases #42fd <;>
        cases #563a <;>
          cases #793c <;>
            cases #86fb <;> instantiate only [List.mem_cons] <;> cases #1bd1 <;> cases #577c <;> cases #7324
-/
#guard_msgs in
example (p : Nat) (s : List Nat) (P : (Nat → Nat) → Prop)
    (ha : P (fun _ => 0))
    (hb : P (fun x => if x ∈ s then x else 0))
    (h : P (fun x => if x = p then x else if x ∈ s then x else 0)) :
    P (fun x => if x ∈ p :: s then x else 0) := by
  grind? only [List.mem_cons]

-- Pre-existing inaccessible parameters still make witness anchors collide, so script replay
-- fails (hence the dropped warning). This exercises the `instantiate approx [...]` fallback,
-- which must keep the premises found in the proof term.
/--
info: Try these:
  [apply] grind only [List.mem_cons, #fe77, #e4e6, #8b87, #f3de]
  [apply] grind only [List.mem_cons]
  [apply] grind =>
    cases #fe77 <;>
      cases #fe77 <;>
        cases #fe77 <;>
          cases #e4e6 <;>
            instantiate approx <;>
              cases #e4e6 <;>
                instantiate approx [List.mem_cons] <;>
                  cases #e4e6 <;> instantiate approx <;> cases #8b87 <;> cases #f3de
-/
#guard_msgs (info, drop warning) in
example (p q r : Nat) (s : List Nat) (P : (Nat → Nat) → Prop)
    (ha : P (fun x => if x = q then x else if x ∈ s then x else 0))
    (hb : P (fun x => if x = r then x else if x ∈ s then x else 0))
    (h : P (fun x => if x = p then x else if x ∈ s then x else 0)) :
    P (fun x => if x ∈ p :: s then x else 0) := by
  revert p q r s P ha hb h
  intro _ _ _ _ _ _ _ _
  grind? only [List.mem_cons]
