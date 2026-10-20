module

/-!
Regression test for #15778: `grind?` suggested a `grind only [...]` that left out `List.mem_cons`
even though the proof used it. The goal follows from `h` by extensionality, while `ha` and `hb`
are irrelevant hypotheses about other functions. `grind` also split on the extensionality
witnesses of `ha` and `hb` and later pruned those splits, but the `cases #<anchor>` steps it
generated for the witness of `h` only made sense with those splits present, so the script did not
replay and the `instantiate` steps degraded to `instantiate approx` without any theorem.
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

example (p : Nat) (s : List Nat) (P : (Nat → Nat) → Prop)
    (ha : P (fun _ => 0))
    (hb : P (fun x => if x ∈ s then x else 0))
    (h : P (fun x => if x = p then x else if x ∈ s then x else 0)) :
    P (fun x => if x ∈ p :: s then x else 0) := by
  grind only [List.mem_cons]


-- Pre-existing inaccessible parameters can still make witness anchors collide. Ignore the
-- replay warning here and check that the fallback retains the premise in its suggestions.
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

example (p q r : Nat) (s : List Nat) (P : (Nat → Nat) → Prop)
    (ha : P (fun x => if x = q then x else if x ∈ s then x else 0))
    (hb : P (fun x => if x = r then x else if x ∈ s then x else 0))
    (h : P (fun x => if x = p then x else if x ∈ s then x else 0)) :
    P (fun x => if x ∈ p :: s then x else 0) := by
  revert p q r s P ha hb h
  intro _ _ _ _ _ _ _ _
  grind only [List.mem_cons]
