def f (x : Option Nat) (h : x ≠ none) : Nat :=
  match x with
  | none => by contradiction
  | some a => a

-- The following should work out-of-the-box with `Option.pbind_some'
example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  grind [f]

/-- info: Try this: grind only [= gen Option.pbind_some', f, cases Or] -/
#guard_msgs (info) in
example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  grind? [f]

reset_grind_attrs%

@[grind gen] theorem pbind_some' {α β} {x : Option α} {a : α} {f : (a : α) → x = some a → Option β}
     (h : x = some a) : Option.pbind x f = f a h := by
  subst h; rfl

example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  grind only [gen pbind_some', f]

-- Note that the following instance does not have hypotheses.
/-- trace: [grind.ematch.instance] pbind_some': (b.pbind fun a h => some (2 * a)) = some (2 * a) -/
#guard_msgs (trace) in
example (a : Nat) (h : b = some a) : (b.pbind fun a h => some <| 2*a) = some (a + a) := by
  set_option trace.grind.ematch.instance true in
  grind only [gen pbind_some']

/--
trace: [grind.ematch.instance] pbind_some': (b.pbind fun a h => some (a + f b ⋯)) = some (a + f b ⋯)
[grind.ematch.instance] f.eq_2: f (some a) ⋯ = a
-/
#guard_msgs (trace) in
example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  set_option trace.grind.ematch.instance true in
  grind [f]

-- Many different instances are generated if the `gen` modifier is not used
/--
trace: [grind.ematch.instance] pbind_some': ∀ (h : b = some a), (b.pbind fun a h => some (a + f b ⋯)) = some (a + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h : b = some (2 * a)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (2 * a + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_2 : b = some (a + f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + f b ⋯ + f b ⋯)
[grind.ematch.instance] f.eq_2: f (some a) ⋯ = a
[grind.ematch.instance] pbind_some': ∀ (h_2 : b = some (a + 2 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 2 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_2 : b = some (a + 3 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 3 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_2 : b = some (a + 4 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 4 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_3 : b = some (a + 5 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 5 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_3 : b = some (2 * a + f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (2 * a + f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_3 : b = some (a + 6 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 6 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_3 : b = some (a + 7 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 7 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_3 : b = some (a + 5 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 5 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_3 : b = some (a + 6 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 6 * f b ⋯ + f b ⋯)
[grind.ematch.instance] pbind_some': ∀ (h_3 : b = some (a + 7 * f b ⋯)),
      (b.pbind fun a h => some (a + f b ⋯)) = some (a + 7 * f b ⋯ + f b ⋯)
-/
#guard_msgs (trace) in
example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  set_option trace.grind.ematch.instance true in
  grind only [pbind_some', f]


-- `Option.pbind_some` produces an instance with a `cast` that makes the result hard to use
/--
trace: [grind.ematch.instance] Option.pbind_some: (some a).pbind (cast ⋯ fun a h => some (a + f b ⋯)) =
      cast ⋯ (fun a h => some (a + f b ⋯)) a ⋯
[grind.ematch.instance] Option.pbind_some: (some (2 * a)).pbind (cast ⋯ fun a h => some (a + f b ⋯)) =
      cast ⋯ (fun a h => some (a + f b ⋯)) (2 * a) ⋯
-/
#guard_msgs (trace) in
example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  set_option trace.grind.ematch.instance true in
  fail_if_success grind only [Option.pbind_some, f]
  sorry

/-- trace: [grind.ematch.instance] pbind_some': (b.pbind fun a h => some (2 * a)) = some (2 * a) -/
#guard_msgs (trace) in
example (a : Nat) (h : b = some a) : (b.pbind fun a h => some <| 2*a) = some (a + a) := by
  set_option trace.grind.ematch.instance true in
  grind only [= gen pbind_some']

example (a : Nat) (h : b = some a) : (b.pbind fun a h => some <| 2*a) = some (a + a) := by
  fail_if_success grind only [= pbind_some']
  sorry

reset_grind_attrs%

@[grind = gen] theorem pbind_some'' {α β} {x : Option α} {a : α} {f : (a : α) → x = some a → Option β}
     (h : x = some a) : Option.pbind x f = f a h := by
  subst h; rfl

/--
trace: [grind.ematch.instance] pbind_some'': (b.pbind fun a h => some (a + f b ⋯)) = some (a + f b ⋯)
[grind.ematch.instance] f.eq_2: f (some a) ⋯ = a
-/
#guard_msgs (trace) in
example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  set_option trace.grind.ematch.instance true in
  grind [f]

reset_grind_attrs%

@[grind =_ gen] theorem pbind_some''' {α β} {x : Option α} {a : α} {f : (a : α) → x = some a → Option β}
     (h : x = some a) : f a h = Option.pbind x f := by
  subst h; rfl

/--
trace: [grind.ematch.instance] pbind_some''': some (a + f b ⋯) = b.pbind fun a h => some (a + f b ⋯)
[grind.ematch.instance] f.eq_2: f (some a) ⋯ = a
-/
#guard_msgs (trace) in
example (h : b = some a) : (b.pbind fun a h => some <| a + f b (by grind)) = some (a + a) := by
  set_option trace.grind.ematch.instance true in
  grind [f]
