opaque g : Nat → Nat

set_option trace.Meta.debug true

@[grind] def f (a : Nat) :=
  match a with
  | 0 => 10
  | x+1 => g (f x)

set_option grind.debug true
set_option grind.debug.proofs true

set_option trace.grind.ematch.instance true
set_option trace.grind.assert true

/--
trace: [grind.assert] f (y + 1) = a
[grind.assert] ¬a = g (f y)
[grind.ematch.instance] f.eq_2: f y.succ = g (f y)
[grind.assert] f (y + 1) = g (f y)
-/
#guard_msgs (trace) in
example : f (y + 1) = a → a = g (f y):= by
  grind

@[grind] def app (xs ys : List α) :=
  match xs with
  | [] => ys
  | x::xs => x :: app xs ys

/--
trace: [grind.assert] app [1, 2] ys = xs
[grind.assert] ¬xs = 1 :: 2 :: ys
[grind.ematch.instance] app.eq_2: app [1, 2] ys = 1 :: app [2] ys
[grind.assert] app [1, 2] ys = 1 :: app [2] ys
[grind.ematch.instance] app.eq_2: app [2] ys = 2 :: app [] ys
[grind.assert] app [2] ys = 2 :: app [] ys
[grind.ematch.instance] app.eq_1: app [] ys = ys
[grind.assert] app [] ys = ys
-/
#guard_msgs (trace) in
example : app [1, 2] ys = xs → xs = 1::2::ys := by
  grind

opaque p : Nat → Nat → Prop
opaque q : Nat → Prop

@[grind =] theorem pq : p x x ↔ q x := by sorry

/--
trace: [grind.assert] p a a
[grind.assert] ¬q a
[grind.ematch.instance] pq: p a a ↔ q a
[grind.assert] p a a = q a
-/
#guard_msgs (trace) in
example : p a a → q a := by
  grind

opaque appV (xs : Vector α n) (ys : Vector α m) : Vector α (n + m) :=
  Vector.append xs ys

@[grind =]
theorem appV_assoc (a : Vector α n) (b : Vector α m) (c : Vector α n') :
        appV a (appV b c) ≍ appV (appV a b) c := sorry

/--
trace: [grind.assert] x1 = appV a_2 b
[grind.assert] x2 = appV x1 c
[grind.assert] x3 = appV b c
[grind.assert] x4 = appV a_2 x3
[grind.assert] ¬x2 ≍ x4
[grind.ematch.instance] appV_assoc: appV a_2 (appV b c) ≍ appV (appV a_2 b) c
[grind.assert] appV a_2 (appV b c) ≍ appV (appV a_2 b) c
-/
#guard_msgs (trace) in
example : x1 = appV a b → x2 = appV x1 c → x3 = appV b c → x4 = appV a x3 → x2 ≍ x4 := by
  grind


/--
info: appV_assoc': [@appV #6 #5 (@HAdd.hAdd `[Nat] `[Nat] `[Nat] `[instHAdd] #4 #3) #2 (@appV _ #4 #3 #1 #0)]
-/
#guard_msgs (info) in
@[grind? =]
theorem appV_assoc' (a : Vector α n) (b : Vector α m) (c : Vector α n') :
        appV a (appV b c) ≍ appV (appV a b) c := sorry
