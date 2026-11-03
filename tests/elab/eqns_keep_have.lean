/-!
Tests that equation lemmas zeta-reduce the `have`s at the root of the right-hand side only when
this exposes a `match` to split, so that `vcgen +jp [f]` sees the join points of `f` (#16122).
-/

def f (x : Nat) : Nat :=
  have y := x + 1
  y + y

/--
info: f.eq_1 (x : Nat) :
  f x =
    have y := x + 1;
    y + y
-/
#guard_msgs in #check f.eq_1

-- A join point of `do` notation.
def prog2 (b : Nat → Bool) : StateM Nat Unit := do
  if b 0 then modify (· + 1) else modify (· + 2)
  if b 1 then modify (· + 1) else modify (· + 2)

/--
info: prog2.eq_1 (b : Nat → Bool) :
  prog2 b =
    have __do_jp := fun __r => if b 1 = true then modify fun x => x + 1 else modify fun x => x + 2;
    if b 0 = true then do
      let __r ← modify fun x => x + 1
      __do_jp __r
    else do
      let __r ← modify fun x => x + 2
      __do_jp __r
-/
#guard_msgs in #check prog2.eq_1

-- The `have` is zeta-reduced to split the `match`.
def h (x : Option Nat) : Nat :=
  have y := 1
  match x with
  | some a => a + y
  | none => y

/-- info: h.eq_1 (a : Nat) : h (some a) = a + 1 -/
#guard_msgs in #check h.eq_1

-- A `have` in a `match` alternative.
def k (x : Option Nat) : Nat :=
  match x with
  | some a => have y := a + 1; y * y
  | none => 0

/--
info: k.eq_1 (a : Nat) :
  k (some a) =
    have y := a + 1;
    y * y
-/
#guard_msgs in #check k.eq_1

-- Structural recursion.
def r : Nat → Nat
  | 0 => 0
  | n + 1 => have y := r n; y + y

/--
info: r.eq_2 (n : Nat) :
  r n.succ =
    have y := r n;
    y + y
-/
#guard_msgs in #check r.eq_2

-- Well-founded recursion.
def w (n : Nat) : Nat := if n = 0 then 0 else have y := w (n - 1); y + y
termination_by n

/--
info: w.eq_1 (n : Nat) :
  w n =
    if n = 0 then 0
    else
      have y := w (n - 1);
      y + y
-/
#guard_msgs in #check w.eq_1
