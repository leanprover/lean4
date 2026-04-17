import Lean
/-!
# Tests of level normalization (`Level.normalize`)
-/

open Lean Elab Command Term

def norm_level (u : Level) : TermElabM Unit := do
  let u' := u.normalize
  guard <| u'.normalize == u'
  guard <| u'.isNormalized
  logInfo m!"`{u}` => `{u'}`"

elab "#norm_level " l:level : command => runTermElabM fun _ => do
    let u ← elabLevel l
    norm_level u

universe u v w

/-- info: `0` => `0` -/
#guard_msgs in #norm_level 0
/-- info: `max (u + 1) (v + 2)` => `max (u + 1) (v + 2)` -/
#guard_msgs in #norm_level max (u + 1) (v + 2)
/-- info: `(max u (v + 1)) + 1` => `max (u + 1) (v + 2)` -/
#guard_msgs in #norm_level (max u (v + 1)) + 1
/-- info: `(max u v) + 2` => `max (u + 2) (v + 2)` -/
#guard_msgs in #norm_level max 0 (max u v + 2)
/-- info: `(max u v) + 2` => `max (u + 2) (v + 2)` -/
#guard_msgs in #norm_level max 1 (max u v + 2)
/-- info: `(max u v) + 2` => `max (u + 2) (v + 2)` -/
#guard_msgs in #norm_level max 2 (max u v + 2)
/-- info: `max 3 ((max u v) + 2)` => `max 3 (u + 2) (v + 2)` -/
#guard_msgs in #norm_level max 3 (max u v + 2)

/-! Used to be `max (max u v) w` -/
/-- info: `max u v w` => `max u v w` -/
#guard_msgs in #norm_level max u v w
/-- info: `max (max u v) w` => `max u v w` -/
#guard_msgs in #norm_level max (max u v) w

/-! Used to be `(max u v) + 1` -/
/-- info: `(imax (max u v) (max v u)) + 1` => `max (u + 1) (v + 1)` -/
#guard_msgs in #norm_level (imax (max u v) (max v u)) + 1

/-! Used to be `(max u (v + 1)) + 3` -/
/-- info: `(imax u (v + 1)) + 3` => `max (u + 3) (v + 4)` -/
#guard_msgs in #eval do
  let u := Level.addOffset (Level.imax (Level.param `u) (Level.succ (Level.param `v))) 3
  norm_level u

/-!
Tests of `Level.isNormalized`
-/
partial def levelGen (seed : Nat) : Level := go seed
where
  go (seed : Nat) : Level :=
    match seed with
    | 0 => .zero
    | 1 => .param `u
    | 2 => .param `v
    | 3 => .param `w
    | 4 => .mvar { name := Name.num `_levelGen 1 }
    | 5 => .mvar { name := Name.num `_levelGen 2 }
    | 6 => .mvar { name := Name.num `_levelGen 3 }
    | _ =>
      let kind := (seed - 6) % 7
      let seed := (seed - 6) / 7
      let rec split (n : Nat) : Nat × Nat :=
        if n == 0 then (0, 0)
        else
          let (a, b) := split (n / 4)
          (2*a + (n%4)/2, 2*b + n%2)
      match kind with
      | 0 | 1 | 2 =>
        let (seed1, seed2) := split (3*seed+kind)
        .max (go seed1) (go seed2)
      | 3 =>
        let (seed1, seed2) := split seed
        .imax (go seed1) (go seed2)
      | _ =>
        .succ (go (3*seed+kind-3))

def testNormalization (i : Nat) (log : Bool := false) : TermElabM Unit := do
  let u := levelGen i
  let u' := u.normalize
  if log then
    logInfo m!"{u} => {u'}"
  unless u.isNormalized ↔ (u == u') do
    throwError "{i}. isNormalized failure for {u} => {u'}"
  unless u'.isNormalized do
    throwError "{i}. normalized is not normalized for {u} => {u'}"
  unless u'.normalize == u' do
    throwError "{i}. normalize not idempotent for {u} => {u'}"

#eval show TermElabM Unit from do
  for i in 0...(100000 : Nat) do
    testNormalization i

#eval show TermElabM Unit from do
  for i in 0...(50000 : Nat) do
    testNormalization (7 * i + 20000)

#eval show TermElabM Unit from do
  for i in 0...(20000 : Nat) do
    testNormalization (13 * i + (i^2/2) + 20000)

#eval show TermElabM Unit from do
  for i in 0...(20000 : Nat) do
    testNormalization (37 * i + 20000000000)

#eval show TermElabM Unit from do
  for i in 0...(20000 : Nat) do
    testNormalization (19 * i + 123123123123123124)

/-!
Checking the quality of the level generator for these tests.
-/

/-- info: (max 0 w) + 2 => w + 2 -/
#guard_msgs in #eval testNormalization (log := true) <| 101
/-- info: (max w w) + 1 => w + 1 -/
#guard_msgs in #eval testNormalization (log := true) <| 102
/-- info: (max 0 _levelGen.1) + 1 => _levelGen.1 + 1 -/
#guard_msgs in #eval testNormalization (log := true) <| 103
/-- info: max (max 0 u) 0 => u -/
#guard_msgs in #eval testNormalization (log := true) <| 104
/--
info: (max (max (_levelGen.2 + 1) ((imax u u) + 1)) (max _levelGen.2 w) u (v + 1)) +
  2 => max (u + 3) (v + 3) (w + 2) (_levelGen.2 + 3)
-/
#guard_msgs in #eval testNormalization (log := true) <| 37 * 49999 + 20000000000
/--
info: imax (imax (max _levelGen.1 u) (max 0 v))
  ((max (imax u 0) _levelGen.3) + 1) => max (_levelGen.3 + 1) (imax (max u _levelGen.1) v)
-/
#guard_msgs in #eval testNormalization (log := true) <| 37 * 49998 + 20000000000
/--
info: max (max (max _levelGen.3 u) ((imax v u) + 1)) ((max v _levelGen.1) + 1)
  ((max _levelGen.2 v) + 1) => max u (v + 1) (_levelGen.1 + 1) (_levelGen.2 + 1) _levelGen.3 ((imax v u) + 1)
-/
#guard_msgs in #eval testNormalization (log := true) <| 37 * 49997 + 20000000000
/--
info: max (max ((max 0 _levelGen.1) + 1) (imax u _levelGen.3)) (max 0 (imax 0 0))
  (imax v (max 0 u)) => max (_levelGen.1 + 1) (imax u _levelGen.3) (imax v u)
-/
#guard_msgs in #eval testNormalization (log := true) <| 37 * 49000 + 20000000000
