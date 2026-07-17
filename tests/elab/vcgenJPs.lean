import Lean
import Std.Internal
import Std.Tactic.Do

/-! Tests for `vcgen +jp`: shared-continuation (`__do_jp`) handling. A shared tail after an
`if`/`match` makes do-elaboration emit a `__do_jp`; `+jp` proves the tail once and discharges each
jump through a synthetic spec instead of inlining it. Ported from `mvcgenJPs.lean`. -/

open Lean Order Meta Elab Tactic Sym Std Internal.Do

set_option grind.warning false
set_option mvcgen.warning false

def ifs_pure (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := x + 1 else x := x + 2
  if n > 1 then x := x + 3 else x := x + 4
  if n > 2 then x := x + 1 else x := x + 2
  if n > 3 then x := x + 1 else x := x + 2
  if n > 4 then x := x + 1 else x := x + 2
  if n > 5 then x := x + 1 else x := x + 2
  return x

theorem ifs_pure_triple : ⦃ True ⦄ ifs_pure n ⦃ fun r => r > 0 ⦄ := by
  unfold ifs_pure
  vcgen +jp
  all_goals grind

def difs_pure (n : Nat) : Id Nat := do
  let mut x := 0
  if h : n > 0 then x := x + 1 else x := x + 2
  if h : n > 1 then x := x + 3 else x := x + 4
  if h : n > 2 then x := x + 1 else x := x + 2
  if h : n > 3 then x := x + 1 else x := x + 2
  if h : n > 4 then x := x + 1 else x := x + 2
  if h : n > 5 then x := x + 1 else x := x + 2
  return x

theorem difs_pure_triple : ⦃ True ⦄ difs_pure n ⦃ fun r => r > 0 ⦄ := by
  unfold difs_pure
  vcgen +jp
  all_goals grind

def matches_pure (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  match f 0 with | some y => x := x + y + 1 | none => x := x + 2
  match f 1 with | some y => x := x + y + 1 | none => x := x + 2
  match f 2 with | some y => x := x + y + 1 | none => x := x + 2
  match f 3 with | some y => x := x + y + 1 | none => x := x + 2
  match f 4 with | some y => x := x + y + 1 | none => x := x + 2
  match f 5 with | some y => x := x + y + 1 | none => x := x + 2
  return x

theorem matches_pure_triple : ⦃ True ⦄ matches_pure f ⦃ fun r => r > 0 ⦄ := by
  unfold matches_pure
  vcgen +jp
  all_goals grind

def dmatches_pure (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  match h : f 0 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 1 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 2 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 3 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 4 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 5 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  return x

theorem dmatches_pure_triple : ⦃ True ⦄ dmatches_pure f ⦃ fun r => r > 0 ⦄ := by
  unfold dmatches_pure
  vcgen +jp
  all_goals grind

def mixed_matches_pure (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  match h : f 0, f 10 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 1, f 11 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 2, f 12 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 3, f 13 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 4, f 14 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 5, f 15 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  return x

theorem mixed_matches_pure_triple : ⦃ True ⦄ mixed_matches_pure f ⦃ fun r => r > 0 ⦄ := by
  unfold mixed_matches_pure
  vcgen +jp
  all_goals grind

def if_state (f : Nat → Bool) : StateM Nat Nat := do
  let mut x := 0
  if f 0 then x := x + 1 else x := x + 2
  if f 1 then x := x + 1 else x := x + 2
  if f 2 then x := x + 1 else x := x + 2
  if f 3 then x := x + 1 else x := x + 2
  if f 4 then x := x + 1 else x := x + 2
  if f 5 then x := x + 1 else x := x + 2
  return x

theorem if_state_triple : ⦃ fun _ => True ⦄ if_state f ⦃ fun r => ⌜r > 0⌝ ⦄ := by
  unfold if_state
  vcgen +jp
  all_goals grind

def matches_state (f : Nat → Option Nat) : StateM Nat Nat := do
  let mut x := 0
  match f 0 with | some y => x := x + y + 1 | none => x := x + 2
  match f 1 with | some y => x := x + y + 1 | none => x := x + 2
  match f 2 with | some y => x := x + y + 1 | none => x := x + 2
  match f 3 with | some y => x := x + y + 1 | none => x := x + 2
  match f 4 with | some y => x := x + y + 1 | none => x := x + 2
  match f 5 with | some y => x := x + y + 1 | none => x := x + 2
  return x

theorem matches_state_triple : ⦃ fun _ => True ⦄ matches_state f ⦃ fun r => ⌜r > 0⌝ ⦄ := by
  unfold matches_state
  vcgen +jp
  all_goals grind

def set42 : StateM Nat Unit := set 42

@[spec]
theorem set42_triple : ⦃ fun _ => True ⦄ set42 ⦃ fun _ s => ⌜s > 13⌝ ⦄ := by
  vcgen [set42]
  grind

def mixed_matches_state (f : Nat → Option Nat) : StateM Nat Nat := do
  set 42
  let mut x := 0
  match h : f 0, f 10 with
  | some y, some z =>
    set y
    set42
    x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1
  | _, some _ =>
    x := x + 2
  | _, _ =>
    x := x + (← get)
  match h : f 1, f 11 with
  | some y, some z =>
    set y
    x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1
  | _, some _ =>
    set42
    x := x + 2
  | _, _ =>
    x := x + (← get)
  return x

theorem mixed_matches_state_triple : ⦃ fun _ => True ⦄ mixed_matches_state f ⦃ fun r => ⌜r > 0⌝ ⦄ := by
  unfold mixed_matches_state
  vcgen +jp
  all_goals grind

def early_return (f : Nat → Option Nat) : Id Nat := do
  let mut x := 1
  match f 0 with | some _ => return x | none => x := x + 1
  match f 1 with | some y => x := x + y + 1 | none => return x
  match f 2 with | some y => x := x + y + 1 | none => x := x + 1
  return x

theorem early_return_triple : ⦃ True ⦄ early_return f ⦃ fun r => r > 0 ⦄ := by
  unfold early_return
  vcgen +jp
  all_goals grind

-- Two mutable variables: the join carries several join-argument equalities.
def multi_mut (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  let mut y := 1
  match f 0 with | some z => x := x + z; y := y + x | none => y := y + 2
  match f 1 with | some z => x := x + z + y | none => x := x + y
  return x + y

theorem multi_mut_triple : ⦃ True ⦄ multi_mut f ⦃ fun r => r > 0 ⦄ := by
  unfold multi_mut
  vcgen +jp
  all_goals grind

-- The shared tail performs an effect, so the join-point body applies specs under the
-- match-valued precondition hypothesis.
def monadic_tail (f : Nat → Option Nat) : StateM Nat Nat := do
  let mut x := 1
  match f 0 with | some y => x := x + y | none => x := x + 2
  set x
  match f 1 with | some y => x := x + y | none => x := x + 2
  set x
  return x

theorem monadic_tail_triple : ⦃ fun _ => True ⦄ monadic_tail f ⦃ fun r => ⌜r > 0⌝ ⦄ := by
  unfold monadic_tail
  vcgen +jp
  all_goals grind

-- Literal and successor patterns produce a `Nat.casesOn`-shaped matcher.
def literal_patterns (n m : Nat) : Id Nat := do
  let mut x := 1
  match n with | 0 => x := x + 1 | k+1 => x := x + k + 2
  match m with | 0 => x := x + 1 | k+1 => x := x + k + 2
  return x

theorem literal_patterns_triple : ⦃ True ⦄ literal_patterns n m ⦃ fun r => r > 0 ⦄ := by
  unfold literal_patterns
  vcgen +jp
  all_goals grind

/- A split nested inside an alt (the inner join point's body is a jump to the outer one) and a
throwing alt (the jump behind `throw` is dead code, leaving its precondition unassigned) fail
under `vcgen +jp` and `mvcgen +jp` alike; these cases are exercised once join points support them.
def nested_split (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  match f 0 with
  | some y => if y > 0 then x := x + y else x := x + 1
  | none => x := x + 2
  match f 1 with
  | some y => if y > 0 then x := x + y else x := x + 1
  | none => x := x + 2
  return x

theorem nested_split_triple : ⦃ True ⦄ nested_split f ⦃ fun r => r > 0 ⦄ := by
  unfold nested_split
  vcgen +jp
  all_goals grind

def throwing (f : Nat → Option Nat) : ExceptT String (StateM Nat) Nat := do
  let mut x := 1
  match f 0 with | some y => x := x + y | none => throw "none"
  match f 1 with | some y => x := x + y | none => x := x + 2
  return x

theorem throwing_triple :
    ⦃ fun _ => True ⦄ throwing f ⦃ fun r => ⌜r > 0⌝; epost⟨fun _ _ => True⟩ ⦄ := by
  unfold throwing
  vcgen +jp
  all_goals grind
-/
