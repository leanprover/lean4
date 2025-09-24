import Std.Tactic.Do

open Std.Do

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

theorem ifs_pure_triple : ⦃⌜True⌝⦄ ifs_pure n ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold ifs_pure
  mvcgen -elimLets +jp
  grind

def difs_pure (n : Nat) : Id Nat := do
  let mut x := 0
  if h : n > 0 then x := x + 1 else x := x + 2
  if h : n > 1 then x := x + 3 else x := x + 4
  if h : n > 2 then x := x + 1 else x := x + 2
  if h : n > 3 then x := x + 1 else x := x + 2
  if h : n > 4 then x := x + 1 else x := x + 2
  if h : n > 5 then x := x + 1 else x := x + 2
  return x

theorem difs_pure_triple : ⦃⌜True⌝⦄ difs_pure n ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold difs_pure
  mvcgen -elimLets +jp
  grind

def matches_pure (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  match f 0 with | some y => x := x + y + 1 | none => x := x + 2
  match f 1 with | some y => x := x + y + 1 | none => x := x + 2
  match f 2 with | some y => x := x + y + 1 | none => x := x + 2
  match f 3 with | some y => x := x + y + 1 | none => x := x + 2
  match f 4 with | some y => x := x + y + 1 | none => x := x + 2
  match f 5 with | some y => x := x + y + 1 | none => x := x + 2
  return x

theorem matches_pure_triple : ⦃⌜True⌝⦄ matches_pure f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold matches_pure
  mvcgen -elimLets +jp
  grind

def dmatches_pure (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  match h : f 0 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 1 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 2 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 3 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 4 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  match h : f 5 with | some y => x := x + (cast (congrArg (fun _ => Nat) h) y) + 1 | none => x := x + 2
  return x

theorem dmatches_pure_triple : ⦃⌜True⌝⦄ dmatches_pure f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold dmatches_pure
  mvcgen -elimLets +jp
  grind

def mixed_matches_pure (f : Nat → Option Nat) : Id Nat := do
  let mut x := 0
  match h : f 0, f 10 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 1, f 11 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 2, f 12 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 3, f 13 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 4, f 14 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  match h : f 5, f 15 with | some y, some z => x := x + (cast (congrArg (fun _ => Nat) h) y) + z + 1 | _, some _ => x := x + 2 | _, _ => x := x + 1
  return x

theorem mixed_matches_pure_triple : ⦃⌜True⌝⦄ mixed_matches_pure f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold mixed_matches_pure
  mvcgen -elimLets +jp
  grind

def if_state (f : Nat → Bool) : StateM Nat Nat := do
  let mut x := 0
  if f 0 then x := x + 1 else x := x + 2
  if f 1 then x := x + 1 else x := x + 2
  if f 2 then x := x + 1 else x := x + 2
  if f 3 then x := x + 1 else x := x + 2
  if f 4 then x := x + 1 else x := x + 2
  if f 5 then x := x + 1 else x := x + 2
  return x

theorem if_state_triple : ⦃⌜True⌝⦄ if_state f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold if_state
  mvcgen +jp
  grind

def matches_state (f : Nat → Option Nat) : StateM Nat Nat := do
  let mut x := 0
  match f 0 with | some y => x := x + y + 1 | none => x := x + 2
  match f 1 with | some y => x := x + y + 1 | none => x := x + 2
  match f 2 with | some y => x := x + y + 1 | none => x := x + 2
  match f 3 with | some y => x := x + y + 1 | none => x := x + 2
  match f 4 with | some y => x := x + y + 1 | none => x := x + 2
  match f 5 with | some y => x := x + y + 1 | none => x := x + 2
  return x

theorem matches_state_triple : ⦃⌜True⌝⦄ matches_state f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold matches_state
  mvcgen +jp
  grind

def set42 : StateM Nat Unit := set 42

@[spec]
theorem set42_triple : ⦃⌜True⌝⦄ set42 ⦃⇓ _ s => ⌜s > 13⌝⦄ := by
  mvcgen [set42]

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

theorem mixed_matches_state_triple : ⦃⌜True⌝⦄ mixed_matches_state f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold mixed_matches_state
  mvcgen +jp
  grind

def early_return (f : Nat → Option Nat) : Id Nat := do
  let mut x := 1
  match f 0 with | some _ => return x | none => x := x + 1
  match f 1 with | some y => x := x + y + 1 | none => return x
  match f 2 with | some y => x := x + y + 1 | none => x := x + 1
  return x

theorem early_return_triple : ⦃⌜True⌝⦄ early_return f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold early_return
  mvcgen +jp
  grind
