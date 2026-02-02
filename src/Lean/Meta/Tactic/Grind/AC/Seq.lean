/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.AC
public import Init.Data.Ord
public section
namespace Lean.Grind.AC

def Seq.length : Seq → Nat
  | .var _ => 1
  | .cons _ s => s.length + 1

/-- Returns `true` if `s` is a variable. -/
def Seq.isVar : (s : Seq) → Bool
  | .var _ => true
  | _ => false

/-- Reverses the sequence -/
def Seq.reverse (s : Seq) : Seq :=
  match s with
  | .var _ => s
  | .cons x s => go s (.var x)
where
  go : Seq → Seq → Seq
    | .var x, acc => .cons x acc
    | .cons x s, acc => go s (.cons x acc)

protected def Seq.compare (s₁ s₂ : Seq) : Ordering :=
  let len₁ := s₁.length
  let len₂ := s₂.length
  if len₁ < len₂ then
    .lt
  else if len₁ > len₂ then
    .gt
  else
    lex s₁ s₂
where
  lex (s₁ s₂ : Seq) : Ordering :=
    match s₁, s₂ with
    | .var x,     .var y     => compare x y
    | .cons ..,   .var _     => .gt
    | .var _,     .cons ..   => .lt
    | .cons x s₁, .cons y s₂ => compare x y |>.then (lex s₁ s₂)

instance : Ord Seq where
  compare := Seq.compare

instance : Append Seq where
  append := Seq.concat

/--
Result type for `s₁.startsWith s₂`
-/
private inductive StartsWithResult where
  | /-- `s₁` does not start with `s₂` -/
    false
  | /-- `s₁ == s₂` -/
    exact
  | /-- `s₁ ++ s == s₂` -/
    prefix (s : Seq)
  deriving Repr, Inhabited

/--
`s₁.startsWith s₂` checks whether `s₁` begins with `s₂`.
-/
private def Seq.startsWith (s₁ s₂ : Seq) : StartsWithResult :=
  match s₂, s₁ with
  | .var x,   .var y       => if x == y then .exact else .false
  | .var x,   .cons y s    => if x == y then .prefix s else .false
  | .cons .., .var _       => .false
  | .cons x s₂, .cons y s₁ => if x == y then s₁.startsWith s₂ else .false

local infixr:65 "::" => Seq.cons
local instance : OfNat Seq n where
  ofNat := .var n

private example : Seq.startsWith 1 1 = .exact := rfl
private example : Seq.startsWith 1 0 = .false := rfl
private example : Seq.startsWith (1::0) 1 = .prefix 0 := rfl
private example : Seq.startsWith 1 (1::0) = .false := rfl
private example : Seq.startsWith (1::0) (1::0) = .exact := rfl
private example : Seq.startsWith (1::0::2) (1::0) = .prefix 2 := rfl
private example : Seq.startsWith (1::0::2::3) (1::0) = .prefix (2::3) := rfl

private def a := 1
private example : a = 1 := by rfl

/--
Result type for `s₁.subseq s₂`
-/
inductive SubseqResult where
  | /-- `s₁` is not a subsequence of `s₂` -/
    false
  | /-- `s₁ == s₂` -/
    exact
  | /-- `s₁ ++ s == s₂` -/
    prefix (s : Seq)
  | /-- `s ++ s₁ == s₂` -/
    suffix (s : Seq)
  | /-- `p ++ s₁ ++ s == s₂` -/
    middle (p s : Seq)

/--
`s₁.subseq s₂` checks whether `s₁` is a subsequence of `s₂`
-/
def Seq.subseq (s₁ s₂ : Seq) : SubseqResult :=
  match s₂ with
  | .var _ => if s₁ == s₂ then .exact else .false
  | .cons x s =>
    match s₂.startsWith s₁ with
    | .false    => go s₁ s (.var x)
    | .exact    => .exact
    | .prefix s => .prefix s
where
  go (s₁ s₂ : Seq) (acc : Seq) :=
    match s₂ with
    | .var _ => if s₁ == s₂ then .suffix acc.reverse else .false
    | .cons x s =>
      match s₂.startsWith s₁ with
      | .false    => go s₁ s (.cons x acc)
      | .exact    => .suffix acc.reverse
      | .prefix s => .middle acc.reverse s

example : Seq.subseq 1 1 = .exact := rfl
example : Seq.subseq 1 2 = .false := rfl
example : Seq.subseq (1::2) 2 = .false := rfl
example : Seq.subseq (1::2) (1::2) = .exact := rfl
example : Seq.subseq 1 (1::2) = .prefix 2 := rfl
example : Seq.subseq 2 (1::2) = .suffix 1 := rfl
example : Seq.subseq 2 (0::1::2) = .suffix (0::1) := rfl
example : Seq.subseq (1::2) (0::1::2::3) = .middle 0 3 := rfl
example : Seq.subseq (2::2) (0::1::2::2::3::4) = .middle (0::1) (3::4) := rfl

/--
Result type for `s₁.subset s₂`
-/
inductive SubsetResult where
  | /-- `s₁` is not a subset of `s₂` -/
    false
  | /-- `s₁ == s₂` -/
    exact
  | /-- `s₁.union s == s₂` -/
    strict (s : Seq)

/--
`s₁.subset s₂` checks whether `s₁` is a subset of `s₂`.
It assumes `s₁` and `s₂` are sorted.
-/
def Seq.subset (s₁ s₂ : Seq) : SubsetResult :=
  match s₁, s₂ with
  | .var x, .var y =>
    if x == y then .exact else .false
  | .var x, .cons y s₂ =>
    if x == y then .strict s₂
    else if x < y then .false
    else go (.var x) s₂ (.var y)
  | .cons .., .var _ => .false
  | .cons x s₁, .cons y s₂ =>
    if x == y then subset s₁ s₂
    else if x < y then .false
    else go (.cons x s₁) s₂ (.var y)
where
  go (s₁ s₂ acc : Seq) : SubsetResult :=
    match s₁, s₂ with
    | .var x, .var y =>
      if x == y then .strict acc.reverse else .false
    | .var x, .cons y s₂ =>
      if x == y then .strict (acc.reverse ++ s₂)
      else if x < y then .false
      else go (.var x) s₂ (.cons y acc)
    | .cons .., .var _ => .false
    | .cons x s₁, .cons y s₂ =>
      if x == y then go s₁ s₂ acc
      else if x < y then .false
      else go (.cons x s₁) s₂ (.cons y acc)

example : Seq.subset 1 1 = .exact := rfl
example : Seq.subset 1 2 = .false := rfl
example : Seq.subset (1::2) 2 = .false := rfl
example : Seq.subset (1::2) (1::2) = .exact := rfl
example : Seq.subset 1 (1::2) = .strict 2 := rfl
example : Seq.subset 2 (1::2) = .strict 1 := rfl
example : Seq.subset 2 (0::1::2) = .strict (0::1) := rfl
example : Seq.subset (2::2) (0::1::2::2::3::4) = .strict (0::1::3::4) := rfl
example : Seq.subset (1::2) (0::1::1::1::2::2::3::4) = .strict (0::1::1::2::3::4) := rfl
example : Seq.subset (1::1::2) (0::1::1::1::2::2::3::4) = .strict (0::1::2::3::4) := rfl

def Seq.isSorted (s : Seq) : Bool :=
  match s with
  | .var _ => true
  | .cons x s => go x s
where
  go (x : Var) (s : Seq) : Bool :=
    match s with
    | .var y => x ≤ y
    | .cons y s => x ≤ y && go y s

def Seq.contains (s : Seq) (x : Var) : Bool :=
  match s with
  | .var y => x == y
  | .cons y s => x == y || s.contains x

def Seq.noAdjacentDuplicates (s : Seq) : Bool :=
  match s with
  | .var _ => true
  | .cons x s => go x s
where
  go (x : Var) (s : Seq) : Bool :=
    match s with
    | .var y => x != y
    | .cons y s => x != y && go y s

example : Seq.erase0 (1::0) = 1 := rfl
example : Seq.erase0 (0::1) = 1 := rfl
example : Seq.erase0 (0::1::2) = 1::2 := rfl

/--
Returns `true` if `s₁` and `s₂` have at least one variable in common.
The function assumes both of them are sorted.
-/
def Seq.sharesVar (s₁ s₂ : Seq) : Bool :=
  match s₁, s₂ with
  | .var x,     .var y     => x == y
  | .var x,     .cons y s₂ => x == y || sharesVar (.var x) s₂
  | .cons x s₁, .var y     => x == y || sharesVar s₁ (.var y)
  | .cons x s₁, .cons y s₂ =>
    if x == y then true
    else if x < y then s₁.sharesVar (.cons y s₂)
    else sharesVar (.cons x s₁) s₂
termination_by (s₁.length, s₂.length)
decreasing_by all_goals sorry -- TODO: restore after bootstrap

example : Seq.sharesVar 0 0 = true := by simp [Seq.sharesVar, OfNat.ofNat]
example : Seq.sharesVar (0::1::2) (2::3) = true := by simp [Seq.sharesVar, OfNat.ofNat]
example : Seq.sharesVar (2::3) (0::1::2) = true := by simp [Seq.sharesVar, OfNat.ofNat]
example : Seq.sharesVar (0::1::2) (3::3) = false := by simp [Seq.sharesVar, OfNat.ofNat]
example : Seq.sharesVar (0::2::3) (0::1::2) = true := by simp [Seq.sharesVar, OfNat.ofNat]

def toSeq? (xs : List Var) : Option Seq :=
  match xs with
  | [] => none
  | x::xs => some <| go xs (.var x)
where
  go (xs : List Var) (acc : Seq) : Seq :=
    match xs with
    | [] => acc.reverse
    | x::xs => go xs (.cons x acc)

private def push (s? : Option Seq) (x : Var) : Option Seq :=
  match s? with
  | none => some (.var x)
  | some s => some (.cons x s)

private def rev (s? : Option Seq) : Option Seq :=
  Seq.reverse <$> s?

private def app (s? : Option Seq) (s' : Seq) : Option Seq :=
  match s? with
  | none   => some s'
  | some s => some (s ++ s')

/--
Returns `some (r₁, c, r₂)` if `s₁ == r₁.union c` and `s₂ == r₂.union c`

It assumes `s₁` and `s₂` are sorted
-/
def Seq.superposeAC? (s₁ s₂ : Seq) : Option (Seq × Seq × Seq) :=
  go s₁ s₂ none none none
where
  mkResult (r₁ c r₂ : Option Seq) : Option (Seq × Seq × Seq) :=
    match r₁, c, r₂ with
    | some r₁, some c, some r₂ => some (r₁, c, r₂)
    | _, _, _ => none

  go (s₁ s₂ : Seq) (r₁ c r₂ : Option Seq) : Option (Seq × Seq × Seq) :=
    match s₁, s₂ with
    | .var x, .var y =>
      if x == y then mkResult (rev r₁) (rev (push c x)) (rev r₂)
      else mkResult (rev (push r₁ x)) (rev c) (rev (push r₂ y))
    | .var x, .cons y s₂ =>
      if x == y then mkResult (rev r₁) (rev (push c x)) (app (rev r₂) s₂)
      else if x < y then mkResult (rev (push r₁ x)) (rev c) (app (rev r₂) (.cons y s₂))
      else go (.var x) s₂ r₁ c (push r₂ y)
    | .cons x s₁, .var y =>
      if x == y then mkResult (app (rev r₁) s₁) (rev (push c x)) (rev r₂)
      else if x < y then go s₁ (.var y) (push r₁ x) c r₂
      else mkResult (app (rev r₁) (.cons x s₁)) (rev c) (rev (push r₂ y))
    | .cons x s₁, .cons y s₂ =>
      if x == y then go s₁ s₂ r₁ (push c x) r₂
      else if x < y then go s₁ (.cons y s₂) (push r₁ x) c r₂
      else go (.cons x s₁) s₂ r₁ c (push r₂ y)
  termination_by (s₁.length, s₂.length)
  decreasing_by all_goals sorry -- TODO: restore after bootstrap

/--
Returns `some (p, c, s)` if `s₁ == p ++ c` and `s₂ == c ++ s`
-/
def Seq.superpose? (s₁ s₂ : Seq) : Option (Seq × Seq × Seq) :=
  match s₁ with
  | .var _ => none
  | .cons x s₁ => go s₁ s₂ (.var x)
where
  go (s₁ s₂ p : Seq) : Option (Seq × Seq × Seq) :=
    match s₂.startsWith s₁ with
    | .false => match s₁ with
      | .var _ => none
      | .cons x s₁ => go s₁ s₂ (.cons x p)
    | .exact => none
    | .prefix s => some (p.reverse, s₁, s)

def Seq.firstVar (s : Seq) : Var :=
  match s with
  | .var x => x
  | .cons x _ => x

def Seq.startsWithVar (s : Seq) (x : Var) : Bool :=
  match s with
  | .var y => x == y
  | .cons y _ => x == y

def Seq.lastVar (s : Seq) : Var :=
  match s with
  | .var x => x
  | .cons _ s => s.lastVar

def Seq.endsWithVar (s : Seq) (x : Var) : Bool :=
  match s with
  | .var y => x == y
  | .cons _ s => s.endsWithVar x

end Lean.Grind.AC
