/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Core
public import Init.Grind.AC
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

end Lean.Grind.AC
