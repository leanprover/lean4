/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.Hashable
import Init.Data.Array

public section

namespace Lean.Fmt

def memoHeightLimit : Nat := 6

def nextMemoHeight (memoHeight : Nat) : Nat :=
  if memoHeight = 0 then
    memoHeightLimit
  else
    memoHeight - 1

@[expose]
def FullnessState := UInt8
  deriving BEq, Hashable

@[inline]
def FullnessState.mk (isFullBefore : Bool) (isFullAfter : Bool) : FullnessState :=
  (isFullBefore.toUInt8 <<< 1) ||| isFullAfter.toUInt8

@[inline]
def FullnessState.isFullBefore (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b10) == 1

@[inline]
def FullnessState.isFullAfter (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b1) == 1

@[inline]
def FullnessState.setFullBefore (s : FullnessState) (isFullBefore : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11111101 : UInt8)) ||| (isFullBefore.toUInt8 <<< 1)

@[inline]
def FullnessState.setFullAfter (s : FullnessState) (isFullAfter : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11111110 : UInt8)) ||| isFullAfter.toUInt8

abbrev FailureCond := FullnessState → Bool

inductive Doc where
  | failure
  | newline (flattened? : Option String)
  | text (s : String)
  | flatten (d : Doc)
  | indent (n : Nat) (d : Doc)
  | align (d : Doc)
  | reset (d : Doc)
  | full (d : Doc)
  | either (a b : Doc)
  | concat (a b : Doc)
with
  @[computed_field] isFailure : Doc → FailureCond
    | .failure => fun _ => true
    | .newline .. => (·.isFullAfter)
    | .text s => fun state =>
      match state.isFullBefore, state.isFullAfter with
      | false, false => false
      | true, false => true
      | false, true => true
      | true, true => ! s.isEmpty
    | .full _ => (! ·.isFullAfter)
    | _ => fun _ => false
  @[computed_field] maxNewlineCount? : Doc → Option Nat
    | .failure => none
    | .newline .. => some 1
    | .text _
    | .flatten _ => some 0
    | .indent _ d
    | .align d
    | .reset d
    | .full d => maxNewlineCount? d
    | .either a b => .merge (max · ·) (maxNewlineCount? a) (maxNewlineCount? b)
    | .concat a b => .merge (· + ·) (maxNewlineCount? a) (maxNewlineCount? b)
  @[computed_field] memoHeight : Doc → Nat
    | .failure
    | .newline ..
    | .text _ => memoHeightLimit
    | .flatten d
    | .indent _ d
    | .align d
    | .reset d
    | .full d =>
      let n := memoHeight d
      nextMemoHeight n
    | .either a b
    | .concat a b =>
      let n := min (memoHeight a) (memoHeight b)
      nextMemoHeight n
deriving Inhabited, Repr

def Doc.maybeFlattened (d : Doc) : Doc :=
  .either d d.flatten

def Doc.nl : Doc :=
  .newline (some " ")

def Doc.break : Doc :=
  .newline (some "")

def Doc.hardNl : Doc :=
  .newline none

def Doc.oneOf (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .failure
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.either d

def Doc.join (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .text ""
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.concat d

def Doc.joinUsing (sep : Doc) (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .text ""
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.concat sep |>.concat d

instance : Append Doc where
  append d1 d2 := d1.concat d2

class ToDoc (α : Type) where
  toDoc : α → Doc

instance : ToDoc Doc where
  toDoc d := d

instance : ToDoc String where
  toDoc s := .text s

syntax:max "f'!" interpolatedStr(term) : term

macro_rules
  | `(f'! $interpStr) => do interpStr.expandInterpolatedStr (← `(Doc)) (← `(ToDoc.toDoc))
