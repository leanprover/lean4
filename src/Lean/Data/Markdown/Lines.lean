/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.String.Subslice
public import Init.Data.String.Lemmas.Order
import Init.Data.String.OrderInstances
import Init.While
public import Init.Data.String.FindPos

namespace Lean.Markdown

/-!
# Source Lines

A nonempty array of source lines, and the subslice operations that the parser uses to delimit them.
-/

variable {s : String.Slice}

/-- The subslice from `a` to `b`, or the empty subslice at `a` if `b` is before `a`. -/
public def subsliceClamped (a b : s.Pos) : s.Subslice :=
  if h : a ≤ b then s.subslice a b h else s.subslice a a (String.Slice.Pos.le_refl a)

/--
Parses a line ending, which is `\r\n`, `\r`, or `\n` (CommonMark §2.1), at `p` in `input`. Returns
the position after the ending.
-/
public def parseLineEnding? (input : s.Subslice) (p : s.Pos) : Option s.Pos :=
  if h : p < input.endExclusive then
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let q := p.next h'
    match p.get h' with
    | '\n' => some q
    | '\r' =>
      if h2 : q < input.endExclusive then
        let h2' := String.Slice.Pos.ne_endPos_of_lt h2
        some (if q.get h2' == '\n' then q.next h2' else q)
      else some q
    | _ => none
  else none

/-- `text` without the trailing characters that satisfy `p`. -/
public def trimTrailing (text : s.Subslice) (p : Char → Bool) : s.Subslice := Id.run do
  let mut stop := text.endExclusive
  while text.startInclusive < stop do
    match stop.prev? with
    | some q =>
      if text.startInclusive ≤ q && Option.any p q.get? then stop := q else break
    | none => break
  return subsliceClamped text.startInclusive stop

/--
The text of a construct that may span source lines, as one subslice per line.

The lines are in source order and are nonempty. The subslices exclude line endings and the prefixes
of enclosing containers.
-/
public structure Lines (s : String.Slice) where
  /-- The subslices, one per source line, in source order. -/
  toArray : Array s.Subslice
  /-- There is at least one line. -/
  nonempty : 0 < toArray.size

namespace Lines

variable {s : String.Slice}

/-- A single line. -/
public def singleton (line : s.Subslice) : Lines s := ⟨#[line], by simp⟩

/-- Appends a line. -/
public def push (lines : Lines s) (line : s.Subslice) : Lines s :=
  ⟨lines.toArray.push line, by simp⟩

/-- The first line. -/
public def first (lines : Lines s) : s.Subslice := lines.toArray[0]'lines.nonempty

/-- The last line. -/
public def last (lines : Lines s) : s.Subslice := lines.toArray.back lines.nonempty

/-- The text of each line, as a string. -/
public def copy (lines : Lines s) : Array String := lines.toArray.map (·.copy)

/-- The text of the lines, joined by `sep`. -/
public def text (lines : Lines s) (sep : String := "\n") : String :=
  sep.intercalate lines.copy.toList

public instance : Inhabited (Lines s) := ⟨singleton default⟩

end Lines

/-- The subslice from the start of `first` to the end of `last`. -/
public def span (first last : s.Subslice) : s.Subslice :=
  subsliceClamped first.startInclusive last.endExclusive

/-- The subslice from the start of the first line to the end of the last. -/
public def Lines.extent (lines : Lines s) : s.Subslice :=
  span lines.first lines.last
