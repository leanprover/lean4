/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
import Lean.Fmt.Formatters.Lean.Parser.Term
meta import Lean.Parser.StrInterpolation
import Init.Data

namespace Lean.Fmt

/--
Formats an interpolated string literal like `fmtStr`, with the interpolations rendered as
flattened word-like units. When even placing an interpolation on its own line overflows the page
width, the interpolation is broken apart according to the formatting of the interpolated pattern,
with no other content surrounding it on its lines.
-/
@[builtin_fmt interpolatedStrKind]
public def fmtInterpolatedStr : Fmt := fun stx => do
  let args := stx.getArgs
  -- Alternating literal chunks and interpolated patterns, starting and ending with a chunk.
  if args.size % 2 != 1 then
    throw .partialFormatter
  let mut elems : Array fmtStr.Element := #[]
  for h : i in (0...args.size) do
    let arg := args[i]
    if i % 2 == 1 then
      let term ← fmt arg
      elems := elems.push (.interp term.doc)
      continue
    let some val := arg.isLit? interpolatedStrLitKind
      | throw .partialFormatter
    -- The literal chunks include their delimiters: the first chunk starts with `"` and all
    -- others with `}`; the last chunk ends with `"` and all others with `{`.
    let firstDelimiter := if i == 0 then "\"" else "}"
    let lastDelimiter := if i == args.size - 1 then "\"" else "{"
    if !(val.length >= 2 && val.startsWith firstDelimiter && val.endsWith lastDelimiter) then
      return ← fmtAtomic stx
    let some newElems := fmtStr.lex val.toList.tail.dropLast elems
      | return ← fmtAtomic stx
    elems := newElems
  return Layouts.strLit empty <| ← taggedText (fmtStr.build elems) stx
