/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/
module

prelude
public import Init.Prelude
import Init.Data.String.Modify
import Init.Data.Array.BinSearch

set_option doc.verso true

public section

namespace Lean.Html

/-! # Code points -/

/-- Whether {name}`c` is a [control](https://infra.spec.whatwg.org/#control) code point. -/
def isControl (c : Char) : Bool :=
  let n := c.toNat
  n ≤ 0x001F || (n ≥ 0x007F && n ≤ 0x009F)

/-- Whether {name}`c` is [ASCII whitespace](https://infra.spec.whatwg.org/#ascii-whitespace).
Differs from {name}`Char.isWhitespace` by also including FF U+000C. -/
def isAsciiWhitespace (c : Char) : Bool :=
  c.toNat ∈ [0x0009, 0x000A, 0x000C, 0x000D, 0x0020]

/-- Whether {name}`c` is a [noncharacter](https://infra.spec.whatwg.org/#noncharacter). -/
def isNonCharacter (c : Char) : Bool :=
  let n := c.toNat
  (n ≥ 0xFDD0 && n ≤ 0xFDEF) ||
  n ∈ [0xFFFE, 0xFFFF, 0x1FFFE, 0x1FFFF, 0x2FFFE, 0x2FFFF, 0x3FFFE, 0x3FFFF, 0x4FFFE,
    0x4FFFF, 0x5FFFE, 0x5FFFF, 0x6FFFE, 0x6FFFF, 0x7FFFE, 0x7FFFF, 0x8FFFE, 0x8FFFF,
    0x9FFFE, 0x9FFFF, 0xAFFFE, 0xAFFFF, 0xBFFFE, 0xBFFFF, 0xCFFFE, 0xCFFFF, 0xDFFFE,
    0xDFFFF, 0xEFFFE, 0xEFFFF, 0xFFFFE, 0xFFFFF, 0x10FFFE, 0x10FFFF]

/-! # Tag names -/

/-- Array of void element names, sorted lexicographically. -/
private def voidElements : Array String :=
  #["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source",
    "track", "wbr"]

/-- Whether {name}`tagName` (compared case-insensitively) names a void element.

Void elements are those that cannot have any child nodes.
These only have a start tag; end tags must not be specified.
See https://html.spec.whatwg.org/dev/syntax.html#void-elements. -/
def isVoidElement (tagName : String) : Bool :=
  voidElements.binSearchContains tagName.toLower (· < ·)

end Lean.Html
