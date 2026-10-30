/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.Char.Basic

namespace Lean.Markdown

/-!
This module implements Unicode full case folding, as specified by the entries with status `C` and
`F` in `CaseFolding.txt` of Unicode 18.0.0, for ASCII, the Latin-1 Supplement block, and the Greek
and Coptic block, together with every character elsewhere whose folding consists of characters from
those blocks, such as `Ÿ`, `ẞ`, the Kelvin sign, and the ligature `ﬁ`. Every other character folds
to itself.
-/

/-- Whether `c` is between `lo` and `hi`, inclusive. -/
@[inline] def between (c lo hi : Char) : Bool :=
  lo ≤ c && c ≤ hi

/-- The character `n` code points after `c`, as a string. -/
@[inline] def shifted (c : Char) (n : Nat) : String :=
  String.singleton (Char.ofNat (c.toNat + n))

/--
The folding of `c`, when it is not `c` itself.
-/
def fold? (c : Char) : Option String :=
  -- The character is first located by its block of 256 code points and, within the Greek and
  -- Coptic block, by its row of 16, so that a lookup is a few comparisons. The groups follow
  -- `CaseFolding.txt`.
  match c.val >>> 8 with
  | 0x00 => latin1 c
  | 0x01 =>
    match c with
    | 'Ÿ' => some "ÿ"
    | 'ſ' => some "s"
    | _ => none
  | 0x03 => greek c
  | 0x1E => if c == 'ẞ' then some "ss" else none
  | 0x1F => polytonic c
  | 0x21 =>
    -- The Ohm, Kelvin, and Angstrom signs, as escapes because the literals look like `Ω`, `K`,
    -- and `Å`.
    match c with
    | '\u2126' => some "ω"
    | '\u212A' => some "k"
    | '\u212B' => some "å"
    | _ => none
  | 0xFB => ligatures c
  -- The historical ligature of long `ſ` and `s` that became `ß`, U+1DF95 in Latin Extended-G, which
  -- is beyond the reach of a `\u` escape and which few fonts render. It is also known as
  -- `LATIN SMALL LIGATURE LONG S WITH DESCENDER S`
  | 0x1DF => if c == '𝾕' then some "ss" else none
  | _ => none
where
  /--
  Latin-1 Supplement: `À` to `Þ` fold 32 code points up, except for the multiplication sign between
  `Ö` and `Ø`; the micro sign folds to Greek `μ`; and `ß` folds to `ss`.
  -/
  latin1 (c : Char) : Option String :=
    if between c 'À' 'Ö' || between c 'Ø' 'Þ' then some (shifted c 0x20)
    else
      match c with
      | '\u00B5' => some "μ"  -- the micro sign, as an escape because the literal looks like `μ`
      | 'ß' => some "ss"
      | _ => none
  /-- Greek and Coptic -/
  greek (c : Char) : Option String :=
    -- Comparisons performed by row of 16 code points.
    match c.val >>> 4 with
    -- The combining iota subscript folds to `ι`.
    | 0x34 => if c == '\u0345' then some "ι" else none
    -- The archaic letters at the start of the block.
    | 0x37 =>
      match c with
      | 'Ͱ' => some "ͱ"
      | 'Ͳ' => some "ͳ"
      | 'Ͷ' => some "ͷ"
      | 'Ϳ' => some "ϳ"
      | _ => none
    -- The accented capitals.
    | 0x38 =>
      match c with
      | 'Ά' => some "ά"
      | 'Έ' => some "έ"
      | 'Ή' => some "ή"
      | 'Ί' => some "ί"
      | 'Ό' => some "ό"
      | 'Ύ' => some "ύ"
      | 'Ώ' => some "ώ"
      | _ => none
    -- The alphabet `Α` to `Ϋ` folds 32 code points up, with a gap after `Ρ`, and `ΐ` folds to the
    -- bare vowel followed by the combining diaeresis and acute accent.
    | 0x39 | 0x3A =>
      if between c 'Α' 'Ρ' || between c 'Σ' 'Ϋ' then some (shifted c 0x20)
      else if c == 'ΐ' then some "ι\u0308\u0301"
      else none
    | 0x3B => if c == 'ΰ' then some "υ\u0308\u0301" else none
    -- Final sigma, and the kai symbol.
    | 0x3C =>
      match c with
      | 'ς' => some "σ"
      | 'Ϗ' => some "ϗ"
      | _ => none
    -- The archaic and Coptic letters `Ϙ` to `Ϯ` are in upper and lower pairs, and the rows also
    -- hold symbol variants of letters.
    | 0x3D | 0x3E =>
      if between c 'Ϙ' 'Ϯ' && c.val % 2 == 0 then some (shifted c 1)
      else
        match c with
        | 'ϐ' => some "β"
        | 'ϑ' => some "θ"
        | 'ϕ' => some "φ"
        | 'ϖ' => some "π"
        | _ => none
    -- More symbol variants, and `Ͻ`, `Ͼ`, and `Ͽ`, which fold to the lunate sigmas near the start
    -- of the block.
    | 0x3F =>
      match c with
      | 'ϰ' => some "κ"
      | 'ϱ' => some "ρ"
      | 'ϴ' => some "θ"
      | 'ϵ' => some "ε"
      | 'Ϸ' => some "ϸ"
      | 'Ϲ' => some "ϲ"
      | 'Ϻ' => some "ϻ"
      | 'Ͻ' => some "ͻ"
      | 'Ͼ' => some "ͼ"
      | 'Ͽ' => some "ͽ"
      | _ => none
    | _ => none
  /--
  Greek Extended: the letters with iota subscript fold to the vowel followed by `ι`, and the
  prosgegrammeni, as an escape because the literal looks like `ι`, folds to `ι`.
  -/
  polytonic (c : Char) : Option String :=
    match c with
    | 'ᾳ' | 'ᾼ' => some "αι"
    | 'ᾴ' => some "άι"
    | 'ῃ' | 'ῌ' => some "ηι"
    | 'ῄ' => some "ήι"
    | 'ῳ' | 'ῼ' => some "ωι"
    | 'ῴ' => some "ώι"
    | '\u1FBE' => some "ι"
    | _ => none
  /-- Alphabetic Presentation Forms: the Latin ligatures fold to their letters. -/
  ligatures (c : Char) : Option String :=
    match c with
    | 'ﬀ' => some "ff"
    | 'ﬁ' => some "fi"
    | 'ﬂ' => some "fl"
    | 'ﬃ' => some "ffi"
    | 'ﬄ' => some "ffl"
    | 'ﬅ' | 'ﬆ' => some "st"
    | _ => none

/--
Appends the Unicode full case folding of `c` to `out`, for ASCII, the Latin-1 Supplement block, the
Greek and Coptic block, and the other characters whose foldings are drawn from those blocks. Any
other character is appended unchanged.
-/
public def pushCaseFolded (out : String) (c : Char) : String :=
  -- The micro sign U+00B5 is the first character past ASCII with a folding, so below it the
  -- folding is ASCII lowercasing.
  if c.val < 0xB5 then out.push c.toLower
  else
    match fold? c with
    | some folded => out ++ folded
    | none => out.push c

/--
The Unicode full case folding of `c` for the following characters:
* ASCII
* The Latin-1 Supplement block
* The Greek and Coptic block
* All other characters whose foldings are drawn from the above blocks:
  - `Ÿ`, `ẞ`, `ſ`
  - The Ohm, Kelvin, and Angstrom signs
  - The Latin ligatures `ﬀ` to `ﬆ`
  - The polytonic Greek letters with iota subscript.

For characters not in the above set, `caseFold` is equivalent to `String.singleton`. In particular,
letters with case in Cyrillic, the Latin Extended blocks (Turkish, Vietnamese, Polish, Czech, and
others), Armenian, Georgian, Cherokee, Greek Extended (polytonic Greek), and the fullwidth and
enclosed forms are not folded. This limitation may be lifted in the future.
-/
public def caseFold (c : Char) : String := pushCaseFolded "" c
