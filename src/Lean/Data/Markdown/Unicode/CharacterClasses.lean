/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Char.Basic
public import Init.Data.Array.Basic
import Init.Data.Array.BinSearch
import Init.Data.String.Basic
import Init.Data.String.Iterate

set_option doc.verso true

namespace Lean.Markdown

/-!
# Character classes for the emphasis rules

CommonMark's flanking rules classify the characters around a `*` or {lit}`_` sequence as whitespace,
punctuation, or other. Whitespace is the Unicode {lit}`Zs` category plus tab, line feed, form feed,
and carriage return, and punctuation is the Unicode {lit}`P` and {lit}`S` categories. Both
predicates follow Unicode 18.0.0 exactly.
-/

/--
The characters of the Unicode {lit}`P` and {lit}`S` general categories in Unicode 18.0.0, as 385
inclusive ranges in increasing order, one per line as two hexadecimal code points. Each range lies
within one block, and lines that start with `#` are comments.

The table is a string to keep the {lit}`.olean` file and generated C small.
-/
-- The test `tests/elab/markdown_character_classes.lean` checks the table against the Unicode data
-- in `tests/elab/unicode/DerivedGeneralCategory.txt`.
def punctuationRangeData : String := "
# Basic Latin
0021 002F
003A 0040
005B 0060
007B 007E
# Latin-1 Supplement
00A1 00A9
00AB 00AC
00AE 00B1
00B4 00B4
00B6 00B8
00BB 00BB
00BF 00BF
00D7 00D7
00F7 00F7
# Spacing Modifier Letters
02C2 02C5
02D2 02DF
02E5 02EB
02ED 02ED
02EF 02FF
# Greek and Coptic
0375 0375
037E 037E
0384 0385
0387 0387
03F6 03F6
# Cyrillic
0482 0482
# Armenian
055A 055F
0589 058A
058D 058F
# Hebrew
05BE 05BE
05C0 05C0
05C3 05C3
05C6 05C6
05F3 05F4
# Arabic
0606 060F
061B 061B
061D 061F
066A 066D
06D4 06D4
06DE 06DE
06E9 06E9
06FD 06FE
# Syriac
0700 070D
# NKo
07F6 07F9
07FE 07FF
# Samaritan
0830 083E
# Mandaic
085E 085E
# Arabic Extended-B
0888 0888
# Devanagari
0964 0965
0970 0970
# Bengali
09F2 09F3
09FA 09FB
09FD 09FD
# Gurmukhi
0A76 0A76
# Gujarati
0AF0 0AF1
# Oriya
0B70 0B70
# Tamil
0BF3 0BFA
# Telugu
0C77 0C77
0C7F 0C7F
# Kannada
0C84 0C84
# Malayalam
0D4F 0D4F
0D79 0D79
# Sinhala
0DF4 0DF4
# Thai
0E3F 0E3F
0E4F 0E4F
0E5A 0E5B
# Tibetan
0F01 0F17
0F1A 0F1F
0F34 0F34
0F36 0F36
0F38 0F38
0F3A 0F3D
0F85 0F85
0FBE 0FC5
0FC7 0FCC
0FCE 0FDA
# Myanmar
104A 104F
109E 109F
# Georgian
10FB 10FB
# Ethiopic
1360 1368
# Ethiopic Supplement
1390 1399
# Unified Canadian Aboriginal Syllabics
1400 1400
166D 166E
# Ogham
169B 169C
# Runic
16EB 16ED
# Hanunoo
1735 1736
# Khmer
17D4 17D6
17D8 17DB
# Mongolian
1800 180A
# Limbu
1940 1940
1944 1945
# New Tai Lue
19DE 19DF
# Khmer Symbols
19E0 19FF
# Buginese
1A1E 1A1F
# Tai Tham
1AA0 1AA6
1AA8 1AAD
# Balinese
1B4E 1B4F
1B5A 1B6A
1B74 1B7F
# Batak
1BFC 1BFF
# Lepcha
1C3B 1C3F
# Ol Chiki
1C7E 1C7F
# Sundanese Supplement
1CC0 1CC7
# Vedic Extensions
1CD3 1CD3
# Greek Extended
1FBD 1FBD
1FBF 1FC1
1FCD 1FCF
1FDD 1FDF
1FED 1FEF
1FFD 1FFE
# General Punctuation
2010 2027
2030 205E
# Superscripts and Subscripts
207A 207E
208A 208E
# Currency Symbols
20A0 20C4
# Letterlike Symbols
2100 2101
2103 2106
2108 2109
2114 2114
2116 2118
211E 2123
2125 2125
2127 2127
2129 2129
212E 212E
213A 213B
2140 2144
214A 214D
214F 214F
# Number Forms
218A 218B
# Arrows
2190 21FF
# Mathematical Operators
2200 22FF
# Miscellaneous Technical
2300 23FF
# Control Pictures
2400 2429
# Optical Character Recognition
2440 244A
# Enclosed Alphanumerics
249C 24E9
# Box Drawing
2500 257F
# Block Elements
2580 259F
# Geometric Shapes
25A0 25FF
# Miscellaneous Symbols
2600 26FF
# Dingbats
2700 2775
2794 27BF
# Miscellaneous Mathematical Symbols-A
27C0 27EF
# Supplemental Arrows-A
27F0 27FF
# Braille Patterns
2800 28FF
# Supplemental Arrows-B
2900 297F
# Miscellaneous Mathematical Symbols-B
2980 29FF
# Supplemental Mathematical Operators
2A00 2AFF
# Miscellaneous Symbols and Arrows
2B00 2B73
2B76 2BFF
# Coptic
2CE5 2CEA
2CF9 2CFC
2CFE 2CFF
# Tifinagh
2D70 2D70
# Supplemental Punctuation
2E00 2E2E
2E30 2E5D
2E60 2E63
# CJK Radicals Supplement
2E80 2E99
2E9B 2EF3
# Kangxi Radicals
2F00 2FD5
# Ideographic Description Characters
2FF0 2FFF
# CJK Symbols and Punctuation
3001 3004
3008 3020
3030 3030
3036 3037
303D 303F
# Hiragana
309B 309C
# Katakana
30A0 30A0
30FB 30FB
# Kanbun
3190 3191
3196 319F
# CJK Strokes
31C0 31E5
31EF 31EF
# Enclosed CJK Letters and Months
3200 321E
322A 3247
3250 3250
3260 327F
328A 32B0
32C0 32FF
# CJK Compatibility
3300 33FF
# Yijing Hexagram Symbols
4DC0 4DFF
# Yi Radicals
A490 A4C6
# Lisu
A4FE A4FF
# Vai
A60D A60F
# Cyrillic Extended-B
A673 A673
A67E A67E
# Bamum
A6F2 A6F7
# Modifier Tone Letters
A700 A716
# Latin Extended-D
A720 A721
A789 A78A
# Syloti Nagri
A828 A82B
# Common Indic Number Forms
A836 A839
# Phags-pa
A874 A877
# Saurashtra
A8CE A8CF
# Devanagari Extended
A8F8 A8FA
A8FC A8FC
# Kayah Li
A92E A92F
# Rejang
A95F A95F
# Javanese
A9C1 A9CD
A9DE A9DF
# Cham
AA5C AA5F
# Myanmar Extended-A
AA77 AA79
# Tai Viet
AADE AADF
# Meetei Mayek Extensions
AAF0 AAF1
# Latin Extended-E
AB5B AB5B
AB6A AB6B
# Meetei Mayek
ABEB ABEB
# Alphabetic Presentation Forms
FB29 FB29
# Arabic Presentation Forms-A
FBB2 FBD2
FD3E FD4F
FD90 FD91
FDC8 FDCF
FDFC FDFF
# Vertical Forms
FE10 FE19
# CJK Compatibility Forms
FE30 FE4F
# Small Form Variants
FE50 FE52
FE54 FE66
FE68 FE6B
# Halfwidth and Fullwidth Forms
FF01 FF0F
FF1A FF20
FF3B FF40
FF5B FF65
FFE0 FFE6
FFE8 FFEE
# Specials
FFFC FFFD
# Aegean Numbers
10100 10102
10137 1013F
# Ancient Greek Numbers
10179 10189
1018C 1018E
# Ancient Symbols
10190 1019C
101A0 101A0
# Phaistos Disc
101D0 101FC
# Ugaritic
1039F 1039F
# Old Persian
103D0 103D0
# Caucasian Albanian
1056F 1056F
# Imperial Aramaic
10857 10857
# Palmyrene
10877 10878
# Phoenician
1091F 1091F
# Lydian
1093F 1093F
# Kharoshthi
10A50 10A58
# Old South Arabian
10A7F 10A7F
# Manichaean
10AC8 10AC8
10AF0 10AF6
# Avestan
10B39 10B3F
# Psalter Pahlavi
10B99 10B9C
# Garay
10D6E 10D6E
10D8E 10D8F
# Yezidi
10EAD 10EAD
# Arabic Extended-C
10EC9 10ECA
10ED0 10ED8
# Sogdian
10F55 10F59
# Old Uyghur
10F86 10F89
# Brahmi
11047 1104D
# Kaithi
110BB 110BC
110BE 110C1
# Chakma
11140 11143
# Mahajani
11174 11175
# Sharada
111C5 111C8
111CD 111CD
111DB 111DB
111DD 111DF
# Khojki
11238 1123D
# Multani
112A9 112A9
# Tulu-Tigalari
113D4 113D5
113D7 113D8
# Newa
1144B 1144F
1145A 1145B
1145D 1145D
# Tirhuta
114C6 114C6
# Siddham
115C1 115D7
# Modi
11641 11643
# Mongolian Supplement
11660 1166C
# Takri
116B9 116B9
# Ahom
1173C 1173F
# Dogra
1183B 1183B
# Dives Akuru
11944 11946
# Nandinagari
119E2 119E2
# Zanabazar Square
11A3F 11A46
# Soyombo
11A9A 11A9C
11A9E 11AA2
# Devanagari Extended-A
11B00 11B09
# Sunuwar
11BE1 11BE1
# Bhaiksuki
11C41 11C45
# Marchen
11C70 11C71
# Makasar
11EF7 11EF8
# Kawi
11F43 11F4F
# Tamil Supplement
11FD5 11FF1
11FFF 11FFF
# Cuneiform Numbers and Punctuation
12470 12474
# Cypro-Minoan
12FF1 12FF2
# Mro
16A6E 16A6F
# Bassa Vah
16AF5 16AF5
# Pahawh Hmong
16B37 16B3F
16B44 16B45
# Kirat Rai
16D6D 16D6F
# Medefaidrin
16E97 16E9A
# Ideographic Symbols and Punctuation
16FE2 16FE2
# Duployan
1BC9C 1BC9C
1BC9F 1BC9F
# Symbols for Legacy Computing Supplement
1CC00 1CCEF
1CCFA 1CCFC
1CD00 1CEB3
1CEBA 1CEBF
# Miscellaneous Symbols Supplement
1CEC0 1CED0
1CED2 1CED4
1CEDD 1CEFD
# Znamenny Musical Notation
1CF50 1CFC3
# Byzantine Musical Symbols
1D000 1D0F5
# Musical Symbols
1D100 1D126
1D129 1D164
1D16A 1D16C
1D183 1D184
1D18C 1D1A9
1D1AE 1D1FF
# Ancient Greek Musical Notation
1D200 1D241
1D245 1D245
# Musical Symbols Supplement
1D253 1D25A
1D25D 1D25E
1D260 1D27F
# Tai Xuan Jing Symbols
1D300 1D356
# Mathematical Alphanumeric Symbols
1D6C1 1D6C1
1D6DB 1D6DB
1D6FB 1D6FB
1D715 1D715
1D735 1D735
1D74F 1D74F
1D76F 1D76F
1D789 1D789
1D7A9 1D7A9
1D7C3 1D7C3
# Sutton SignWriting
1D800 1D9FF
1DA37 1DA3A
1DA6D 1DA74
1DA76 1DA83
1DA85 1DA8B
# Miscellaneous Symbols and Arrows Extended
1DB00 1DB1C
# Nyiakeng Puachue Hmong
1E14F 1E14F
# Wancho
1E2FF 1E2FF
# Ol Onal
1E5FF 1E5FF
# Adlam
1E95E 1E95F
# Indic Siyaq Numbers
1ECAC 1ECAC
1ECB0 1ECB0
# Ottoman Siyaq Numbers
1ED2E 1ED2E
# Arabic Mathematical Alphabetic Symbols
1EEF0 1EEF1
# Mahjong Tiles
1F000 1F02B
# Domino Tiles
1F030 1F093
# Playing Cards
1F0A0 1F0AE
1F0B1 1F0BF
1F0C1 1F0CF
1F0D1 1F0F5
# Enclosed Alphanumeric Supplement
1F10D 1F1AE
1F1E6 1F1FF
# Enclosed Ideographic Supplement
1F200 1F202
1F210 1F23B
1F240 1F248
1F250 1F251
1F260 1F265
# Miscellaneous Symbols and Pictographs
1F300 1F5FF
# Emoticons
1F600 1F64F
# Ornamental Dingbats
1F650 1F67F
# Transport and Map Symbols
1F680 1F6D9
1F6DC 1F6EC
1F6F0 1F6FC
# Alchemical Symbols
1F700 1F77F
# Geometric Shapes Extended
1F780 1F7DB
1F7E0 1F7EB
1F7F0 1F7FF
# Supplemental Arrows-C
1F800 1F80B
1F810 1F847
1F850 1F859
1F860 1F887
1F890 1F8AD
1F8B0 1F8BB
1F8C0 1F8C1
1F8D0 1F8D8
# Supplemental Symbols and Pictographs
1F900 1F9FF
# Chess Symbols
1FA00 1FA57
1FA60 1FA6D
# Symbols and Pictographs Extended-A
1FA70 1FA7C
1FA80 1FAC6
1FAC8 1FAC8
1FACC 1FADD
1FADF 1FAEB
1FAEF 1FAFA
# Symbols for Legacy Computing
1FB00 1FB92
1FB94 1FBEF
1FBFA 1FBFA
"

/-- The value of the hexadecimal digit {name}`c`, or {lean}`0` for any other character. -/
def hexDigit (c : Char) : UInt32 :=
  if c.isDigit then c.val - '0'.val
  else if 'A' ≤ c && c ≤ 'F' then c.val - 'A'.val + 10
  else 0

/--
The ranges of {name}`punctuationRangeData`, as inclusive pairs in increasing order.
-/
def punctuationRanges : Array (UInt32 × UInt32) := Id.run do
  let mut ranges := Array.emptyWithCapacity 400
  let mut numeral : UInt32 := 0
  let mut first? : Option UInt32 := none
  let mut inBlockName := false
  for c in punctuationRangeData do
    if inBlockName then
      if c == '\n' then inBlockName := false
    else if c == '#' then
      inBlockName := true
    else if c == ' ' then
      first? := some numeral
      numeral := 0
    else if c == '\n' then
      if let some first := first? then ranges := ranges.push (first, numeral)
      first? := none
      numeral := 0
    else
      numeral := numeral * 16 + hexDigit c
  return ranges

/--
Whether {name}`c` is Unicode punctuation in the sense of CommonMark: a character of the {lit}`P`
(punctuation) or {lit}`S` (symbol) general categories, per Unicode 18.0.0. This includes the ASCII
punctuation, the mathematical operators and arrows, currency signs, and emoji, and it excludes
letters, digits, whitespace, and combining marks.
-/
public def isUnicodePunctuation (c : Char) : Bool :=
  -- A range is less than a probe when it ends before the probe's code point, so the search finds
  -- the range that contains the code point if there is one.
  punctuationRanges.binSearchContains (c.val, c.val) fun a b => a.2 < b.1

/--
Whether {name}`c` is Unicode whitespace in the sense of CommonMark: a character of the {lit}`Zs`
general category, or a tab, line feed, form feed, or carriage return. The {lit}`Zs` category has
seventeen characters in Unicode 18.0.0.
-/
public def isUnicodeWhitespace (c : Char) : Bool :=
  match c with
  | ' ' | '\t' | '\n' | '\x0C' | '\r' => true
  -- The no-break space, the Ogham space mark, the narrow no-break space, the medium mathematical
  -- space, and the ideographic space.
  | '\u00A0' | '\u1680' | '\u202F' | '\u205F' | '\u3000' => true
  -- The en quad through the hair space.
  | _ => '\u2000' ≤ c && c ≤ '\u200A'
