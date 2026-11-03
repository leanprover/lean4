/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Char.Basic

set_option doc.verso true

namespace Lean.Markdown

/-!
# Character Classes for the Emphasis Rules

CommonMark's flanking rules classify the characters around a `*` or {lit}`_` sequence as whitespace,
punctuation, or other. Whitespace is the Unicode {lit}`Zs` category plus tab, line feed, form feed,
and carriage return, and punctuation is the Unicode {lit}`P` and {lit}`S` categories. Both
predicates follow Unicode 18.0.0 exactly.
-/

-- The functions below form a binary search tree over the 381 ranges of characters above U+007F in
-- the Unicode `P` and `S` general categories in Unicode 18.0.0, in increasing order. The test
-- `tests/elab/markdown_character_classes.lean` checks the result against the Unicode data in
-- `tests/elab/unicode/DerivedGeneralCategory.txt`.

def punctuation_00A1_02DF (v : UInt32) : Bool :=
  -- Latin-1 Supplement
  (0x00A1 ≤ v && v ≤ 0x00A9) ||
  (0x00AB ≤ v && v ≤ 0x00AC) ||
  (0x00AE ≤ v && v ≤ 0x00B1) ||
  v == 0x00B4 ||
  (0x00B6 ≤ v && v ≤ 0x00B8) ||
  v == 0x00BB ||
  v == 0x00BF ||
  v == 0x00D7 ||
  v == 0x00F7 ||
  -- Spacing Modifier Letters
  (0x02C2 ≤ v && v ≤ 0x02C5) ||
  (0x02D2 ≤ v && v ≤ 0x02DF)

def punctuation_02E5_058F (v : UInt32) : Bool :=
  -- Spacing Modifier Letters
  (0x02E5 ≤ v && v ≤ 0x02EB) ||
  v == 0x02ED ||
  (0x02EF ≤ v && v ≤ 0x02FF) ||
  -- Greek and Coptic
  v == 0x0375 ||
  v == 0x037E ||
  (0x0384 ≤ v && v ≤ 0x0385) ||
  v == 0x0387 ||
  v == 0x03F6 ||
  -- Cyrillic
  v == 0x0482 ||
  -- Armenian
  (0x055A ≤ v && v ≤ 0x055F) ||
  (0x0589 ≤ v && v ≤ 0x058A) ||
  (0x058D ≤ v && v ≤ 0x058F)

def punctuation_00A1_058F (v : UInt32) : Bool :=
  if v < 0x02E5 then punctuation_00A1_02DF v else punctuation_02E5_058F v

def punctuation_05BE_06E9 (v : UInt32) : Bool :=
  -- Hebrew
  v == 0x05BE ||
  v == 0x05C0 ||
  v == 0x05C3 ||
  v == 0x05C6 ||
  (0x05F3 ≤ v && v ≤ 0x05F4) ||
  -- Arabic
  (0x0606 ≤ v && v ≤ 0x060F) ||
  v == 0x061B ||
  (0x061D ≤ v && v ≤ 0x061F) ||
  (0x066A ≤ v && v ≤ 0x066D) ||
  v == 0x06D4 ||
  v == 0x06DE ||
  v == 0x06E9

def punctuation_06FD_09FD (v : UInt32) : Bool :=
  -- Arabic
  (0x06FD ≤ v && v ≤ 0x06FE) ||
  -- Syriac
  (0x0700 ≤ v && v ≤ 0x070D) ||
  -- NKo
  (0x07F6 ≤ v && v ≤ 0x07F9) ||
  (0x07FE ≤ v && v ≤ 0x07FF) ||
  -- Samaritan
  (0x0830 ≤ v && v ≤ 0x083E) ||
  -- Mandaic
  v == 0x085E ||
  -- Arabic Extended-B
  v == 0x0888 ||
  -- Devanagari
  (0x0964 ≤ v && v ≤ 0x0965) ||
  v == 0x0970 ||
  -- Bengali
  (0x09F2 ≤ v && v ≤ 0x09F3) ||
  (0x09FA ≤ v && v ≤ 0x09FB) ||
  v == 0x09FD

def punctuation_05BE_09FD (v : UInt32) : Bool :=
  if v < 0x06FD then punctuation_05BE_06E9 v else punctuation_06FD_09FD v

def punctuation_00A1_09FD (v : UInt32) : Bool :=
  if v < 0x05BE then punctuation_00A1_058F v else punctuation_05BE_09FD v

def punctuation_0A76_0E4F (v : UInt32) : Bool :=
  -- Gurmukhi
  v == 0x0A76 ||
  -- Gujarati
  (0x0AF0 ≤ v && v ≤ 0x0AF1) ||
  -- Oriya
  v == 0x0B70 ||
  -- Tamil
  (0x0BF3 ≤ v && v ≤ 0x0BFA) ||
  -- Telugu
  v == 0x0C77 ||
  v == 0x0C7F ||
  -- Kannada
  v == 0x0C84 ||
  -- Malayalam
  v == 0x0D4F ||
  v == 0x0D79 ||
  -- Sinhala
  v == 0x0DF4 ||
  -- Thai
  v == 0x0E3F ||
  v == 0x0E4F

def punctuation_0E5A_104F (v : UInt32) : Bool :=
  -- Thai
  (0x0E5A ≤ v && v ≤ 0x0E5B) ||
  -- Tibetan
  (0x0F01 ≤ v && v ≤ 0x0F17) ||
  (0x0F1A ≤ v && v ≤ 0x0F1F) ||
  v == 0x0F34 ||
  v == 0x0F36 ||
  v == 0x0F38 ||
  (0x0F3A ≤ v && v ≤ 0x0F3D) ||
  v == 0x0F85 ||
  (0x0FBE ≤ v && v ≤ 0x0FC5) ||
  (0x0FC7 ≤ v && v ≤ 0x0FCC) ||
  (0x0FCE ≤ v && v ≤ 0x0FDA) ||
  -- Myanmar
  (0x104A ≤ v && v ≤ 0x104F)

def punctuation_0A76_104F (v : UInt32) : Bool :=
  if v < 0x0E5A then punctuation_0A76_0E4F v else punctuation_0E5A_104F v

def punctuation_109E_180A (v : UInt32) : Bool :=
  -- Myanmar
  (0x109E ≤ v && v ≤ 0x109F) ||
  -- Georgian
  v == 0x10FB ||
  -- Ethiopic
  (0x1360 ≤ v && v ≤ 0x1368) ||
  -- Ethiopic Supplement
  (0x1390 ≤ v && v ≤ 0x1399) ||
  -- Unified Canadian Aboriginal Syllabics
  v == 0x1400 ||
  (0x166D ≤ v && v ≤ 0x166E) ||
  -- Ogham
  (0x169B ≤ v && v ≤ 0x169C) ||
  -- Runic
  (0x16EB ≤ v && v ≤ 0x16ED) ||
  -- Hanunoo
  (0x1735 ≤ v && v ≤ 0x1736) ||
  -- Khmer
  (0x17D4 ≤ v && v ≤ 0x17D6) ||
  (0x17D8 ≤ v && v ≤ 0x17DB) ||
  -- Mongolian
  (0x1800 ≤ v && v ≤ 0x180A)

def punctuation_1940_1C3F (v : UInt32) : Bool :=
  -- Limbu
  v == 0x1940 ||
  (0x1944 ≤ v && v ≤ 0x1945) ||
  -- New Tai Lue
  (0x19DE ≤ v && v ≤ 0x19DF) ||
  -- Khmer Symbols
  (0x19E0 ≤ v && v ≤ 0x19FF) ||
  -- Buginese
  (0x1A1E ≤ v && v ≤ 0x1A1F) ||
  -- Tai Tham
  (0x1AA0 ≤ v && v ≤ 0x1AA6) ||
  (0x1AA8 ≤ v && v ≤ 0x1AAD) ||
  -- Balinese
  (0x1B4E ≤ v && v ≤ 0x1B4F) ||
  (0x1B5A ≤ v && v ≤ 0x1B6A) ||
  (0x1B74 ≤ v && v ≤ 0x1B7F) ||
  -- Batak
  (0x1BFC ≤ v && v ≤ 0x1BFF) ||
  -- Lepcha
  (0x1C3B ≤ v && v ≤ 0x1C3F)

def punctuation_109E_1C3F (v : UInt32) : Bool :=
  if v < 0x1940 then punctuation_109E_180A v else punctuation_1940_1C3F v

def punctuation_0A76_1C3F (v : UInt32) : Bool :=
  if v < 0x109E then punctuation_0A76_104F v else punctuation_109E_1C3F v

def punctuation_00A1_1C3F (v : UInt32) : Bool :=
  if v < 0x0A76 then punctuation_00A1_09FD v else punctuation_0A76_1C3F v

def punctuation_1C7E_205E (v : UInt32) : Bool :=
  -- Ol Chiki
  (0x1C7E ≤ v && v ≤ 0x1C7F) ||
  -- Sundanese Supplement
  (0x1CC0 ≤ v && v ≤ 0x1CC7) ||
  -- Vedic Extensions
  v == 0x1CD3 ||
  -- Greek Extended
  v == 0x1FBD ||
  (0x1FBF ≤ v && v ≤ 0x1FC1) ||
  (0x1FCD ≤ v && v ≤ 0x1FCF) ||
  (0x1FDD ≤ v && v ≤ 0x1FDF) ||
  (0x1FED ≤ v && v ≤ 0x1FEF) ||
  (0x1FFD ≤ v && v ≤ 0x1FFE) ||
  -- General Punctuation
  (0x2010 ≤ v && v ≤ 0x2027) ||
  (0x2030 ≤ v && v ≤ 0x205E)

def punctuation_207A_2129 (v : UInt32) : Bool :=
  -- Superscripts and Subscripts
  (0x207A ≤ v && v ≤ 0x207E) ||
  (0x208A ≤ v && v ≤ 0x208E) ||
  -- Currency Symbols
  (0x20A0 ≤ v && v ≤ 0x20C4) ||
  -- Letterlike Symbols
  (0x2100 ≤ v && v ≤ 0x2101) ||
  (0x2103 ≤ v && v ≤ 0x2106) ||
  (0x2108 ≤ v && v ≤ 0x2109) ||
  v == 0x2114 ||
  (0x2116 ≤ v && v ≤ 0x2118) ||
  (0x211E ≤ v && v ≤ 0x2123) ||
  v == 0x2125 ||
  v == 0x2127 ||
  v == 0x2129

def punctuation_1C7E_2129 (v : UInt32) : Bool :=
  if v < 0x207A then punctuation_1C7E_205E v else punctuation_207A_2129 v

def punctuation_212E_24E9 (v : UInt32) : Bool :=
  -- Letterlike Symbols
  v == 0x212E ||
  (0x213A ≤ v && v ≤ 0x213B) ||
  (0x2140 ≤ v && v ≤ 0x2144) ||
  (0x214A ≤ v && v ≤ 0x214D) ||
  v == 0x214F ||
  -- Number Forms
  (0x218A ≤ v && v ≤ 0x218B) ||
  -- Arrows
  (0x2190 ≤ v && v ≤ 0x21FF) ||
  -- Mathematical Operators
  (0x2200 ≤ v && v ≤ 0x22FF) ||
  -- Miscellaneous Technical
  (0x2300 ≤ v && v ≤ 0x23FF) ||
  -- Control Pictures
  (0x2400 ≤ v && v ≤ 0x2429) ||
  -- Optical Character Recognition
  (0x2440 ≤ v && v ≤ 0x244A) ||
  -- Enclosed Alphanumerics
  (0x249C ≤ v && v ≤ 0x24E9)

def punctuation_2500_2AFF (v : UInt32) : Bool :=
  -- Box Drawing
  (0x2500 ≤ v && v ≤ 0x257F) ||
  -- Block Elements
  (0x2580 ≤ v && v ≤ 0x259F) ||
  -- Geometric Shapes
  (0x25A0 ≤ v && v ≤ 0x25FF) ||
  -- Miscellaneous Symbols
  (0x2600 ≤ v && v ≤ 0x26FF) ||
  -- Dingbats
  (0x2700 ≤ v && v ≤ 0x2775) ||
  (0x2794 ≤ v && v ≤ 0x27BF) ||
  -- Miscellaneous Mathematical Symbols-A
  (0x27C0 ≤ v && v ≤ 0x27EF) ||
  -- Supplemental Arrows-A
  (0x27F0 ≤ v && v ≤ 0x27FF) ||
  -- Braille Patterns
  (0x2800 ≤ v && v ≤ 0x28FF) ||
  -- Supplemental Arrows-B
  (0x2900 ≤ v && v ≤ 0x297F) ||
  -- Miscellaneous Mathematical Symbols-B
  (0x2980 ≤ v && v ≤ 0x29FF) ||
  -- Supplemental Mathematical Operators
  (0x2A00 ≤ v && v ≤ 0x2AFF)

def punctuation_212E_2AFF (v : UInt32) : Bool :=
  if v < 0x2500 then punctuation_212E_24E9 v else punctuation_2500_2AFF v

def punctuation_1C7E_2AFF (v : UInt32) : Bool :=
  if v < 0x212E then punctuation_1C7E_2129 v else punctuation_212E_2AFF v

def punctuation_2B00_2FD5 (v : UInt32) : Bool :=
  -- Miscellaneous Symbols and Arrows
  (0x2B00 ≤ v && v ≤ 0x2B73) ||
  (0x2B76 ≤ v && v ≤ 0x2BFF) ||
  -- Coptic
  (0x2CE5 ≤ v && v ≤ 0x2CEA) ||
  (0x2CF9 ≤ v && v ≤ 0x2CFC) ||
  (0x2CFE ≤ v && v ≤ 0x2CFF) ||
  -- Tifinagh
  v == 0x2D70 ||
  -- Supplemental Punctuation
  (0x2E00 ≤ v && v ≤ 0x2E2E) ||
  (0x2E30 ≤ v && v ≤ 0x2E5D) ||
  (0x2E60 ≤ v && v ≤ 0x2E63) ||
  -- CJK Radicals Supplement
  (0x2E80 ≤ v && v ≤ 0x2E99) ||
  (0x2E9B ≤ v && v ≤ 0x2EF3) ||
  -- Kangxi Radicals
  (0x2F00 ≤ v && v ≤ 0x2FD5)

def punctuation_2FF0_31E5 (v : UInt32) : Bool :=
  -- Ideographic Description Characters
  (0x2FF0 ≤ v && v ≤ 0x2FFF) ||
  -- CJK Symbols and Punctuation
  (0x3001 ≤ v && v ≤ 0x3004) ||
  (0x3008 ≤ v && v ≤ 0x3020) ||
  v == 0x3030 ||
  (0x3036 ≤ v && v ≤ 0x3037) ||
  (0x303D ≤ v && v ≤ 0x303F) ||
  -- Hiragana
  (0x309B ≤ v && v ≤ 0x309C) ||
  -- Katakana
  v == 0x30A0 ||
  v == 0x30FB ||
  -- Kanbun
  (0x3190 ≤ v && v ≤ 0x3191) ||
  (0x3196 ≤ v && v ≤ 0x319F) ||
  -- CJK Strokes
  (0x31C0 ≤ v && v ≤ 0x31E5)

def punctuation_2B00_31E5 (v : UInt32) : Bool :=
  if v < 0x2FF0 then punctuation_2B00_2FD5 v else punctuation_2FF0_31E5 v

def punctuation_31EF_A60F (v : UInt32) : Bool :=
  -- CJK Strokes
  v == 0x31EF ||
  -- Enclosed CJK Letters and Months
  (0x3200 ≤ v && v ≤ 0x321E) ||
  (0x322A ≤ v && v ≤ 0x3247) ||
  v == 0x3250 ||
  (0x3260 ≤ v && v ≤ 0x327F) ||
  (0x328A ≤ v && v ≤ 0x32B0) ||
  (0x32C0 ≤ v && v ≤ 0x32FF) ||
  -- CJK Compatibility
  (0x3300 ≤ v && v ≤ 0x33FF) ||
  -- Yijing Hexagram Symbols
  (0x4DC0 ≤ v && v ≤ 0x4DFF) ||
  -- Yi Radicals
  (0xA490 ≤ v && v ≤ 0xA4C6) ||
  -- Lisu
  (0xA4FE ≤ v && v ≤ 0xA4FF) ||
  -- Vai
  (0xA60D ≤ v && v ≤ 0xA60F)

def punctuation_A673_A8FC (v : UInt32) : Bool :=
  -- Cyrillic Extended-B
  v == 0xA673 ||
  v == 0xA67E ||
  -- Bamum
  (0xA6F2 ≤ v && v ≤ 0xA6F7) ||
  -- Modifier Tone Letters
  (0xA700 ≤ v && v ≤ 0xA716) ||
  -- Latin Extended-D
  (0xA720 ≤ v && v ≤ 0xA721) ||
  (0xA789 ≤ v && v ≤ 0xA78A) ||
  -- Syloti Nagri
  (0xA828 ≤ v && v ≤ 0xA82B) ||
  -- Common Indic Number Forms
  (0xA836 ≤ v && v ≤ 0xA839) ||
  -- Phags-pa
  (0xA874 ≤ v && v ≤ 0xA877) ||
  -- Saurashtra
  (0xA8CE ≤ v && v ≤ 0xA8CF) ||
  -- Devanagari Extended
  (0xA8F8 ≤ v && v ≤ 0xA8FA) ||
  v == 0xA8FC

def punctuation_31EF_A8FC (v : UInt32) : Bool :=
  if v < 0xA673 then punctuation_31EF_A60F v else punctuation_A673_A8FC v

def punctuation_2B00_A8FC (v : UInt32) : Bool :=
  if v < 0x31EF then punctuation_2B00_31E5 v else punctuation_31EF_A8FC v

def punctuation_1C7E_A8FC (v : UInt32) : Bool :=
  if v < 0x2B00 then punctuation_1C7E_2AFF v else punctuation_2B00_A8FC v

def punctuation_00A1_A8FC (v : UInt32) : Bool :=
  if v < 0x1C7E then punctuation_00A1_1C3F v else punctuation_1C7E_A8FC v

def punctuation_A92E_ABEB (v : UInt32) : Bool :=
  -- Kayah Li
  (0xA92E ≤ v && v ≤ 0xA92F) ||
  -- Rejang
  v == 0xA95F ||
  -- Javanese
  (0xA9C1 ≤ v && v ≤ 0xA9CD) ||
  (0xA9DE ≤ v && v ≤ 0xA9DF) ||
  -- Cham
  (0xAA5C ≤ v && v ≤ 0xAA5F) ||
  -- Myanmar Extended-A
  (0xAA77 ≤ v && v ≤ 0xAA79) ||
  -- Tai Viet
  (0xAADE ≤ v && v ≤ 0xAADF) ||
  -- Meetei Mayek Extensions
  (0xAAF0 ≤ v && v ≤ 0xAAF1) ||
  -- Latin Extended-E
  v == 0xAB5B ||
  (0xAB6A ≤ v && v ≤ 0xAB6B) ||
  -- Meetei Mayek
  v == 0xABEB

def punctuation_FB29_FF0F (v : UInt32) : Bool :=
  -- Alphabetic Presentation Forms
  v == 0xFB29 ||
  -- Arabic Presentation Forms-A
  (0xFBB2 ≤ v && v ≤ 0xFBD2) ||
  (0xFD3E ≤ v && v ≤ 0xFD4F) ||
  (0xFD90 ≤ v && v ≤ 0xFD91) ||
  (0xFDC8 ≤ v && v ≤ 0xFDCF) ||
  (0xFDFC ≤ v && v ≤ 0xFDFF) ||
  -- Vertical Forms
  (0xFE10 ≤ v && v ≤ 0xFE19) ||
  -- CJK Compatibility Forms
  (0xFE30 ≤ v && v ≤ 0xFE4F) ||
  -- Small Form Variants
  (0xFE50 ≤ v && v ≤ 0xFE52) ||
  (0xFE54 ≤ v && v ≤ 0xFE66) ||
  (0xFE68 ≤ v && v ≤ 0xFE6B) ||
  -- Halfwidth and Fullwidth Forms
  (0xFF01 ≤ v && v ≤ 0xFF0F)

def punctuation_A92E_FF0F (v : UInt32) : Bool :=
  if v < 0xFB29 then punctuation_A92E_ABEB v else punctuation_FB29_FF0F v

def punctuation_FF1A_101A0 (v : UInt32) : Bool :=
  -- Halfwidth and Fullwidth Forms
  (0xFF1A ≤ v && v ≤ 0xFF20) ||
  (0xFF3B ≤ v && v ≤ 0xFF40) ||
  (0xFF5B ≤ v && v ≤ 0xFF65) ||
  (0xFFE0 ≤ v && v ≤ 0xFFE6) ||
  (0xFFE8 ≤ v && v ≤ 0xFFEE) ||
  -- Specials
  (0xFFFC ≤ v && v ≤ 0xFFFD) ||
  -- Aegean Numbers
  (0x10100 ≤ v && v ≤ 0x10102) ||
  (0x10137 ≤ v && v ≤ 0x1013F) ||
  -- Ancient Greek Numbers
  (0x10179 ≤ v && v ≤ 0x10189) ||
  (0x1018C ≤ v && v ≤ 0x1018E) ||
  -- Ancient Symbols
  (0x10190 ≤ v && v ≤ 0x1019C) ||
  v == 0x101A0

def punctuation_101D0_10AF6 (v : UInt32) : Bool :=
  -- Phaistos Disc
  (0x101D0 ≤ v && v ≤ 0x101FC) ||
  -- Ugaritic
  v == 0x1039F ||
  -- Old Persian
  v == 0x103D0 ||
  -- Caucasian Albanian
  v == 0x1056F ||
  -- Imperial Aramaic
  v == 0x10857 ||
  -- Palmyrene
  (0x10877 ≤ v && v ≤ 0x10878) ||
  -- Phoenician
  v == 0x1091F ||
  -- Lydian
  v == 0x1093F ||
  -- Kharoshthi
  (0x10A50 ≤ v && v ≤ 0x10A58) ||
  -- Old South Arabian
  v == 0x10A7F ||
  -- Manichaean
  v == 0x10AC8 ||
  (0x10AF0 ≤ v && v ≤ 0x10AF6)

def punctuation_FF1A_10AF6 (v : UInt32) : Bool :=
  if v < 0x101D0 then punctuation_FF1A_101A0 v else punctuation_101D0_10AF6 v

def punctuation_A92E_10AF6 (v : UInt32) : Bool :=
  if v < 0xFF1A then punctuation_A92E_FF0F v else punctuation_FF1A_10AF6 v

def punctuation_10B39_110C1 (v : UInt32) : Bool :=
  -- Avestan
  (0x10B39 ≤ v && v ≤ 0x10B3F) ||
  -- Psalter Pahlavi
  (0x10B99 ≤ v && v ≤ 0x10B9C) ||
  -- Garay
  v == 0x10D6E ||
  (0x10D8E ≤ v && v ≤ 0x10D8F) ||
  -- Yezidi
  v == 0x10EAD ||
  -- Arabic Extended-C
  (0x10EC9 ≤ v && v ≤ 0x10ECA) ||
  (0x10ED0 ≤ v && v ≤ 0x10ED8) ||
  -- Sogdian
  (0x10F55 ≤ v && v ≤ 0x10F59) ||
  -- Old Uyghur
  (0x10F86 ≤ v && v ≤ 0x10F89) ||
  -- Brahmi
  (0x11047 ≤ v && v ≤ 0x1104D) ||
  -- Kaithi
  (0x110BB ≤ v && v ≤ 0x110BC) ||
  (0x110BE ≤ v && v ≤ 0x110C1)

def punctuation_11140_1145B (v : UInt32) : Bool :=
  -- Chakma
  (0x11140 ≤ v && v ≤ 0x11143) ||
  -- Mahajani
  (0x11174 ≤ v && v ≤ 0x11175) ||
  -- Sharada
  (0x111C5 ≤ v && v ≤ 0x111C8) ||
  v == 0x111CD ||
  v == 0x111DB ||
  (0x111DD ≤ v && v ≤ 0x111DF) ||
  -- Khojki
  (0x11238 ≤ v && v ≤ 0x1123D) ||
  -- Multani
  v == 0x112A9 ||
  -- Tulu-Tigalari
  (0x113D4 ≤ v && v ≤ 0x113D5) ||
  (0x113D7 ≤ v && v ≤ 0x113D8) ||
  -- Newa
  (0x1144B ≤ v && v ≤ 0x1144F) ||
  (0x1145A ≤ v && v ≤ 0x1145B)

def punctuation_10B39_1145B (v : UInt32) : Bool :=
  if v < 0x11140 then punctuation_10B39_110C1 v else punctuation_11140_1145B v

def punctuation_1145D_11A9C (v : UInt32) : Bool :=
  -- Newa
  v == 0x1145D ||
  -- Tirhuta
  v == 0x114C6 ||
  -- Siddham
  (0x115C1 ≤ v && v ≤ 0x115D7) ||
  -- Modi
  (0x11641 ≤ v && v ≤ 0x11643) ||
  -- Mongolian Supplement
  (0x11660 ≤ v && v ≤ 0x1166C) ||
  -- Takri
  v == 0x116B9 ||
  -- Ahom
  (0x1173C ≤ v && v ≤ 0x1173F) ||
  -- Dogra
  v == 0x1183B ||
  -- Dives Akuru
  (0x11944 ≤ v && v ≤ 0x11946) ||
  -- Nandinagari
  v == 0x119E2 ||
  -- Zanabazar Square
  (0x11A3F ≤ v && v ≤ 0x11A46) ||
  -- Soyombo
  (0x11A9A ≤ v && v ≤ 0x11A9C)

def punctuation_11A9E_16A6F (v : UInt32) : Bool :=
  -- Soyombo
  (0x11A9E ≤ v && v ≤ 0x11AA2) ||
  -- Devanagari Extended-A
  (0x11B00 ≤ v && v ≤ 0x11B09) ||
  -- Sunuwar
  v == 0x11BE1 ||
  -- Bhaiksuki
  (0x11C41 ≤ v && v ≤ 0x11C45) ||
  -- Marchen
  (0x11C70 ≤ v && v ≤ 0x11C71) ||
  -- Makasar
  (0x11EF7 ≤ v && v ≤ 0x11EF8) ||
  -- Kawi
  (0x11F43 ≤ v && v ≤ 0x11F4F) ||
  -- Tamil Supplement
  (0x11FD5 ≤ v && v ≤ 0x11FF1) ||
  v == 0x11FFF ||
  -- Cuneiform Numbers and Punctuation
  (0x12470 ≤ v && v ≤ 0x12474) ||
  -- Cypro-Minoan
  (0x12FF1 ≤ v && v ≤ 0x12FF2) ||
  -- Mro
  (0x16A6E ≤ v && v ≤ 0x16A6F)

def punctuation_1145D_16A6F (v : UInt32) : Bool :=
  if v < 0x11A9E then punctuation_1145D_11A9C v else punctuation_11A9E_16A6F v

def punctuation_10B39_16A6F (v : UInt32) : Bool :=
  if v < 0x1145D then punctuation_10B39_1145B v else punctuation_1145D_16A6F v

def punctuation_A92E_16A6F (v : UInt32) : Bool :=
  if v < 0x10B39 then punctuation_A92E_10AF6 v else punctuation_10B39_16A6F v

def punctuation_16AF5_1CEBF (v : UInt32) : Bool :=
  -- Bassa Vah
  v == 0x16AF5 ||
  -- Pahawh Hmong
  (0x16B37 ≤ v && v ≤ 0x16B3F) ||
  (0x16B44 ≤ v && v ≤ 0x16B45) ||
  -- Kirat Rai
  (0x16D6D ≤ v && v ≤ 0x16D6F) ||
  -- Medefaidrin
  (0x16E97 ≤ v && v ≤ 0x16E9A) ||
  -- Ideographic Symbols and Punctuation
  v == 0x16FE2 ||
  -- Duployan
  v == 0x1BC9C ||
  v == 0x1BC9F ||
  -- Symbols for Legacy Computing Supplement
  (0x1CC00 ≤ v && v ≤ 0x1CCEF) ||
  (0x1CCFA ≤ v && v ≤ 0x1CCFC) ||
  (0x1CD00 ≤ v && v ≤ 0x1CEB3) ||
  (0x1CEBA ≤ v && v ≤ 0x1CEBF)

def punctuation_1CEC0_1D241 (v : UInt32) : Bool :=
  -- Miscellaneous Symbols Supplement
  (0x1CEC0 ≤ v && v ≤ 0x1CED0) ||
  (0x1CED2 ≤ v && v ≤ 0x1CED4) ||
  (0x1CEDD ≤ v && v ≤ 0x1CEFD) ||
  -- Znamenny Musical Notation
  (0x1CF50 ≤ v && v ≤ 0x1CFC3) ||
  -- Byzantine Musical Symbols
  (0x1D000 ≤ v && v ≤ 0x1D0F5) ||
  -- Musical Symbols
  (0x1D100 ≤ v && v ≤ 0x1D126) ||
  (0x1D129 ≤ v && v ≤ 0x1D164) ||
  (0x1D16A ≤ v && v ≤ 0x1D16C) ||
  (0x1D183 ≤ v && v ≤ 0x1D184) ||
  (0x1D18C ≤ v && v ≤ 0x1D1A9) ||
  (0x1D1AE ≤ v && v ≤ 0x1D1FF) ||
  -- Ancient Greek Musical Notation
  (0x1D200 ≤ v && v ≤ 0x1D241)

def punctuation_16AF5_1D241 (v : UInt32) : Bool :=
  if v < 0x1CEC0 then punctuation_16AF5_1CEBF v else punctuation_1CEC0_1D241 v

def punctuation_1D245_1D76F (v : UInt32) : Bool :=
  -- Ancient Greek Musical Notation
  v == 0x1D245 ||
  -- Musical Symbols Supplement
  (0x1D253 ≤ v && v ≤ 0x1D25A) ||
  (0x1D25D ≤ v && v ≤ 0x1D25E) ||
  (0x1D260 ≤ v && v ≤ 0x1D27F) ||
  -- Tai Xuan Jing Symbols
  (0x1D300 ≤ v && v ≤ 0x1D356) ||
  -- Mathematical Alphanumeric Symbols
  v == 0x1D6C1 ||
  v == 0x1D6DB ||
  v == 0x1D6FB ||
  v == 0x1D715 ||
  v == 0x1D735 ||
  v == 0x1D74F ||
  v == 0x1D76F

def punctuation_1D789_1E5FF (v : UInt32) : Bool :=
  -- Mathematical Alphanumeric Symbols
  v == 0x1D789 ||
  v == 0x1D7A9 ||
  v == 0x1D7C3 ||
  -- Sutton SignWriting
  (0x1D800 ≤ v && v ≤ 0x1D9FF) ||
  (0x1DA37 ≤ v && v ≤ 0x1DA3A) ||
  (0x1DA6D ≤ v && v ≤ 0x1DA74) ||
  (0x1DA76 ≤ v && v ≤ 0x1DA83) ||
  (0x1DA85 ≤ v && v ≤ 0x1DA8B) ||
  -- Miscellaneous Symbols and Arrows Extended
  (0x1DB00 ≤ v && v ≤ 0x1DB1C) ||
  -- Nyiakeng Puachue Hmong
  v == 0x1E14F ||
  -- Wancho
  v == 0x1E2FF ||
  -- Ol Onal
  v == 0x1E5FF

def punctuation_1D245_1E5FF (v : UInt32) : Bool :=
  if v < 0x1D789 then punctuation_1D245_1D76F v else punctuation_1D789_1E5FF v

def punctuation_16AF5_1E5FF (v : UInt32) : Bool :=
  if v < 0x1D245 then punctuation_16AF5_1D241 v else punctuation_1D245_1E5FF v

def punctuation_1E95E_1F1AE (v : UInt32) : Bool :=
  -- Adlam
  (0x1E95E ≤ v && v ≤ 0x1E95F) ||
  -- Indic Siyaq Numbers
  v == 0x1ECAC ||
  v == 0x1ECB0 ||
  -- Ottoman Siyaq Numbers
  v == 0x1ED2E ||
  -- Arabic Mathematical Alphabetic Symbols
  (0x1EEF0 ≤ v && v ≤ 0x1EEF1) ||
  -- Mahjong Tiles
  (0x1F000 ≤ v && v ≤ 0x1F02B) ||
  -- Domino Tiles
  (0x1F030 ≤ v && v ≤ 0x1F093) ||
  -- Playing Cards
  (0x1F0A0 ≤ v && v ≤ 0x1F0AE) ||
  (0x1F0B1 ≤ v && v ≤ 0x1F0BF) ||
  (0x1F0C1 ≤ v && v ≤ 0x1F0CF) ||
  (0x1F0D1 ≤ v && v ≤ 0x1F0F5) ||
  -- Enclosed Alphanumeric Supplement
  (0x1F10D ≤ v && v ≤ 0x1F1AE)

def punctuation_1F1E6_1F6FC (v : UInt32) : Bool :=
  -- Enclosed Alphanumeric Supplement
  (0x1F1E6 ≤ v && v ≤ 0x1F1FF) ||
  -- Enclosed Ideographic Supplement
  (0x1F200 ≤ v && v ≤ 0x1F202) ||
  (0x1F210 ≤ v && v ≤ 0x1F23B) ||
  (0x1F240 ≤ v && v ≤ 0x1F248) ||
  (0x1F250 ≤ v && v ≤ 0x1F251) ||
  (0x1F260 ≤ v && v ≤ 0x1F265) ||
  -- Miscellaneous Symbols and Pictographs
  (0x1F300 ≤ v && v ≤ 0x1F5FF) ||
  -- Emoticons
  (0x1F600 ≤ v && v ≤ 0x1F64F) ||
  -- Ornamental Dingbats
  (0x1F650 ≤ v && v ≤ 0x1F67F) ||
  -- Transport and Map Symbols
  (0x1F680 ≤ v && v ≤ 0x1F6D9) ||
  (0x1F6DC ≤ v && v ≤ 0x1F6EC) ||
  (0x1F6F0 ≤ v && v ≤ 0x1F6FC)

def punctuation_1E95E_1F6FC (v : UInt32) : Bool :=
  if v < 0x1F1E6 then punctuation_1E95E_1F1AE v else punctuation_1F1E6_1F6FC v

def punctuation_1F700_1F8D8 (v : UInt32) : Bool :=
  -- Alchemical Symbols
  (0x1F700 ≤ v && v ≤ 0x1F77F) ||
  -- Geometric Shapes Extended
  (0x1F780 ≤ v && v ≤ 0x1F7DB) ||
  (0x1F7E0 ≤ v && v ≤ 0x1F7EB) ||
  (0x1F7F0 ≤ v && v ≤ 0x1F7FF) ||
  -- Supplemental Arrows-C
  (0x1F800 ≤ v && v ≤ 0x1F80B) ||
  (0x1F810 ≤ v && v ≤ 0x1F847) ||
  (0x1F850 ≤ v && v ≤ 0x1F859) ||
  (0x1F860 ≤ v && v ≤ 0x1F887) ||
  (0x1F890 ≤ v && v ≤ 0x1F8AD) ||
  (0x1F8B0 ≤ v && v ≤ 0x1F8BB) ||
  (0x1F8C0 ≤ v && v ≤ 0x1F8C1) ||
  (0x1F8D0 ≤ v && v ≤ 0x1F8D8)

def punctuation_1F900_1FBFA (v : UInt32) : Bool :=
  -- Supplemental Symbols and Pictographs
  (0x1F900 ≤ v && v ≤ 0x1F9FF) ||
  -- Chess Symbols
  (0x1FA00 ≤ v && v ≤ 0x1FA57) ||
  (0x1FA60 ≤ v && v ≤ 0x1FA6D) ||
  -- Symbols and Pictographs Extended-A
  (0x1FA70 ≤ v && v ≤ 0x1FA7C) ||
  (0x1FA80 ≤ v && v ≤ 0x1FAC6) ||
  v == 0x1FAC8 ||
  (0x1FACC ≤ v && v ≤ 0x1FADD) ||
  (0x1FADF ≤ v && v ≤ 0x1FAEB) ||
  (0x1FAEF ≤ v && v ≤ 0x1FAFA) ||
  -- Symbols for Legacy Computing
  (0x1FB00 ≤ v && v ≤ 0x1FB92) ||
  (0x1FB94 ≤ v && v ≤ 0x1FBEF) ||
  v == 0x1FBFA

def punctuation_1F700_1FBFA (v : UInt32) : Bool :=
  if v < 0x1F900 then punctuation_1F700_1F8D8 v else punctuation_1F900_1FBFA v

def punctuation_1E95E_1FBFA (v : UInt32) : Bool :=
  if v < 0x1F700 then punctuation_1E95E_1F6FC v else punctuation_1F700_1FBFA v

def punctuation_16AF5_1FBFA (v : UInt32) : Bool :=
  if v < 0x1E95E then punctuation_16AF5_1E5FF v else punctuation_1E95E_1FBFA v

def punctuation_A92E_1FBFA (v : UInt32) : Bool :=
  if v < 0x16AF5 then punctuation_A92E_16A6F v else punctuation_16AF5_1FBFA v

def punctuation_00A1_1FBFA (v : UInt32) : Bool :=
  if v < 0xA92E then punctuation_00A1_A8FC v else punctuation_A92E_1FBFA v

/--
Whether {name}`c` is Unicode punctuation in the sense of CommonMark: a character of the {lit}`P`
(punctuation) or {lit}`S` (symbol) general categories, per Unicode 18.0.0. This includes the ASCII
punctuation, the mathematical operators and arrows, currency signs, and emoji, and it excludes
letters, digits, whitespace, and combining marks.
-/
public def isUnicodePunctuation (c : Char) : Bool :=
  let v := c.val
  if v < 0x80 then
    -- Basic Latin
    (0x0021 ≤ v && v ≤ 0x002F) || (0x003A ≤ v && v ≤ 0x0040) ||
    (0x005B ≤ v && v ≤ 0x0060) || (0x007B ≤ v && v ≤ 0x007E)
  else
    punctuation_00A1_1FBFA v

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
