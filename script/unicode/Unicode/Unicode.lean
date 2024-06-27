/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

inductive Letter where
  | Lu -- uppercase
  | Ll -- lowercase
  | Lt -- titlecase
  | Lm -- modifier
  | Lo -- other
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive Mark where
  | Mn -- nonspacing
  | Mc -- spacing combining
  | Me -- enclosing
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive Number where
  | Nd -- decimal digit
  | Nl -- letter
  | No -- other
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive Punctuation where
  | Pc -- connector
  | Pd -- dash
  | Ps -- open
  | Pe -- close
  | Pi -- initial quote
  | Pf -- final quote
  | Po -- other
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive Symbol where
  | Sm -- math
  | Sc -- currency
  | Sk -- modifier
  | So -- other
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive Separator where
  | Zs -- space
  | Zl -- line
  | Zp -- paragraph
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive Other where
  | Cc -- control
  | Cf -- format
  | Cs -- surrogate
  | Co -- private use
  | Cn -- not assigned
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive GeneralCategory where
  | Letter (minor : Letter)
  | Mark (minor : Mark)
  | Number (minor : Number)
  | Punctuation (minor : Punctuation)
  | Symbol (minor : Symbol)
  | Separator (minor : Separator)
  | Other (minor : Other)
  deriving Repr, DecidableEq, Inhabited, Nonempty

inductive BidiClass where
  | AL  -- Arabic Letter
  | AN  -- Arabic Number
  | B   -- Paragraph Separator
  | BN  -- Boundary Neutral
  | CS  -- Common Separator
  | EN  -- European Number
  | ES  -- European Separator
  | ET  -- European Terminator
  | FSI -- First Strong Isolate
  | L   -- Left To Right
  | LRE -- Left To Right Embedding
  | LRI -- Left To Right Isolate
  | LRO -- Left To Right Override
  | NSM -- Nonspacing Mark
  | ON  -- Other Neutral
  | PDF -- Pop Directional Format
  | PDI -- Pop Directional Isolate
  | R   -- Right To Left
  | RLE -- Right To Left Embedding
  | RLI -- Right To Left Isolate
  | RLO -- Right To Left Override
  | S   -- Segment Separator
  | WS  -- White Space

structure UnicodeData where
  codepointRaw : String
  codepoint : Nat
  gc : GeneralCategory
  deriving Repr, DecidableEq, Inhabited, Nonempty
