/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Char.Basic

namespace Lean

def isGreek (c : Char) : Bool :=
0x391 ≤ c.val && c.val ≤ 0x3dd

def isLetterLike (c : Char) : Bool :=
(0x3b1  ≤ c.val && c.val ≤ 0x3c9 && c.val ≠ 0x3bb) ||                  -- Lower greek, but lambda
(0x391  ≤ c.val && c.val ≤ 0x3A9 && c.val ≠ 0x3A0 && c.val ≠ 0x3A3) || -- Upper greek, but Pi and Sigma
(0x3ca  ≤ c.val && c.val ≤ 0x3fb) ||                                   -- Coptic letters
(0x1f00 ≤ c.val && c.val ≤ 0x1ffe) ||                                  -- Polytonic Greek Extended Character Set
(0x2100 ≤ c.val && c.val ≤ 0x214f) ||                                  -- Letter like block
(0x1d49c ≤ c.val && c.val ≤ 0x1d59f)                                   -- Latin letters, Script, Double-struck, Fractur

def isSubScriptAlnum (c : Char) : Bool :=
(0x2080 ≤ c.val && c.val ≤ 0x2089) || -- numeric subscripts
(0x2090 ≤ c.val && c.val ≤ 0x209c) ||
(0x1d62 ≤ c.val && c.val ≤ 0x1d6a)

def isIdFirst (c : Char) : Bool :=
c.isAlpha || c = '_' || isLetterLike c

def isIdRest (c : Char) : Bool :=
c.isAlphanum || c = '_' || c = '\'' || c == '!' || c == '?' || isLetterLike c || isSubScriptAlnum c

def idBeginEscape := '«'
def idEndEscape   := '»'
def isIdBeginEscape (c : Char) : Bool :=
c = idBeginEscape
def isIdEndEscape (c : Char) : Bool :=
c = idEndEscape

end Lean
