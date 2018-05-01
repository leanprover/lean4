/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.char.basic

namespace lean

def is_greek (c : char) : bool :=
0x391 ≤ c.val && c.val ≤ 0x3dd

def is_letter_like (c : char) : bool :=
(0x3b1  ≤ c.val && c.val ≤ 0x3c9 && c.val ≠ 0x3bb) ||                  -- Lower greek, but lambda
(0x391  ≤ c.val && c.val ≤ 0x3A9 && c.val ≠ 0x3A0 && c.val ≠ 0x3A3) || -- Upper greek, but Pi and Sigma
(0x3ca  ≤ c.val && c.val ≤ 0x3fb) ||                                   -- Coptic letters
(0x1f00 ≤ c.val && c.val ≤ 0x1ffe) ||                                  -- Polytonic Greek Extended Character Set
(0x2100 ≤ c.val && c.val ≤ 0x214f) ||                                  -- Letter like block
(0x1d49c ≤ c.val && c.val ≤ 0x1d59f)                                   -- Latin letters, Script, Double-struck, Fractur

def is_sub_script_alnum (c : char) : bool :=
(0x207f ≤ c.val && c.val ≤ 0x2089) || -- n superscript and numberic subscripts
(0x2090 ≤ c.val && c.val ≤ 0x209c) ||
(0x1d62 ≤ c.val && c.val ≤ 0x1d6a)

def is_id_first (c : char) : bool :=
c.is_alpha || c = '_' || is_letter_like c

def is_id_rest (c : char) : bool :=
c.is_alphanum || c = '_' || c = '\'' || is_letter_like c || is_sub_script_alnum c

def id_begin_escape := '«'
def id_end_escape   := '»'
def is_id_begin_escape (c : char) : bool :=
c = id_begin_escape
def is_id_end_escape (c : char) : bool :=
c = id_end_escape

end lean
