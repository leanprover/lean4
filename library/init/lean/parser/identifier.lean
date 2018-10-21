/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.char.basic init.lean.parser.parsec

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

namespace parser
variables {m : Type → Type} {μ : Type} [monad m] [monad_parsec μ m] [alternative m]
open monad_parsec

def id_part_default : m string :=
do c ← satisfy is_id_first,
   take_while_cont is_id_rest (to_string c)

def id_part_escaped : m string :=
ch id_begin_escape *> take_until1 is_id_end_escape <* ch id_end_escape

def id_part : m string :=
cond is_id_begin_escape
  id_part_escaped
  id_part_default

def identifier : m name :=
(try $ do s  ← id_part,
       foldl name.mk_string (mk_simple_name s) (ch '.' *> id_part)) <?> "identifier"

def c_identifier : m string :=
(try $ do c ← satisfy (λ c, c.is_alpha || c = '_'),
       take_while_cont (λ c, c.is_alphanum || c = '_') (to_string c)) <?> "C identifier"

def cpp_identifier : m string :=
(try $ do n ← c_identifier,
       ns ← many ((++) <$> str "::" <*> c_identifier),
       pure $ string.join (n::ns)) <?> "C++ identifier"

end parser
end lean
