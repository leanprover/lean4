/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.parser.parsec

namespace lean
namespace parser
open monad_parsec

def parse_hex_digit : parsec nat :=
(    (do d ← digit, return $ d.val - '0'.val)
 <|> (do c ← satisfy (λ c, 'a'.val ≤ c.val && c.val ≤ 'f'.val), return $ 10 + (c.val - 'a'.val))
 <|> (do c ← satisfy (λ c, 'A'.val ≤ c.val && c.val ≤ 'F'.val), return $ 10 + (c.val - 'A'.val)))
<?> "hexadecimal"

def parse_quoted_char : parsec char :=
do p ← pos,
   c ← any,
   if c = '\\'      then return '\\'
   else if c = '\"' then return '\"'
   else if c = '\'' then return '\''
   else if c = '\n' then return '\n'
   else if c = '\t' then return '\t'
   else if c = 'x'  then do {
     d₁ ← parse_hex_digit,
     d₂ ← parse_hex_digit,
     return $ char.of_nat (16*d₁ + d₂) }
   else if c = 'u'  then do {
     d₁ ← parse_hex_digit,
     d₂ ← parse_hex_digit,
     d₃ ← parse_hex_digit,
     d₄ ← parse_hex_digit,
     return $ char.of_nat (16*(16*(16*d₁ + d₂) + d₃) + d₄) }
   else unexpected_at "quoted character" p

def parse_string_literal_aux : nat → string → parsec string
| 0     s := ch '\"' >> return s
| (n+1) s := do
  c ← any,
  if c = '\\' then do c ← parse_quoted_char, parse_string_literal_aux n (s.push c)
  else if c = '\"' then return s
  else parse_string_literal_aux n (s.push c)

def parse_string_literal : parsec string :=
do ch '\"',
   r ← remaining,
   parse_string_literal_aux r ""

end parser
end lean
