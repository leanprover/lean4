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
variables {m : Type → Type} {μ : Type} [monad m] [monad_parsec μ m] [alternative m] [inhabited μ]

def parse_hex_digit : m nat :=
(    (do d ← digit, pure $ d.val - '0'.val)
 <|> (do c ← satisfy (λ c, 'a'.val ≤ c.val && c.val ≤ 'f'.val), pure $ 10 + (c.val - 'a'.val))
 <|> (do c ← satisfy (λ c, 'A'.val ≤ c.val && c.val ≤ 'F'.val), pure $ 10 + (c.val - 'A'.val)))
<?> "hexadecimal"

def parse_quoted_char : m char :=
do it ← left_over,
   c ← any,
   if c = '\\'      then pure '\\'
   else if c = '\"' then pure '\"'
   else if c = '\'' then pure '\''
   else if c = '\n' then pure '\n'
   else if c = '\t' then pure '\t'
   else if c = 'x'  then do {
     d₁ ← parse_hex_digit,
     d₂ ← parse_hex_digit,
     pure $ char.of_nat (16*d₁ + d₂) }
   else if c = 'u'  then do {
     d₁ ← parse_hex_digit,
     d₂ ← parse_hex_digit,
     d₃ ← parse_hex_digit,
     d₄ ← parse_hex_digit,
     pure $ char.of_nat (16*(16*(16*d₁ + d₂) + d₃) + d₄) }
   else unexpected_at "quoted character" it

def parse_string_literal_aux : nat → string → m string
| 0     s := ch '\"' *> pure s
| (n+1) s := do
  c ← any,
  if c = '\\' then do c ← parse_quoted_char, parse_string_literal_aux n (s.push c)
  else if c = '\"' then pure s
  else parse_string_literal_aux n (s.push c)

def parse_string_literal : m string :=
do ch '\"',
   r ← remaining,
   parse_string_literal_aux r ""

end parser
end lean
