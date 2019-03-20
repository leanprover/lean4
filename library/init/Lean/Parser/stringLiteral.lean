/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.parser.parsec

namespace Lean
namespace Parser
open MonadParsec
variables {m : Type → Type} {μ : Type} [Monad m] [MonadParsec μ m] [Alternative m]

def parseHexDigit : m Nat :=
(    (do d ← digit, pure $ d.toNat - '0'.toNat)
 <|> (do c ← satisfy (λ c, 'a'.val ≤ c.val && c.val ≤ 'f'.val), pure $ 10 + (c.toNat - 'a'.toNat))
 <|> (do c ← satisfy (λ c, 'A'.val ≤ c.val && c.val ≤ 'F'.val), pure $ 10 + (c.toNat - 'A'.toNat)))
<?> "hexadecimal"

def parseQuotedChar : m Char :=
do it ← leftOver,
   c ← any,
   if c = '\\'      then pure '\\'
   else if c = '\"' then pure '\"'
   else if c = '\'' then pure '\''
   else if c = 'n' then pure '\n'
   else if c = 't' then pure '\t'
   else if c = 'x'  then do {
     d₁ ← parseHexDigit,
     d₂ ← parseHexDigit,
     pure $ Char.ofNat (16*d₁ + d₂) }
   else if c = 'u'  then do {
     d₁ ← parseHexDigit,
     d₂ ← parseHexDigit,
     d₃ ← parseHexDigit,
     d₄ ← parseHexDigit,
     pure $ Char.ofNat (16*(16*(16*d₁ + d₂) + d₃) + d₄) }
   else unexpectedAt "quoted character" it

def parseStringLiteralAux : Nat → String → m String
| 0     s := ch '\"' *> pure s
| (n+1) s := do
  c ← any,
  if c = '\\' then do c ← parseQuotedChar, parseStringLiteralAux n (s.push c)
  else if c = '\"' then pure s
  else parseStringLiteralAux n (s.push c)

def parseStringLiteral : m String :=
do ch '\"',
   r ← remaining,
   parseStringLiteralAux r ""

end Parser
end Lean
