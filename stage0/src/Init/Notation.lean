/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude

infixr:90 " ∘ "  => Function.comp
infixr:35 " × "  => Prod

infixl:65 " + "  => Add.add
infixl:65 " - "  => Sub.sub
infixl:70 " * "  => Mul.mul
infixl:70 " / "  => Div.div
infixl:70 " % "  => Mod.mod
infixl:70 " %ₙ " => ModN.modn
infixr:80 " ^ "  => Pow.pow

infix:50 " ≤ "  => HasLessEq.LessEq
infix:50 " <= " => HasLessEq.LessEq
infix:50 " < "  => HasLess.Less
infix:50 " ≥ "  => GreaterEq
infix:50 " >= " => GreaterEq
infix:50 " > "  => Greater
infix:50 " = "  => Eq
infix:50 " == " => BEq.beq
infix:50 " ~= " => HEq
infix:50 " ≅ "  => HEq

infixr:35 " ∧ "   => And
infixr:35 " /\\ " => And
infixr:30 " ∨   " => Or
infixr:30 " \\/ " => Or

infixl:35 " && " => and
infixl:30 " || " => or

infixl:65 " ++ " => Append.append
infixr:67 " :: " => List.cons

infixr:2   " <|> " => OrElse.orElse
infixr:60  " >> "  => AndThen.andThen
infixl:55  " >>= " => Bind.bind
infixl:60  " <*> " => Seq.seq
infixl:60  " <* "  => SeqLeft.seqLeft
infixr:60  " *> "  => SeqRight.seqRight
infixr:100 " <$> " => Functor.map
