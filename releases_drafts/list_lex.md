We replace the inductive predicate `List.lt` with an upstreamed version of `List.Lex` from Mathlib.
(Previously `Lex.lt` was defined in terms of `<`; now it is generalized to take an arbitrary relation.)
This subtely changes the notion of ordering on `List α`.

`List.lt` was a weaker relation: in particular if `l₁ < l₂`, then
`a :: l₁ < b :: l₂` may hold according to `List.lt` even if `a` and `b` are merely incomparable
(either neither `a < b` nor `b < a`), whereas according to `List.Lex` this would require `a = b`.

When `<` is total, in the sense that `¬ · < ·` is antisymmetric, then the two relations coincide.

Mathlib was already overriding the order instances for `List α`,
so this change should not be noticed by anyone already using Mathlib.

We simultaneously add the boolean valued `List.lex` function, parameterised by a `BEq` typeclass
and an arbitrary `lt` function. This will support the flexibility previously provided for `List.lt`,
via a `==` function which is weaker than strict equality.
