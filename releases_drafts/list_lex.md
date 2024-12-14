We rename the inductive predicate `Lex.lt` to `List.Lex'`
(simultaneously generalizing it to take an arbitrary relation, not just `<`),
and upstream `List.Lex` from Mathlib.

`List.Lex'` is a weaker relation: in particular if `l₁ ≤ l₂`, then
`a :: l₁ ≤ b :: l₂` may hold according to `List.Lex'` even if `a` and `b` are merely incomparable
(either neither `a < b` nor `b < a`), whereas according to `List.Lex` this would require `a = b`.

When `<` is total, in the sense that `¬ · < ·` is antisymmetric, then the two relations coincide.

`List.Lex'` has some advantages,
in particular that theorems about it do not require decidable equality.
However, this is mostly outweighed by the confusing behaviour that occurs
when `<` is not total.

For now, we leave the define of lexicographic ordering on `List α` in terms of `List.Lex'`,
but with theorems relating the definitions in terms of `List.Lex'` and `List.Lex`.
We intend to later deprecate `List.Lex'` and only use `List.Lex`, thereby changing the definition
of lexicographic ordering on `List α`.

Note that Mathlib already overrides the order instances
for `List α`, so this change should not be noticed by anyone already using Mathlib.
