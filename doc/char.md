# Characters

A value of type `Char`, also known as a character, is a [Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value). It is represented using an unsigned 32-bit integer and is statically guaranteed to be a valid Unicode scalar value.

Syntactically, character literals are enclosed in single quotes.
```lean
#eval 'a' -- 'a'
#eval '∀' -- '∀'
```

Characters are ordered and can be decidably compared using the relational operators `=`, `<`, `≤`, `>`, `≥`.

The `unicodeVersion` definition gives Lean's current version of Unicode.

New versions of Unicode are released regularly and subsequently all methods in the standard library depending on Unicode are updated. Therefore the behavior of some char and str methods and the value of this constant changes over time. *This is not considered to be a breaking change.*
