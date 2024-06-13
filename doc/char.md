# Characters

A value of type `Char`, also known as a character, is a [Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value). It is represented using an unsigned 32-bit integer and is statically guaranteed to be a valid Unicode scalar value.

Syntactically, character literals are enclosed in single quotes.
```lean
#eval 'a' -- 'a'
#eval '∀' -- '∀'
```

Characters are ordered and can be decidably compared using the relational operators `=`, `<`, `≤`, `>`, `≥`.
