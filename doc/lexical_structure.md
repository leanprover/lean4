Lexical Structure
=================

This section describes the detailed lexical structure of the Lean
language.

A Lean program consists of a stream of UTF-8 tokens where each token
is one of the following:

```
   token: symbol | command | ident | string | raw_string | char | numeral |
        : decimal | doc_comment | mod_doc_comment | field_notation
```

Tokens can be separated by the whitespace characters space, tab, line
feed, and carriage return, as well as comments. Single-line comments
start with ``--``, whereas multi-line comments are enclosed by ``/-``
and ``-/`` and can be nested.

Symbols and Commands
====================

.. *(TODO: list built-in symbols and command tokens?)*

Symbols are static tokens that are used in term notations and
commands. They can be both keyword-like (e.g. the `have
<structured_proofs>` keyword) or use arbitrary Unicode characters.

Command tokens are static tokens that prefix any top-level declaration
or action. They are usually keyword-like, with transitory commands
like `#print <instructions>` prefixed by the ``#`` character. The set
of built-in commands is listed in [Other Commands](./other_commands.md).

Users can dynamically extend the sets of both symbols (via the
commands listed in [Quoted Symbols](#quoted-symbols) and command
tokens (via the `[user_command] <attributes>` attribute).

.. _identifiers:

Identifiers
===========

An *atomic identifier*, or *atomic name*, is (roughly) an alphanumeric
string that does not begin with a numeral. A (hierarchical)
*identifier*, or *name*, consists of one or more atomic names
separated by periods.

Parts of atomic names can be escaped by enclosing them in pairs of French double quotes ``«»``.

```lean
   def Foo.«bar.baz» := 0  -- name parts ["Foo", "bar.baz"]
```

```
   ident: atomic_ident | ident "." atomic_ident
   atomic_ident: atomic_ident_start atomic_ident_rest*
   atomic_ident_start: letterlike | "_" | escaped_ident_part
   letterlike: [a-zA-Z] | greek | coptic | letterlike_symbols
   greek: <[α-ωΑ-Ωἀ-῾] except for [λΠΣ]>
   coptic: [ϊ-ϻ]
   letterlike_symbols: [℀-⅏]
   escaped_ident_part: "«" [^«»\r\n\t]* "»"
   atomic_ident_rest: atomic_ident_start | [0-9'ⁿ] | subscript
   subscript: [₀-₉ₐ-ₜᵢ-ᵪ]
```

String Literals
===============

String literals are enclosed by double quotes (``"``). They may contain line breaks, which are conserved in the string value.  Backslash (`\`) is a special escape character which can be used to the following
special characters:
- `\\` represents an escaped backslash, so this escape causes one backslash to be included in the string.
- `\"` puts a double quote in the string.
- `\'` puts an apostrophe in the string.
- `\n` puts a new line character in the string.
- `\t` puts a tab character in the string.
- `\xHH` puts the character represented by the 2 digit hexadecimal into the string.  For example
"this \x26 that" which become "this & that".  Values above 0x80 will be interpreted according to the
[Unicode table](https://unicode-table.com/en/) so "\xA9 Copyright 2021" is "© Copyright 2021".
- `\uHHHH` puts the character represented by the 4 digit hexadecimal into the string, so the following
string "\u65e5\u672c" will become "日本" which means "Japan".
- `\` followed by a newline and then any amount of whitespace is a "gap" that is equivalent to the empty string,
useful for letting a string literal span across multiple lines. Gaps spanning multiple lines can be confusing,
so the parser raises an error if the trailing whitespace contains any newlines.

So the complete syntax is:

```
   string       : '"' string_item '"'
   string_item  : string_char | char_escape | string_gap
   string_char  : [^"\\]
   char_escape  : "\" ("\" | '"' | "'" | "n" | "t" | "x" hex_char{2} | "u" hex_char{4})
   hex_char     : [0-9a-fA-F]
   string_gap   : "\" newline whitespace*
```

Raw String Literals
===================

Raw string literals are string literals without any escape character processing.
They begin with `r##...#"` (with zero or more `#` characters) and end with `"#...##` (with the same number of `#` characters).
The contents of a raw string literal may contain `"##..#` so long as the number of `#` characters
is less than the number of `#` characters used to begin the raw string literal.

```
   raw_string          : raw_string_aux(0) | raw_string_aux(1) | raw_string_aux(2) | ...
   raw_string_aux(n)   : 'r' '#'{n} '"' raw_string_item '"' '#'{n}
   raw_string_item(n)  : raw_string_char | raw_string_quote(n)
   raw_string_char     : [^"]
   raw_string_quote(n) : '"' '#'{0..n-1}
```

Char Literals
=============

Char literals are enclosed by single quotes (``'``).

```
   char      : "'" char_item "'"
   char_item : char_char | char_escape
   char_char : [^'\\]
```

Numeric Literals
================

Numeric literals can be specified in various bases.

```
   numeral    : numeral10 | numeral2 | numeral8 | numeral16
   numeral10  : [0-9]+
   numeral2   : "0" [bB] [0-1]+
   numeral8   : "0" [oO] [0-7]+
   numeral16  : "0" [xX] hex_char+
```

Floating point literals are also possible with optional exponent:

```
   float    : [0-9]+ "." [0-9]+ [[eE[+-][0-9]+]
```

For example:

```
constant w : Int := 55
constant x : Nat := 26085
constant y : Nat := 0x65E5
constant z : Float := 2.548123e-05
```

Note: that negative numbers are created by applying the "-" negation prefix operator to the number, for example:

```
constant w : Int := -55
```

Doc Comments
============

A special form of comments, doc comments are used to document modules
and declarations.

```
   doc_comment: "/--" ([^-] | "-" [^/])* "-/"
   mod_doc_comment: "/-!" ([^-] | "-" [^/])* "-/"
```

Field Notation
==============

Trailing field notation tokens are used in expressions such as
``(1+1).to_string``. Note that ``a.toString`` is a single
[Identifier](#identifiers), but may be interpreted as a field
notation expression by the parser.

```
   field_notation: "." ([0-9]+ | atomic_ident)
```
