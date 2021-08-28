Lexical Structure
=================

This section describes the detailed lexical structure of the Lean
language. Many readers will want to skip this section on a first
reading.

Lean input is processed into a stream of tokens by its scanner, using
the UTF-8 encoding. The next token is the longest matching prefix of
the remaining input.

```
   token: `symbol` | `command` | `ident` | `string` | `char` | `numeral` |
        : `decimal` | `quoted_symbol` | `doc_comment` | `mod_doc_comment` |
        : `field_notation`
```

Tokens can be separated by the whitespace characters space, tab, line
feed, and carriage return, as well as comments. Single-line comments
start with ``--``, whereas multi-line comments are enclosed by ``/-``
and ``-/`` and can be nested.

Symbols and Commands
====================

.. *(TODO: list built-in symbols and command tokens?)*

Symbols are static tokens that are used in term notations and
commands. They can be both keyword-like (e.g. the :keyword:`have
<structured_proofs>` keyword) or use arbitrary Unicode characters.

Command tokens are static tokens that prefix any top-level declaration
or action. They are usually keyword-like, with transitory commands
like :keyword:`#print <instructions>` prefixed by an additional
``#``. The set of built-in commands is listed in the :numref:`Chapter
%s <other_commands>` section.

Users can dynamically extend the sets of both symbols (via the
commands listed in :numref:`quoted_symbols`) and command tokens (via
the :keyword:`[user_command] <attributes>` attribute).

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
   ident: `atomic_ident` | `ident` "." `atomic_ident`
   atomic_ident: `atomic_ident_start` `atomic_ident_rest`*
   atomic_ident_start: `letterlike` | "_" | `escaped_ident_part`
   letterlike: [a-zA-Z] | `greek` | `coptic` | `letterlike_symbols`
   greek: <[α-ωΑ-Ωἀ-῾] except for [λΠΣ]>
   coptic: [ϊ-ϻ]
   letterlike_symbols: [℀-⅏]
   escaped_ident_part: "«" [^«»\r\n\t]* "»"
   atomic_ident_rest: `atomic_ident_start` | [0-9'ⁿ] | `subscript`
   subscript: [₀-₉ₐ-ₜᵢ-ᵪ]
```

String Literals
===============

String literals are enclosed by double quotes (``"``). They may contain line breaks, which are conserved in the string value.

```
   string       : '"' `string_item` '"'
   string_item  : `string_char` | `string_escape`
   string_char  : [^\\]
   string_escape: "\" ("\" | '"' | "'" | "n" | "t" | "x" `hex_char` `hex_char`)
   hex_char     : [0-9a-fA-F]
```

Char Literals
=============

Char literals are enclosed by single quotes (``'``).

```
   char: "'" `string_item` "'"
```

Numeric Literals
================

Numeric literals can be specified in various bases.

```
   numeral    : `numeral10` | `numeral2` | `numeral8` | `numeral16`
   numeral10  : [0-9]+
   numeral2   : "0" [bB] [0-1]+
   numeral8   : "0" [oO] [0-7]+
   numeral16  : "0" [xX] `hex_char`+
```

Decimal literals are currently only being used for some :keyword:`set_option <options>` values.


```
   decimal    : [0-9]+ "." [0-9]+
```

Quoted Symbols
==============

In a fixed set of commands (:keyword:`notation
<notation_declarations>`, :keyword:`local notation
<notation_declarations>`, and :keyword:`reserve
<notation_declarations>`), symbols (known or unknown) can be quoted by
enclosing them in backticks (`````). Quoted symbols are used by these
commands for registering new notations and symbols.

```
   quoted_symbol      : "`" " "* `quoted_symbol_start` `quoted_symbol_rest`* " "* "`"
   quoted_symbol_start: [^0-9"\n\t `]
   quoted_symbol_rest : [^"\n\t `]
```

A quoted symbol may contain surrounding whitespace, which is
customarily used for pretty printing the symbol and ignored while
scanning.

While backticks are not allowed in a user-defined symbol, they are
used in some built-in symbols (see :ref:`quotations`), which are
accessible outside of the set of commands noted above.

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
:ref:`identifier <identifiers>`, but may be interpreted as a field
notation expression by the parser.

```
   field_notation: "." ([0-9]+ | `atomic_ident`)
```
