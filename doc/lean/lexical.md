# Lexical conventions

## Reserved keywords

This is the list of reserved keywords in Lean:
`axiom`,
`check`,
`coercion`,
`definition`,
`echo`,
`environment`,
`eval`,
`exit`,
`have`,
`help`,
`import`,
`infix`,
`infixr`,
`infixl`,
`notation`,
`options`,
`pi`,
`pop::context`,
`print`,
`scope`,
`theorem`,
`type`,
`universe`,
`variable`,
`variables`,
`by`,
`exists`,
`forall`,
`fun`,
`in`,
`let`

Remark: Lean commands always start with a upper case letter.

The following symbols are also reserved: `->`, `==`, `Π`, `λ`, `→`, `∀`, `∃`, `_`, `,`, `.`, `:`, `(`, `)`, `{`, `}`

## Identifiers

Lean identifiers are divided in 3 categories.

In the first category, identifiers are of the form `[a-zA-Z_'@][a-zA-Z0-9_'@]*`. Here are examples of valid identifiers in this category: `fact`, `sin`, `move_front`, `f1`, `@cast`, and `A'`.

In Lean, we support hierarchical identifiers. A hierarchical is essentially a sequence of category 1 identifiers separated by `::`. We use hierarchical names to simulate modules in Lean. Here are some examples: `mod::x`, `foo::bla::1`.

In the second category, we have any non empty sequence of the following characters: `=`, `<`, `>`, `^`, `|`, `&`, `~`, `+`, `-`, `*`, `/`, `\\`, `$`, `%`, `?`, `;`, `[`, `]`, `#`. Here are examples of indentifiers in this category: `==`, `++`, `<<==`.

In the third category, we have any non empty sequence of non-ascii characters. Here are some examples: `⊆`, `∨`, and `¬`.

This separation may seem adhoc, the main motivation is to minimize the number of white spaces in Lean files.
For example, we can write `x+y*z` instead of `x + y * z`.

We usually use category 1 identifiers to name variable declarations,
definitions, axioms and theorems. Category 2 and 3 are usually used to
define notation, i.e., symbolic abbreviations denoting terms. For
example, the integer addition is named `Int::add`, and real addition
`Real::add`.  The symbol `+` is notation for both of them.

## Numerals

Natural numbers are of the form `[0-9]+`, and decimal numbers are of the form `[0-9]+.[0-9]*`.
Natural numbers have type Nat, and decimal numbers have type Real. Lean automatically introduce coercions when needed.

## Strings

Strings are defined as usual as `"[any sequence of characters excluded "]"`.

## Comments

A comment starts anywhere with a double hyphen `--` and runs until the of the line.
