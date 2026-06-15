# Locating Parsers and Their Syntax Node Kinds

## Finding the parser for a piece of syntax

The syntax node kind passed to `@[builtin_fmt <kind>]` is the full declaration name of
the parser (e.g. `Lean.Parser.Command.export`). To find it:

1. **Search by parser name** if you can guess it:

   ```bash
   grep -rn "def export" src/Lean/Parser/Command.lean
   grep -rn "def structInst\b" src/Lean/Parser/
   ```

2. **Search by a specific token** that occurs in the syntax. Tokens appear as string
   literals in parser definitions, usually with a leading and/or trailing space
   (the space encodes pretty-printer spacing):

   ```bash
   grep -rn '"export "' src/Lean/Parser/
   grep -rn '" deriving"' src/Lean/Parser/
   grep -rn '"grind_pattern"' src/Lean/
   ```

   If a literal search fails, try without the spaces, or search for a rarer token of
   the same syntax (e.g. `=/=` instead of `where`).

Main parser locations:

- `src/Lean/Parser/{Command,Term,Do,Tactic,Attr,Level,Extra,Module}.lean` — core grammar
- `src/Lean/Parser/Term/Basic.lean` etc. — submodules
- `src/Lean/Meta/Tactic/Grind/Parser.lean` — grind-related commands
- `syntax`/`notation`/`macro` declarations elsewhere in `src/` for non-builtin syntax

The kind of a syntax node can also be inspected directly: elaborate an example with
`#check` on a quotation, or `run_cmd` printing `stx.getKind` — but reading the parser
definition is usually faster and you will need it for the match pattern anyway.

For `syntax (name := k)`/`leading_parser` definitions the kind is the declared name, but
`macro`/`notation`/anonymous `syntax` get mangled auto-generated kinds you cannot guess
(`«term∃_,_»`, `«term_×__1»`, `tacticFunext___`, `Lean.«command__Unif_hint____Where_|_-⊢__»`).
For these, printing the kind is the reliable way to get the exact `@[builtin_fmt ...]`
argument — build the syntax in the right category:

```lean
run_cmd Lean.logInfo (toString (← `(tactic| funext x)).raw.getKind)
run_cmd Lean.logInfo (toString (← `(term| (x : Nat) × Nat)).raw.getKind)
```

Caveats when discovering kinds this way:

- **`macro (name := X) "tok" …` has kind `X`** (the declared `name`), *not* a token-derived
  mangled name. So the placeholder `macro (name := mclearMacro) "mclear"` has kind
  `…Tactic.mclearMacro`, even though a *bare* `macro "exfalso"` (no `name`) mangles to
  `…Tactic.tacticExfalso`.
- **`@[builtin_fmt KIND]` validates `KIND` at compile time** — an unknown kind is a hard build
  error (``Invalid `[fmt]` argument: Unknown syntax kind …``), so a wrong guess fails loudly
  rather than silently never firing. Lean on the build. The two attribute forms validate
  differently (`evalFmtAttributeKey` in `FmtM/Attribute.lean`): the `builtin_` forms accept any
  `KIND` that names a declaration in the environment, whereas the plain forms (`@[fmt]`,
  `@[infix_fmt]`, …) require `Parser.isValidSyntaxNodeKind`. The looser builtin check exists
  precisely so that a formatter for a fresh `[builtin*Parser]` can land in the same change as the
  parser: `isValidSyntaxNodeKind` only learns about such a parser in the next stage, but the
  declaration itself is already there. Both forms of the general attribute
  (`@[builtin_fmt]`/`@[fmt]`) additionally accept the three module-level kinds `moduleKind`,
  `cmdsKind` and `headerKind`, which are not parser declarations; the specialized attributes do
  not.
- **Root-namespace kinds are written bare**, e.g. `@[builtin_fmt «term‹_›»]`,
  `@[builtin_fmt «tacticBy_cases_:_»]` (syntax declared outside any `namespace`, like
  `Init/ByCases.lean`). Do **not** prefix them with `_root_.` — the attribute keeps the prefix
  literally and rejects it.

## Which parsers receive their own syntax node kind

Formatters are registered per syntax node kind, so only parsers that produce their own
node can carry their own formatter. Everything else is matched *inside* the parent
formatter's anti-quotation.

Parsers that **do** get their own kind:

- `leading_parser` / `trailing_parser` definitions — the kind is the full declaration
  name (`Lean.Parser.Command.export`).
- Parsers that explicitly wrap in `node k p`, `leadingNode`, `trailingNode` or
  `nodeWithAntiquot`.
- `syntax (name := k) ... : cat`, `notation`, `infixl`/`infixr`/`prefix`/`postfix`,
  `macro` declarations — these produce `ParserDescr`s with (possibly auto-generated)
  kinds. Note: `infixl`/`infixr`/`infix`/`prefix`/`postfix` notations with a `ParserDescr` get an
  infix/prefix/postfix formatter automatically (the fixity and the precedences are read off the
  descriptor); no attribute needed, and no formatter unless the derived one is wrong.

Parsers that do **not** get their own kind:

- Combinators: `optional (...)` produces a null node (match with `$[...]?`),
  `many`/`many1` produce null nodes (match with `$xs*`), `sepBy`/`sepBy1` produce null
  nodes with interleaved separators (match with `$xs,*`).
- Token parsers: `symbol`/string literals produce atoms; `ident`, `num`, `str`, `name`
  produce token nodes with the builtin kinds `` `ident ``, `` `num ``, ... (these
  builtin kinds *can* carry formatters, e.g. `@[builtin_fmt num] ... := fmtRaw`).
- Plain `def p := p₁ <|> p₂` without `node` — no kind of its own; register formatters
  for the kinds of the alternatives instead.
- Parser *categories* (`categoryParser`) — the parsed alternative determines the node.
  A category reference inside a parent parser (e.g. `structInstFieldDecl`) shows up as
  a child node of whatever kind was parsed; the parent formatter just recurses on it
  with `fmt`.

Consequence for formatter structure: a parser definition like

```lean
def optDeclSig := leading_parser many binder >> optional (" : " >> termParser)
```

has its own kind (`optDeclSig`), but the `many`/`optional` parts inside it do not —
your formatter for the *parent* matches them structurally with `$binders*` and
`$[:%$tk $type?:term]?`.
