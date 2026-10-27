# Anti-Quotations in Formatter Syntax Matches

A formatter's syntax match uses quotation patterns against a specific parser:

```lean
| `(Parser.Command.export| export%$exportTk $namespaceId:ident (%$lbTk $exportedIds:ident* )%$rbTk ) => ...
| _ => throw .partialFormatter
```

## Pattern vocabulary

- `tok%$name` — bind a token (atom) to `name`. Bind **every** token; the formatter must
  recurse into tokens with `fmt` so that comments attached to them are preserved.
- `$x:kind` — bind a component with an expected kind annotation.
- `$[...]?` — optional group; bind the contents with `?`-suffixed names
  (`$[:%$typeAscriptionTk? $type?:term]?`). Each name becomes an `Option`.
- `$xs*` / `$xs:kind*` — repetition (null node), yields a `TSyntaxArray`.
- `$xs,*` / `$xs:kind,*` / `$xs;*` — separated repetition, yields a `TSepArray`
  (pass to `fmtTSepArray` to keep the separators).

## Subtleties

**Type all quoted names if possible.** Write `$declId:declId`, `$type?:term`,
`$classes:derivingClass,*` rather than untyped `$x`. This catches mismatches at compile
time and disambiguates the anti-quotation parser. Exceptions where typing is not
possible: bound tokens (`%$name`) and components that are alternatives of several
kinds (e.g. `$[$metaOrNoncomputable?]?` in `fmtDeclWithDeclModifiers`, or
`$tk` matching `structure <|> class` in `fmtStructure`) — leave these untyped.

**One token in the pattern matches all alternative tokens at that position.**
Anti-quotations only match on the `Syntax.node` structure, not on atom contents. When a
parser references multiple tokens in one place, the anti-quotation contains just one of
them and it matches all of them:

- In `inductive`, the parser has `optional (symbol " :=" <|> " where")`; the pattern
  `:=%$sepTk` matches both `:=` and `where` (see `fmtInductive`).
- `fun%$funTk` also matches `λ`; `=>%$arrowTk` also matches `↦` (see `fmtFun`).
- `.%$dotTk` in `cdot` also matches `·` (see `fmtCdot`).

Since the bound token is formatted with `fmt`, the *actual* token from the input is
reproduced — the formatter does not normalize `λ` to `fun`.

**A `keyword%$name` binding can fail to *parse* when `keyword%` is itself a token.** Lean's
lexer is maximal-munch, so if any (possibly unrelated) parser registers a `keyword%`-shaped
token, writing `keyword%$name` lexes that longer token and the `%$` splice is never seen. You get
a confusing `unexpected token 'keyword%'; expected …` even though a neighbouring `other%$tk`
(whose `other%` is not a token) parses fine. Real cases: the term-level `clear% x; e` registers
`clear%`, and the `exact?%` term registers `exact?%`, so `clear%$clearTk` / `exact?%$exactTk`
both fail. Work around it by binding *that one keyword* by index — match it without `%$` and read
`getStxArg! stx 0` — while keeping the rest of the pattern an anti-quotation (see `fmtTacticClear`,
`fmtExact?`).

**A token inside an auto-wrapped sub-node can still be bound inline.** When a parser
references a small `leading_parser` node like `Term.typeSpec` (`leading_parser " : " >> termParser`)
— directly or via `optional typeSpec` / `optType` — you do *not* have to match the sub-node whole
and recurse. Writing the inner shape inline binds the wrapped token fine: `$[:%$tk? $type?:term]?`
matches `optional typeSpec` and binds the `:` even though it lives inside the `typeSpec` node (see
`fmtLetIdDecl`, and the `initialize` optional `$[$id?:ident :%$colonTk? $type?:term ←%$leftArrowTk?]?`).
Mirror the elaborator's own quotation when unsure which inline shape parses.

**Two-stage matching when the anti-quotation parser gets confused.** Inlining a nested
parser's components into one big pattern sometimes confuses the anti-quotation parser.
Match the outer node first, binding the inner node whole, then match the inner node in
a second step (see `fmtStructExplicitBinder`):

```lean
| `(Parser.Command.structExplicitBinder|
    $declModifiers:declModifiers
    (%$lbTk $ids:ident* $signature:optDeclSig $[$tacticOrDefault?]? )%$rbTk) => do
  let `(Parser.Command.optDeclSig| $binders* $[:%$typeAscriptionTk? $type?:term]?) := signature
    | throw .partialFormatter
  ...
```

**`meta def` aliases for parsers not usable in quotations.** Parsers that are functions
(take arguments) cannot be named in a quotation directly. Define an alias and quote against
that. An alias that several modules quote against goes in `FmtM/CommonFormatters.lean` as a
`public meta def` (`explicitBinderF`, `implicitBinderF`, `strictImplicitBinderF`), which
`fmtExplicitBinder` in `Formatters/Lean/Parser/Term/Basic.lean` uses:

```lean
public meta def explicitBinderF := Parser.Term.explicitBinder  -- in `FmtM/CommonFormatters.lean`

@[builtin_fmt Lean.Parser.Term.explicitBinder]
public def fmtExplicitBinder : Fmt := fun
  | `(explicitBinderF| (%$lbTk $ids* ...)%$rbTk) => ...
```

**Nested `$[…]?` groups compound the `Option`.** When the grammar nests one optional inside
another — e.g. `conv`'s `(" in " (occs)? term)?` — a binder in the *inner* optional is wrapped
twice: `occs?` has type `Option (Option (TSyntax \`occs))`, not `Option (TSyntax \`occs)`. Passing
it straight to `fmt?` (which expects `Option Syntax`) is a type error; flatten it first with
`.join`: `fmt? occs?.join` (see `fmtConvTactic` in `Formatters/Init/Conv.lean`). Binders that sit
in only the *outer* group (`inTk?`, `t?` there) are singly-wrapped as usual, so only the
doubly-nested one needs the `.join`.

**Always end with `| _ => throw .partialFormatter`.** This is the safety net when the
grammar evolves: the formatter degrades to `fmtRaw` (input formatting retained) instead
of producing wrong output, and the occurrence is recorded in `partialFormatters` for
diagnosis.

**Use `$[$x]*` group splices for repetitions of `stx` parsers.** The `stx` category
defines its own postfix `*` (`Init/Notation.lean`), so in a pattern over e.g.
`many1 syntaxParser`, a bare `$args*` parses as the `stx*` *syntax* with the antiquot as
its operand — the binding gets type `TSyntax \`stx` and the pattern only matches inputs
that literally use the postfix `*`. Write the explicit group splice instead, which also
works with a kind annotation and nested inside optional groups (see `fmtSyntaxSepBy`):

```lean
| `(Parser.Syntax.paren| (%$lbTk $[$args]* )%$rbTk) => ...
| `(Parser.Command.«macro»| ... $[$args:macroArg]* $tail:macroTail) => ...
| `(Parser.Syntax.sepBy| sepBy(%$lbTk $[$args]* ,%$comma₁Tk $sepStr:str $[,%$comma₂Tk? $[$sepParserArgs?]*]? ...) => ...
```

**`patternIgnore` tokens cannot be bound.** A token wrapped in `patternIgnore` in the
parser (e.g. the `⊢`/`|-` separator of `unif_hint`, declared as
`patternIgnore(atomic("|" noWs "-") <|> "⊢")`) is *omitted* from the anti-quotation: you
do not write it in the pattern (or if you do, e.g. `⊢`, it matches but a `%$name` on it
binds nothing — referencing the name is an "unknown identifier" error). It is still
present in the syntax tree, so read it by index from the matched node and render it with
`fmtAtomic` (see `fmtUnifHint`, which keeps the rest of the command as an anti-quotation but
takes the separator from `stx[7]`). The `patternIgnore(...)` alternation may itself be a
*wrapping node*, so the token can sit one level deeper than the obvious index: `discharger`'s
`patternIgnore(&"discharger" <|> &"disch")` puts the keyword inside a `patternIgnore` node, so
the keyword atom is `stx[1][0][0]` (read with nested `getStxArg!` calls), not `stx[1]` (see
`fmtTacticDischarger`).

**Repetitions guarded by `linebreak` cannot be destructured inline.** A parser like
`calcSteps` (`... withPosition((ppLine linebreak calcStep)*)`) puts a `linebreak` before
each repeated element, so a pattern `$steps:calcStep*` fails to *parse* (the quoted
sample has no real line breaks between elements): you get `unexpected token '$'`. Fall
back to `getStxArg!` / `.getArgs` for the repetition (see `fmtCalcSteps`/`fmtCalc`), even
though the surrounding `calc%$calcTk $steps:calcSteps` still uses an anti-quotation.

**Quotations match against the *parser*, not the pretty form.** When a pattern refuses
to match, read the parser definition and compare the node structure argument by
argument; `getStxArg!` plus manual kind checks is the fallback for nodes the
anti-quotation parser cannot express (see `fmtStructInstLVal`, `fmtLetConfig`).

**Ambiguous notations parse to a `choice` node.** Brackets shared by several parsers
(e.g. `{ ... }` is both set-builder `«term{_}»` and `structInst`) parse to a `choice`
node. `fmt` sends the `choice` node to `fmtChoiceNode`, which formats each alternative with the
formatter of its own kind. Thus your per-kind formatter still receives a node of its kind. When
all alternatives that did not fall back to `fmtRaw` give the same document, `fmtChoiceNode` uses
that document. Otherwise, it uses the alternative that the elaborator picked
(`Elab.ChoiceResolutionInfo`), and fails with `ambiguousChoiceNode` if the elaborator picked none.
A kind-qualified quotation works directly: `` `(«term{_}»| {%$lbTk $elems:term,* }%$rbTk) ``.

**A `(… <|> hygieneInfo)`-style "optional" is not an `optional`.** Some heads, like
`sufficesDecl`'s `(atomic (group (binderIdent >> " : ")) <|> hygieneInfo)`, encode "binder
or nothing" as an *alternation with `hygieneInfo`*, not as `optional`. A `$[…]?` group does
**not** match it, and `$h:binderIdent` is rejected at that position (the parser expects the
`group`/`hygieneInfo` alternation, not a bare `binderIdent`). Match the concrete forms the
way the elaborator's macro does: `$x:ident :` (binder), `_%$x :` (hole binder), and
`$_:hygieneInfo` (no binder) as separate alternatives. Cross-check against the parser's own
macros (`grep` the kind in `src/Lean/Elab`) — they show exactly which quotation forms parse.

**Symbolic infix/postfix notations: use a *bare* quotation, not a kind-qualified one.** For
a notation like `term "..." term` (and the `<...`, `...=`, `...*`, … range variants), a
kind-qualified pattern `` `(Std.«term_..._»| $a:term ...%$opTk $b:term) `` makes the *leading*
`term` operand parse at full term precedence, so it greedily re-enters the same notation and
swallows the operator — you get a confusing `unexpected token '$'; expected '...'` (and it is
*not* fixed by deleting the space before the operator). Drop the `kind|` prefix and write the
bare quotation exactly as the notation's own `macro_rules` quote it, with the operator glued
to its operand (no surrounding space): `` `($a:term...%$opTk $b:term) `` (see the `fmtRange*`
formatters in `Formatters/Init/Data/Range/Polymorphic/PRange.lean`). The `@[builtin_fmt <kind>]`
registration already pins the formatter to the right node, so the bare pattern is unambiguous.
Operator-*first* forms have no leading operand and are unaffected either way:
`` `(*...%$opTk $b:term) `` works kind-qualified or bare. If the notation is also **`scoped`**, the
bare quotation only *parses* when its namespace is open — add `open scoped <Namespace>` to the
formatter file (e.g. `open scoped BitVec` for the trailing `_#'_` bitvector literal in
`Formatters/Init/Data/BitVec/Basic.lean`; the non-scoped, *leading* `_#_` literal in the same file
is unaffected and keeps its kind-qualified pattern).

**A trailing `?`/`!` token can't be bound with `%$` — read it by index, and mind `noWs`
group nodes.** A literal `?` or `!` immediately after a token splice (or antiquotation) is
consumed as the antiquotation's optional/`many` modifier: in `` `($t:term[%$lbTk $i:term]%$rbTk?%$questionTk) ``
the `?` rebinds `rbTk` as an optional and `%$questionTk` never matches (`unknown identifier
rbTk`); even a separating space (`]%$rbTk ?`) fails to parse. Instead match the suffix
*literally* (`` `($t:term[%$lbTk $i:term]?) ``) and read the trailing token by index with
`getStxArg!`. When you do, remember that zero-width combinators like `noWs` can sit behind
empty `(group)`/null nodes in the tree, so child indices don't line up with the visible
tokens: the node for `x noWs "[" i "]" noWs "?"` is `x (group) "[" i "]" (group) "?"`, putting
`]` at index 4 and `?` at index 6 (not 3 and 4). Always dump the real tree first —
`Lean.Parser.runParserCategory env \`term "xs[i]?"` then `toString` — to read off the correct
indices (see `fmtGetElemQuestion`/`fmtGetElemExclamation` in `Formatters/Init/GetElem.lean`).
