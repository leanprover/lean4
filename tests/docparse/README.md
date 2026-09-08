# Verso parser tests

The part of each `.txt` filename before the first `_` selects the parser that reads it (see
`testConfigs` in `run_test.lean`). The expected output records the resulting syntax tree, any parse
errors, and, for parsers whose output reproduces their input exactly, a round-trip verdict from
`validateRoundTrip`.

`validateRoundTrip` checks four properties:

* Every leaf has `.original` source info whose text is exactly the input at its recorded range.
* The leaves are in order, and no two of them overlap.
* The whitespace recorded on the leaves exactly fills the gaps between tokens.
* `Syntax.reprint` reproduces the input.

Configs that only classify input or discard their output (`inlineTextChar`, `blockOpener`, and the
lookahead marker configs) skip the check. The check also runs for parses that reported errors, so
the expected output files pin how the harness treats recovered and partial output. A successful
parse has to pass the check. An errored parse records whatever verdict its recovery produces,
ordinarily a failure at a `<missing>` leaf or an uncovered region.

The `coverage_0001.txt` entry leaves its own contents unparsed. It re-parses every input file in the
directory instead. It fails when no successful parse result contains some syntax kind from
`parserProducedKinds` in `run_test.lean`. Keep that list in step with the productions in
`Lean.DocString.Syntax` when the parser changes.

The `blankPara_0001.txt` entry re-parses every input file as well. It fails when a paragraph in a
successful parse is written as nothing but whitespace. A paragraph contains content, so a run of
empty lines is not a paragraph. It judges by the text as written, because an escape makes content
out of the character it escapes: `\ ` on a line of its own is a paragraph whose decoded content is a
space.

## Parser coverage audit

The table maps each production-level `ParserFn` in `Lean.DocString.Parser` to the test-file
prefixes that exercise it. These productions also exercise the generic combinators (`atLeastFn`,
`asTokenFn`, `ignoreFn`, `withCurrentColumn`, the `recover*` family, and so on). The
`recoverBlock`/`recoverBlocks` prefixes also target the recovery paths.

| `ParserFn` | Exercised by prefixes |
| --- | --- |
| `valFn` | `arg_val`, `arg`, `args`, `nameAndArgs` |
| `argFn` (positional, named with and without parens, flags) | `arg`, `args`, `nameAndArgs`, `codeBlock`, `directive`, `role` |
| `argsFn` | `args`, `nameAndArgs` |
| `nameAndArgsFn` | `nameAndArgs`, `codeBlock`, `directive`, `role` |
| `inlineTextCharFn` | `inlineTextChar`, `manyInlineTextChar`, `text` |
| `textFn` (incl. escapes) | `text`, `emph`, `oneInline`, `blocks`, `document` |
| `linebreakFn` | `block`, `blocks`, `oneInline`, `document` |
| `emphFn` | `emph`, `blocks`, `role` |
| `boldFn` | `blocks`, `oneInline`, `role` |
| `codeFn` (incl. backtick runs, space stripping) | `code`, `oneInline`, `blocks`, `role` |
| `mathFn` (`$` and `$$`) | `oneInline` |
| `linkFn`, `linkTargetFn` (URL and reference targets) | `block`, `blocks`, `oneInline` |
| `imageFn` | `blocks`, `document`, `oneInline` |
| `footnoteFn` | `block`, `blocks`, `oneInline` |
| `roleFn` (bracketed and bracketless) | `role`, `block`, `oneInline` |
| `blockOpenerFn` | `blockOpener` |
| `lookaheadUnorderedListMarker` | `lookaheadUnorderedListMarker` |
| `lookaheadOrderedListMarker` | `lookaheadOrderedListMarker` |
| `unorderedMarkersFn`, `numberingFn`, `listItemFn`, `unorderedListFn`, `orderedListFn` (both numbering styles) | `blocks`, `block`, `directive` |
| `definitionListFn`, `descItemFn` | `blocks` |
| `blockquoteFn` | `blocks` |
| `paraFn` | `block`, `blocks`, `directive`, `document` |
| `headerFn` | `header`, `blocks` |
| `codeBlockFn` (named and anonymous, indentation, blank lines) | `codeBlock`, `block` |
| `directiveFn` (incl. nesting) | `directive`, `blocks` |
| `blockCommandFn` | `block`, `blocks` |
| `linkRefFn` | `blocks` |
| `footnoteRefFn` | `blocks` |
| `metadataBlockFn`, `metadataContents` | `metadataBlock`, `blocks` |
| `blockFn`, `blocksFn`, `blocks1Fn` | `block`, `blocks`, `recoverBlock`, `recoverBlocks` |
| `documentFn` (incl. empty, whitespace-only, tabs, CRLF input) | `document` |
| `blockTailWs`, `lineTailWs`, `wsFallback` | `blocks`, `document` |

## Writing doc syntax in quotations

Each production has a parser of its own, so a quotation can write document syntax, as in
`` `(Lean.Doc.Parser.Block.para| $inls*) ``. Delimiter runs have their own parsers too. A quotation
that leaves the delimiter open splices one in (`$b:listMarker`, `$i:headerMarker`,
`$d:emphDelimiter`, `$m:inlineMathMarker`), instead of fixing a marker style or a header level.

There are three limitations.

A quotation cannot write literal content out. Content tokens have no delimiters of their own, so
`versoText`, `versoCode`, and `versoCodeBlock` accept only antiquotations. Inline code has a further
restriction. Backticks already have a meaning inside a quotation, so splice its delimiters as
`$d:codeDelimiter` too.

A quotation cannot splice both halves of a description list item. Nothing that a quotation can see
separates its inlines from its blocks.

The literal list form is ambiguous. In `` `(Lean.Doc.Parser.Block.ul| * $bs* * $cs*) `` an item's
contents absorb the marker that follows. The real parser uses indentation to find the end of an
item, and a quotation has no indentation. Splice the items instead, as
`` `(Lean.Doc.Parser.Block.ul| $items*) ``.
