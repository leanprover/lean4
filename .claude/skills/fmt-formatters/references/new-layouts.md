# Proposing New Layouts

New layouts go into `src/Lean/Fmt/FmtM/Layouts.lean` (namespace `Lean.Fmt.Layouts`).
A new layout must satisfy all of the following:

1. **It must be a re-occurring pattern.** A layout earns its place by being applicable
   in several formatters. If a document shape is needed by exactly one syntax, build it
   from primitives inside that formatter instead — that is what `Primitives.lean` is
   for.

2. **It must have a name that says what it does.** The name must make it easy to
   identify the layout's behavior and clearly distinguish it from the existing layouts
   (compare `horizontalOrVertical` vs `fill` vs `lines`: three different breaking
   behaviors, three unambiguous names). If you cannot assign a layout a good name,
   that is a signal the abstraction is wrong — there should be no layouts that cannot
   be given a good name. Prefer a parameter on an existing layout (like
   `Types.ApplicationFormat` / `Types.BracketFormat`) over a second, vaguely-named
   variant.

3. **It must correctly deal with empty documents.** Optional components arrive as
   `empty` documents (from `fmt?`). A layout must not produce stray separators, double
   spaces, or dangling keywords around them. Use `combine` (which drops always-empty
   components together with their separators) or filter with `isAlwaysEmpty` explicitly,
   and make sure the all-empty input collapses to `empty` (see `Layouts.bracketed`'s
   `body.isAlwaysEmpty` check and `Layouts.keywordSeparated`'s
   `keywordTk.isAlwaysEmpty` case).

Also follow the existing conventions: take `TaggedDoc`s (already formatted components),
not `Syntax`; pure functions, not `FmtM` (monadic helpers belong with the `fmt*`
utilities in `FmtM/CommonFormatters.lean`); configuration via a small `Types.<Name>Format`
inductive or structure next to the layout.
