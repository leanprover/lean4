/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Grind.Interactive
public import Init.NotationExtra

@[expose] public section

/-!
Syntax of the `vcgen` tactic for the `Std.WP` program logic. The builtin elaborator lives in
`Lean.Elab.Tactic.VCGen`.
-/

namespace Lean.Parser

namespace Attr

/--
Theorems tagged with the `spec` attribute are used by the `vcgen`, `mspec` and `mvcgen` tactics.

* When used on a theorem `foo_spec : Triple (foo a b c) P Q`, then `mspec` and `mvcgen` will use
  `foo_spec` as a specification for calls to `foo`.
* Otherwise, when used on a definition that `@[simp]` would work on, it is added to the internal
  simp set of `mvcgen` that is used within `wp⟦·⟧` contexts to simplify match discriminants and
  applications of constants.
-/
syntax (name := spec) "spec" (ppSpace prio)? : attr

end Attr

namespace Tactic

/--
An invariant alternative of the form `· term`, one per invariant goal.
-/
syntax invariantDotAlt := ppDedent(ppLine) cdotTk (colGe term)

/--
An invariant alternative of the form `| inv<n> a b c => term`, one per invariant goal.
-/
syntax invariantCaseAlt := ppDedent(ppLine) "| " caseArg " => " (colGe term)

/--
Either the contextual keyword ` invariants ` or its tracing form ` invariants? ` which suggests
skeletons for missing invariants as a hint.
-/
syntax invariantsKW := &"invariants " <|> &"invariants? "

/--
After `mvcgen [...]`, there can be an optional `invariants` followed by either
* a bulleted list of invariants `· term; · term`.
* a labelled list of invariants `| inv1 => term; inv2 a b c => term`, which is useful for naming
  inaccessibles.
The tracing variant ` invariants? ` will suggest a skeleton for missing invariants; see the
docstring for `mvcgen`.
-/
syntax invariantAlts := invariantsKW withPosition((colGe (invariantDotAlt <|> invariantCaseAlt))*)

/--
A single `frames` alternative `| f a _ c => frame`: a program pattern (a head identifier applied to
binder or `_` arguments, matched like the `until` pattern) and the frame assertion to apply when the
spec for that program is used during VC generation. The named binders (e.g. `a`, `c`) are in scope
in `frame`, bound to the matched arguments.
-/
syntax frameAlt := ppDedent(ppLine) "| " ident (ppSpace colGt binderIdent)* " => " (colGe term)

-- The optional `with $g` form is sugar for `sym => vcgen … <;> $g`. `$g` is a single grind-mode
-- step, so a multi-step sequence needs explicit grouping (e.g. `with (s₁; s₂)`).

/--
The discharging step in `vcgen … with`. It is a single `grind`-mode tactic (e.g. `finish`,
`intro`) so it can share `vcgen`'s internalised E-graph. The `tactic` alternative is a
lower-priority catch-all so that a non-`grind` step (e.g. `with grind`, `with simp`) still parses
and the elaborator can report a helpful error instead of a raw `expected grind` parser error.
-/
declare_syntax_cat vcgenDischarge
syntax (name := vcgenDischargeGrind) grind : vcgenDischarge
syntax (name := vcgenDischargeTactic) (priority := low) tactic : vcgenDischarge

@[tactic_alt Lean.Parser.Tactic.vcgenMacro]
syntax (name := vcgen) "vcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")?
  (&" until " term)?
  (&" frames " withPosition((colGe frameAlt)+))?
  (invariantAlts)?
  (&" simplifying_assumptions" (ppSpace colGt ident)? (" [" ident,* "]")?)?
  (&" with " vcgenDischarge)? : tactic

namespace Grind

/-- `vcgen` step for `sym => …` blocks. No `with` clause: compose with subsequent grind
steps using `<;>` instead. -/
syntax (name := vcgen) "vcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")?
  (&" until " term)?
  (&" frames " withPosition((colGe frameAlt)+))?
  (invariantAlts)?
  (&" simplifying_assumptions" (ppSpace colGt ident)? (" [" ident,* "]")?)?
  : grind

end Grind

end Tactic

end Lean.Parser
