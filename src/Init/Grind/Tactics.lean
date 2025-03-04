/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Tactics

namespace Lean.Parser
/--
Reset all `grind` attributes. This command is intended for testing purposes only and should not be used in applications.
-/
syntax (name := resetGrindAttrs) "%reset_grind_attrs" : command

namespace Attr
syntax grindEq     := "= "
syntax grindEqBoth := atomic("_" "=" "_ ")
syntax grindEqRhs  := atomic("=" "_ ")
syntax grindEqBwd  := atomic("←" "= ") <|> atomic("<-" "= ")
syntax grindBwd    := "← " <|> "-> "
syntax grindFwd    := "→ " <|> "<- "
syntax grindRL     := "⇐ " <|> "<= "
syntax grindLR     := "⇒ " <|> "=> "
syntax grindUsr    := &"usr "
syntax grindCases  := &"cases "
syntax grindCasesEager := atomic(&"cases" &"eager ")
syntax grindIntro  := &"intro "
syntax grindMod := grindEqBoth <|> grindEqRhs <|> grindEq <|> grindEqBwd <|> grindBwd <|> grindFwd <|> grindRL <|> grindLR <|> grindUsr <|> grindCasesEager <|> grindCases <|> grindIntro
syntax (name := grind) "grind" (grindMod)? : attr
end Attr
end Lean.Parser

namespace Lean.Grind
/--
The configuration for `grind`.
Passed to `grind` using, for example, the `grind (config := { matchEqs := true })` syntax.
-/
structure Config where
  /-- If `trace` is `true`, `grind` records used E-matching theorems and case-splits. -/
  trace : Bool := false
  /-- Maximum number of case-splits in a proof search branch. It does not include splits performed during normalization. -/
  splits : Nat := 8
  /-- Maximum number of E-matching (aka heuristic theorem instantiation) rounds before each case split. -/
  ematch : Nat := 5
  /--
  Maximum term generation.
  The input goal terms have generation 0. When we instantiate a theorem using a term from generation `n`,
  the new terms have generation `n+1`. Thus, this parameter limits the length of an instantiation chain. -/
  gen : Nat := 5
  /-- Maximum number of theorem instances generated using E-matching in a proof search tree branch. -/
  instances : Nat := 1000
  /-- If `matchEqs` is `true`, `grind` uses `match`-equations as E-matching theorems. -/
  matchEqs : Bool := true
  /-- If `splitMatch` is `true`, `grind` performs case-splitting on `match`-expressions during the search. -/
  splitMatch : Bool := true
  /-- If `splitIte` is `true`, `grind` performs case-splitting on `if-then-else` expressions during the search. -/
  splitIte : Bool := true
  /--
  If `splitIndPred` is `true`, `grind` performs case-splitting on inductive predicates.
  Otherwise, it performs case-splitting only on types marked with `[grind cases]` attribute. -/
  splitIndPred : Bool := false
  /-- By default, `grind` halts as soon as it encounters a sub-goal where no further progress can be made. -/
  failures : Nat := 1
  /-- Maximum number of heartbeats (in thousands) the canonicalizer can spend per definitional equality test. -/
  canonHeartbeats : Nat := 1000
  /-- If `ext` is `true`, `grind` uses extensionality theorems available in the environment. -/
  ext : Bool := true
  /-- If `verbose` is `false`, additional diagnostics information is not collected. -/
  verbose : Bool := true
  /-- If `clean` is `true`, `grind` uses `expose_names` and only generates accessible names. -/
  clean : Bool := true
  /--
  If `qlia` is `true`, `grind` may generate counterexamples for integer constraints using rational numbers.
  This approach is cheaper but incomplete. -/
  qlia : Bool := false
  deriving Inhabited, BEq

end Lean.Grind

namespace Lean.Parser.Tactic

/-!
`grind` tactic and related tactics.
-/

syntax grindErase := "-" ident
syntax grindLemma := (Attr.grindMod)? ident
syntax grindParam := grindErase <|> grindLemma

syntax (name := grind)
  "grind" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  ("on_failure " term)? : tactic


syntax (name := grindTrace)
  "grind?" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  ("on_failure " term)? : tactic

end Lean.Parser.Tactic
