/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Std.Do
import Init.NotationExtra
import Std.Tactic.Do.ProofMode -- For (meta) importing `mgoalStx`; otherwise users might experience
                               -- a broken goal view due to the builtin delaborator for `MGoalEntails`

namespace Lean.Parser

namespace Attr

/--
Theorems tagged with the `spec` attribute are used by the `mspec` and `mvcgen` tactics.

* When used on a theorem `foo_spec : Triple (foo a b c) P Q`, then `mspec` and `mvcgen` will use
  `foo_spec` as a specification for calls to `foo`.
* Otherwise, when used on a definition that `@[simp]` would work on, it is added to the internal
  simp set of `mvcgen` that is used within `wp⟦·⟧` contexts to simplify match discriminants and
  applications of constants.
-/
syntax (name := spec) "spec" (Tactic.simpPre <|> Tactic.simpPost)? patternIgnore("← " <|> "<- ")? (ppSpace prio)? : attr

end Attr

namespace Tactic

@[inherit_doc Lean.Parser.Tactic.massumptionMacro]
syntax (name := massumption) "massumption" : tactic

@[inherit_doc Lean.Parser.Tactic.mclearMacro]
syntax (name := mclear) "mclear" colGt ident : tactic

@[inherit_doc Lean.Parser.Tactic.mconstructorMacro]
syntax (name := mconstructor) "mconstructor" : tactic

@[inherit_doc Lean.Parser.Tactic.mexactMacro]
syntax (name := mexact) "mexact" colGt term : tactic

@[inherit_doc Lean.Parser.Tactic.mexfalsoMacro]
syntax (name := mexfalso) "mexfalso" : tactic

@[inherit_doc Lean.Parser.Tactic.mexistsMacro]
syntax (name := mexists) "mexists" term,+ : tactic

@[inherit_doc Lean.Parser.Tactic.mframeMacro]
syntax (name := mframe) "mframe" : tactic

/-- Duplicate a stateful `Std.Do.SPred` hypothesis. -/
syntax (name := mdup) "mdup" ident " => " ident : tactic

@[inherit_doc Lean.Parser.Tactic.mhaveMacro]
syntax (name := mhave) "mhave" ident optional(":" term) " := " term : tactic

@[inherit_doc Lean.Parser.Tactic.mreplaceMacro]
syntax (name := mreplace) "mreplace" ident optional(":" term) " := " term : tactic

@[inherit_doc Lean.Parser.Tactic.mrightMacro]
syntax (name := mright) "mright" : tactic

@[inherit_doc Lean.Parser.Tactic.mleftMacro]
syntax (name := mleft) "mleft" : tactic

@[inherit_doc Lean.Parser.Tactic.mpureMacro]
syntax (name := mpure) "mpure" colGt ident : tactic

@[inherit_doc Lean.Parser.Tactic.mpureIntroMacro]
macro (name := mpureIntro) "mpure_intro" : tactic =>
  `(tactic| apply $(mkIdent ``Std.Do.SPred.Tactic.Pure.intro))

@[inherit_doc Lean.Parser.Tactic.mrevertMacro]
syntax (name := mrevert) "mrevert" colGt ident : tactic

@[inherit_doc Lean.Parser.Tactic.mspecializeMacro]
syntax (name := mspecialize) "mspecialize" ident (colGt term:max)* : tactic

@[inherit_doc Lean.Parser.Tactic.mspecializePureMacro]
syntax (name := mspecializePure) "mspecialize_pure" term (colGt term:max)* " => " ident : tactic

@[inherit_doc Lean.Parser.Tactic.mstartMacro]
syntax (name := mstart) "mstart" : tactic

@[inherit_doc Lean.Parser.Tactic.mstopMacro]
syntax (name := mstop) "mstop" : tactic

declare_syntax_cat mcasesPat
syntax mcasesPatAlts := sepBy1(mcasesPat, " | ")
syntax binderIdent : mcasesPat
syntax "-" : mcasesPat
syntax "⟨" mcasesPatAlts,* "⟩" : mcasesPat
syntax "(" mcasesPatAlts ")" : mcasesPat
syntax "⌜" binderIdent "⌝" : mcasesPat
syntax "□" binderIdent : mcasesPat

macro "%" h:binderIdent : mcasesPat => `(mcasesPat| ⌜$h⌝)
macro "#" h:binderIdent : mcasesPat => `(mcasesPat| □ $h)

inductive MCasesPat
  | one (name : TSyntax ``binderIdent)
  | clear
  | tuple (args : List MCasesPat)
  | alts (args : List MCasesPat)
  | pure       (h : TSyntax ``binderIdent)
  | stateful (h : TSyntax ``binderIdent)
  deriving Repr, Inhabited

partial def MCasesPat.parse (pat : TSyntax `mcasesPat) : MacroM MCasesPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `mcasesPat → Option MCasesPat
  | `(mcasesPat| $name:binderIdent) => some <| .one name
  | `(mcasesPat| -) => some <| .clear
  | `(mcasesPat| ⟨$[$args],*⟩) => args.mapM goAlts |>.map (.tuple ·.toList)
  | `(mcasesPat| ⌜$h⌝) => some (.pure h)
  | `(mcasesPat| □$h) => some (.stateful h)
  | `(mcasesPat| ($pat)) => goAlts pat
  | _ => none
  goAlts : TSyntax ``mcasesPatAlts → Option MCasesPat
  | `(mcasesPatAlts| $args|*) =>
    match args.getElems with
    | #[arg] => go arg
    | args   => args.mapM go |>.map (.alts ·.toList)
  | _ => none

@[inherit_doc Lean.Parser.Tactic.mcasesMacro]
syntax (name := mcases) "mcases" ident " with " mcasesPat : tactic

declare_syntax_cat mrefinePat
syntax binderIdent : mrefinePat
syntax mrefinePats := sepBy1(mrefinePat, ", ")
syntax "⟨" mrefinePats "⟩" : mrefinePat
syntax "(" mrefinePat ")" : mrefinePat
syntax "⌜" term "⌝" : mrefinePat
syntax "□" binderIdent : mrefinePat
syntax "?" binderIdent : mrefinePat

macro "%" h:term : mrefinePat => `(mrefinePat| ⌜$h⌝)
macro "#" h:binderIdent : mrefinePat => `(mrefinePat| □ $h)

inductive MRefinePat
  | one (name : TSyntax ``binderIdent)
  | tuple (args : List MRefinePat)
  | pure       (h : TSyntax `term)
  | stateful (h : TSyntax ``binderIdent)
  | hole (name : TSyntax ``binderIdent)
  deriving Repr, Inhabited

partial def MRefinePat.parse (pat : TSyntax `mrefinePat) : MacroM MRefinePat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `mrefinePat → Option MRefinePat
  | `(mrefinePat| $name:binderIdent) => some <| .one name
  | `(mrefinePat| ?$name) => some (.hole name)
  | `(mrefinePat| ⟨$[$args],*⟩) => args.mapM go |>.map (.tuple ·.toList)
  | `(mrefinePat| ⌜$h⌝) => some (.pure h)
  | `(mrefinePat| □$h) => some (.stateful h)
  | `(mrefinePat| ($pat)) => go pat
  | _ => none

@[inherit_doc Lean.Parser.Tactic.mrefineMacro]
syntax (name := mrefine) "mrefine" mrefinePat : tactic

declare_syntax_cat mintroPat
syntax mcasesPat : mintroPat
syntax "∀" binderIdent : mintroPat

@[inherit_doc Lean.Parser.Tactic.mintroMacro]
syntax (name := mintro) "mintro" (ppSpace colGt mintroPat)+ : tactic

macro_rules
  | `(tactic| mintro $pat₁ $pat₂ $pats:mintroPat*) => `(tactic| mintro $pat₁; mintro $pat₂ $pats*)
  | `(tactic| mintro $pat:mintroPat) => do
    match pat with
    | `(mintroPat| $_:binderIdent) => Macro.throwUnsupported -- handled by a builtin elaborator
    | `(mintroPat| ∀$_:binderIdent) => Macro.throwUnsupported -- handled by a builtin elaborator
    | `(mintroPat| $pat:mcasesPat) => `(tactic| mintro h; mcases h with $pat)
    | _ => Macro.throwUnsupported -- presently unreachable

/--
`mspec_no_simp $spec` first tries to decompose `Bind.bind`s before applying `$spec`.
This variant of `mspec_no_simp` does not; `mspec_no_bind $spec` is defined as
```
try with_reducible mspec_no_bind Std.Do.Spec.bind
mspec_no_bind $spec
```
-/
syntax (name := mspecNoBind) "mspec_no_bind" (ppSpace colGt term)? : tactic

/--
Like `mspec`, but does not attempt slight simplification and closing of trivial sub-goals.
`mspec $spec` is roughly (the set of simp lemmas below might not be up to date)
```
mspec_no_simp $spec
all_goals
  ((try simp only [SPred.true_intro_simp, SPred.true_intro_simp_nil, SVal.curry_cons,
                   SVal.uncurry_cons, SVal.getThe_here, SVal.getThe_there]);
   (try mpure_intro; trivial))
```
-/
macro (name := mspecNoSimp) "mspec_no_simp" spec:(ppSpace colGt term)? : tactic =>
  `(tactic| ((try with_reducible mspec_no_bind $(mkIdent ``Std.Do.Spec.bind)); mspec_no_bind $[$spec]?))

@[inherit_doc Lean.Parser.Tactic.mspecMacro]
macro (name := mspec) "mspec" spec:(ppSpace colGt term)? : tactic =>
  `(tactic| (mspec_no_simp $[$spec]?
             all_goals ((try simp only [
                          $(mkIdent ``Std.Do.SPred.true_intro_simp):term,
                          $(mkIdent ``Std.Do.SPred.true_intro_simp_nil):term,
                          $(mkIdent ``Std.Do.SVal.curry_cons):term,
                          $(mkIdent ``Std.Do.SVal.uncurry_cons):term,
                          $(mkIdent ``Std.Do.SVal.getThe_here):term,
                          $(mkIdent ``Std.Do.SVal.getThe_there):term])
                        (try mpure_intro; trivial))))

@[inherit_doc Lean.Parser.Tactic.mvcgenMacro]
syntax (name := mvcgen) "mvcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

/--
Like `mvcgen`, but does not attempt to prove trivial VCs via `mpure_intro; trivial`.
-/
syntax (name := mvcgenNoTrivial) "mvcgen_no_trivial" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

/--
Like `mvcgen_no_trivial`, but `mvcgen_step 42` will only do 42 steps of the VC generation procedure.
This is helpful for bisecting bugs in `mvcgen` and tracing its execution.
-/
syntax (name := mvcgenStep) "mvcgen_step" optConfig
 (num)? (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic
