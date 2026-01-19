/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do
public import Std.Tactic.Do.ProofMode -- For (meta) importing `mgoalStx`; otherwise users might experience
                                      -- a broken goal view due to the builtin delaborator for `MGoalEntails`

@[expose] public section


namespace Lean.Elab.Tactic.Do.VCGen

structure Config where
  /--
  If `true` (the default), we will try to prove VCs via `mvcgen_trivial`, which is extensible
  via `macro_rules`.
  -/
  trivial : Bool := true
  /--
  If `true` (the default), we will simplify every generated VC after trying
  `mvcgen_trivial` by running `mleave`. (Note that this can be expensive.)
  -/
  leave : Bool := true
  /--
  If `true` (the default), we substitute away let-declarations that are used at most once before
  starting VC generation and will do the same for every VC generated.
  -/
  elimLets : Bool := true
  /--
  If `false` (the default), then we aggressively split `if` and `match` statements and inline join
  points unconditionally. For some programs this causes exponential blowup of VCs.
  Set this flag to choose a more conservative (but slightly lossy) encoding that traverses
  every join point only once and yields a formula the size of which is linear in the number of
  control flow splits.
  -/
  jp : Bool := false
  /--
  If set to `some n`, `mvcgen` will only do 42 steps of the VC generation procedure.
  This is helpful for bisecting bugs in `mvcgen` and tracing its execution.
  -/
  stepLimit : Option Nat := none
end Lean.Elab.Tactic.Do.VCGen

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

@[tactic_alt Lean.Parser.Tactic.massumptionMacro]
syntax (name := massumption) "massumption" : tactic

@[tactic_alt Lean.Parser.Tactic.mclearMacro]
syntax (name := mclear) "mclear" colGt ident : tactic

@[tactic_alt Lean.Parser.Tactic.mclearMacro]
macro (name := mclearError) "mclear" : tactic => Macro.throwError "`mclear` expects at an identifier"

@[tactic_alt Lean.Parser.Tactic.mconstructorMacro]
syntax (name := mconstructor) "mconstructor" : tactic

@[tactic_alt Lean.Parser.Tactic.mexactMacro]
syntax (name := mexact) "mexact" colGt term : tactic

@[tactic_alt Lean.Parser.Tactic.mexactMacro]
macro (name := mexactError) "mexact" : tactic => Macro.throwError "`mexact` expects a term"

@[tactic_alt Lean.Parser.Tactic.mexfalsoMacro]
syntax (name := mexfalso) "mexfalso" : tactic

@[tactic_alt Lean.Parser.Tactic.mexistsMacro]
syntax (name := mexists) "mexists" term,+ : tactic

@[tactic_alt Lean.Parser.Tactic.mexistsMacro]
macro (name := mexistsError) "mexists" : tactic => Macro.throwError "`mexists` expects at least one term"

@[tactic_alt Lean.Parser.Tactic.mframeMacro]
syntax (name := mframe) "mframe" : tactic

/-- Duplicate a stateful `Std.Do.SPred` hypothesis. -/
syntax (name := mdup) "mdup" ident " => " ident : tactic

@[tactic_alt Lean.Parser.Tactic.mhaveMacro]
syntax (name := mhave) "mhave" ident optional(":" term) " := " term : tactic

@[tactic_alt Lean.Parser.Tactic.mhaveMacro]
macro (name := mhaveError) "mhave" : tactic => Macro.throwError "The syntax is `mhave h := term`"

@[tactic_alt Lean.Parser.Tactic.mreplaceMacro]
syntax (name := mreplace) "mreplace" ident optional(":" term) " := " term : tactic

@[tactic_alt Lean.Parser.Tactic.mreplaceMacro]
macro (name := mreplaceError) "mreplace" : tactic => Macro.throwError "The syntax is `mreplace h := term`"

@[tactic_alt Lean.Parser.Tactic.mrightMacro]
syntax (name := mright) "mright" : tactic

@[tactic_alt Lean.Parser.Tactic.mleftMacro]
syntax (name := mleft) "mleft" : tactic

@[tactic_alt Lean.Parser.Tactic.mpureMacro]
syntax (name := mpure) "mpure" colGt ident : tactic

@[tactic_alt Lean.Parser.Tactic.mpureMacro]
macro (name := mpureError) "mpure" : tactic => Macro.throwError "`mpure` expects an identifier"

@[tactic_alt Lean.Parser.Tactic.mpureIntroMacro]
syntax (name := mpureIntro) "mpure_intro" : tactic

@[tactic_alt Lean.Parser.Tactic.mrenameIMacro]
syntax (name := mrenameI) "mrename_i" (ppSpace colGt binderIdent)+ : tactic

@[tactic_alt Lean.Parser.Tactic.mrenameIMacro]
macro (name := mrenameIError) "mrename_i" : tactic => Macro.throwError "`mrename_i` expects at least one identifier"

@[tactic_alt Lean.Parser.Tactic.mspecializeMacro]
syntax (name := mspecialize) "mspecialize" ident (colGt term:max)* : tactic

@[tactic_alt Lean.Parser.Tactic.mspecializeMacro]
macro (name := mspecializeError) "mspecialize" : tactic => Macro.throwError "The syntax is `mspecialize h term*`"

@[tactic_alt Lean.Parser.Tactic.mspecializePureMacro]
syntax (name := mspecializePure) "mspecialize_pure" term (colGt term:max)* " => " ident : tactic

@[tactic_alt Lean.Parser.Tactic.mspecializeMacro]
macro (name := mspecializePureError) "mspecialize_pure" : tactic => Macro.throwError "The syntax is `mspecialize_pure h term*`"

@[tactic_alt Lean.Parser.Tactic.mstartMacro]
syntax (name := mstart) "mstart" : tactic

@[tactic_alt Lean.Parser.Tactic.mstopMacro]
syntax (name := mstop) "mstop" : tactic

@[tactic_alt Lean.Parser.Tactic.mleaveMacro]
macro (name := mleave) "mleave" : tactic =>
  `(tactic| (try simp only [
              $(mkIdent ``Std.Do.SPred.down_pure):term,
              $(mkIdent ``Std.Do.SPred.apply_pure):term,
              -- $(mkIdent ``Std.Do.SPred.entails_cons):term, -- Ineffective until #9015 lands
              $(mkIdent ``Std.Do.SPred.entails_1):term,
              $(mkIdent ``Std.Do.SPred.entails_2):term,
              $(mkIdent ``Std.Do.SPred.entails_3):term,
              $(mkIdent ``Std.Do.SPred.entails_4):term,
              $(mkIdent ``Std.Do.SPred.entails_5):term,
              $(mkIdent ``Std.Do.SPred.entails_nil):term,
              $(mkIdent ``Std.Do.SPred.and_cons):term,
              $(mkIdent ``Std.Do.SPred.and_nil):term,
              $(mkIdent ``Std.Do.SPred.or_cons):term,
              $(mkIdent ``Std.Do.SPred.or_nil):term,
              $(mkIdent ``Std.Do.SPred.not_cons):term,
              $(mkIdent ``Std.Do.SPred.not_nil):term,
              $(mkIdent ``Std.Do.SPred.imp_cons):term,
              $(mkIdent ``Std.Do.SPred.imp_nil):term,
              $(mkIdent ``Std.Do.SPred.iff_cons):term,
              $(mkIdent ``Std.Do.SPred.iff_nil):term,
              $(mkIdent ``Std.Do.SPred.exists_cons):term,
              $(mkIdent ``Std.Do.SPred.exists_nil):term,
              $(mkIdent ``Std.Do.SPred.forall_cons):term,
              $(mkIdent ``Std.Do.SPred.forall_nil):term,
              $(mkIdent ``Std.Do.SVal.curry_cons):term,
              $(mkIdent ``Std.Do.SVal.curry_nil):term,
              $(mkIdent ``Std.Do.SVal.uncurry_cons):term,
              $(mkIdent ``Std.Do.SVal.uncurry_nil):term,
              $(mkIdent ``Std.Do.SVal.getThe_here):term,
              $(mkIdent ``Std.Do.SVal.getThe_there):term,
              $(mkIdent ``Std.Do.ExceptConds.entails.refl):term,
              $(mkIdent ``Std.Do.ExceptConds.entails_true):term,
              $(mkIdent ``Std.Do.ExceptConds.entails_false):term,
              $(mkIdent ``ULift.down_ite):term,
              $(mkIdent ``ULift.down_dite):term,
              $(mkIdent ``List.Cursor.prefix_at):term,
              $(mkIdent ``List.Cursor.suffix_at):term,
              $(mkIdent ``List.Cursor.current_at):term,
              $(mkIdent ``List.Cursor.tail_at):term,
              $(mkIdent ``and_imp):term,
              $(mkIdent ``and_true):term,
              $(mkIdent ``dite_eq_ite):term,
              $(mkIdent ``exists_prop):term,
              $(mkIdent ``true_implies):term] at *))

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

@[tactic_alt Lean.Parser.Tactic.mcasesMacro]
syntax (name := mcases) "mcases" ident " with " mcasesPat : tactic

@[tactic_alt Lean.Parser.Tactic.mcasesMacro]
macro (name := mcasesError) "mcases" : tactic => Macro.throwError "The syntax is `mcases h with pat`"

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

@[tactic_alt Lean.Parser.Tactic.mrefineMacro]
syntax (name := mrefine) "mrefine" mrefinePat : tactic

@[tactic_alt Lean.Parser.Tactic.mrefineMacro]
macro (name := mrefineError) "mrefine" : tactic => Macro.throwError "`mrefine` expects a pattern"

declare_syntax_cat mintroPat
syntax mcasesPat : mintroPat
syntax "∀" binderIdent : mintroPat

@[tactic_alt Lean.Parser.Tactic.mintroMacro]
syntax (name := mintro) "mintro" (ppSpace colGt mintroPat)+ : tactic

@[tactic_alt Lean.Parser.Tactic.mintroMacro]
macro (name := mintroError) "mintro" : tactic => Macro.throwError "`mintro` expects at least one pattern"

macro_rules
  | `(tactic| mintro $pat₁ $pat₂ $pats:mintroPat*) => `(tactic| mintro $pat₁; mintro $pat₂ $pats*)
  | `(tactic| mintro $pat:mintroPat) => do
    match pat with
    | `(mintroPat| $_:binderIdent) => Macro.throwUnsupported -- handled by a builtin elaborator
    | `(mintroPat| ∀$_:binderIdent) => Macro.throwUnsupported -- handled by a builtin elaborator
    | `(mintroPat| $pat:mcasesPat) => `(tactic| mintro h; mcases h with $pat)
    | _ => Macro.throwUnsupported -- presently unreachable

declare_syntax_cat mrevertPat

syntax ident : mrevertPat
syntax "∀" optional(num) : mrevertPat

@[tactic_alt Lean.Parser.Tactic.mrevertMacro]
syntax (name := mrevert) "mrevert" (ppSpace colGt mrevertPat)* : tactic

@[tactic_alt Lean.Parser.Tactic.mrevertMacro]
macro (name := mrevertError) "mrevert" : tactic => Macro.throwError "`mrevert` expects at least one pattern"

macro_rules
  | `(tactic| mrevert $pat₁ $pat₂ $pats:mrevertPat*) => `(tactic| mrevert $pat₁; mrevert $pat₂ $pats*)

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
  ((try simp only [SPred.true_intro_simp, SPred.apply_pure]);
   (try mpure_intro; trivial))
```
-/
macro (name := mspecNoSimp) "mspec_no_simp" spec:(ppSpace colGt term)? : tactic =>
  `(tactic| ((try with_reducible mspec_no_bind $(mkIdent ``Std.Do.Spec.bind)) <;> mspec_no_bind $[$spec]?))

@[tactic_alt Lean.Parser.Tactic.mspecMacro]
macro (name := mspec) "mspec" spec:(ppSpace colGt term)? : tactic =>
  `(tactic| (mspec_no_simp $[$spec]?
             all_goals ((try simp only [
                          $(mkIdent ``Std.Do.SPred.true_intro_simp):term,
                          $(mkIdent ``Std.Do.SPred.apply_pure):term])
                        (try mpure_intro; trivial))))

syntax "mvcgen_trivial_extensible" : tactic

/--
`mvcgen_trivial` is the tactic automatically called by `mvcgen` to discharge VCs.
It tries to discharge the VC by applying `(try mpure_intro); trivial` and otherwise delegates to
`mvcgen_trivial_extensible`.
Users are encouraged to extend `mvcgen_trivial_extensible` instead of this tactic in order not to
override the default `(try mpure_intro); trivial` behavior.
-/
macro "mvcgen_trivial" : tactic =>
  `(tactic| first
    | (try mpure_intro); trivial
    | try mvcgen_trivial_extensible
  )

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
In induction alternative, which can have 1 or more cases on the left
and `_`, `?_`, or a tactic sequence after the `=>`.
-/
syntax vcAlt := "| " sepBy1(caseArg, " | ") " => " tacticSeq -- `case` tactic has "case " instead of "| "

/--
After `with`, there is an optional tactic that runs on all branches, and
then a list of alternatives.
-/
syntax vcAlts := "with " (ppSpace colGt tactic)? withPosition((colGe vcAlt)*)

@[tactic_alt Lean.Parser.Tactic.mvcgenMacro]
syntax (name := mvcgen) "mvcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")?
  (invariantAlts)? (vcAlts)? : tactic

/--
A hint tactic that expands to `mvcgen invariants?`.
-/
syntax (name := mvcgenHint) "mvcgen?" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic
