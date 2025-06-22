/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Init.NotationExtra

namespace Lean.Parser.Tactic

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
syntax (name := mpureIntro) "mpure_intro" : tactic

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
