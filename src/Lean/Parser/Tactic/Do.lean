/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Lean.Parser.Term

namespace Lean.Parser.Tactic.Do
open Lean Parser Term

syntax (name := massumption) "massumption" : tactic
syntax (name := mclear) "mclear" colGt ident : tactic
syntax (name := mconstructor) "mconstructor" : tactic
syntax (name := mexact) "mexact" colGt term : tactic
syntax (name := mexfalso) "mexfalso" : tactic
syntax (name := mexists) "mexists" term,+ : tactic
syntax (name := mframe) "mframe" : tactic
syntax (name := mdup) "mdup" ident " => " ident : tactic
syntax (name := mhave) "mhave" ident optType " := " term : tactic
syntax (name := mreplace) "mreplace" ident optType " := " term : tactic
syntax (name := mleft) "mleft" : tactic
syntax (name := mright) "mright" : tactic
syntax (name := mpure) "mpure" colGt ident : tactic
syntax (name := mpureIntro) "mpure_intro" : tactic
syntax (name := mrevert) "mrevert" colGt ident : tactic
syntax (name := mspecialize) "mspecialize" ident (colGt term:max)* : tactic
syntax (name := mspecializePure) "mspecialize_pure" term (colGt term:max)* " => " ident : tactic
syntax (name := mstart) "mstart" : tactic
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

/--
  Like `rcases`, but operating on stateful hypotheses.
  Example: Given a goal `h : (P ∧ (Q ∨ R) ∧ (Q → R)) ⊢ₛ R`,
  `mcases h with ⟨-, ⟨hq | hr⟩, hqr⟩` will yield two goals:
  `(hq : Q, hqr : Q → R) ⊢ₛ R` and `(hr : R) ⊢ₛ R`.

  That is, `mcases h with pat` has the following semantics, based on `pat`:
  * `pat=□h'` renames `h` to `h'` in the stateful context, regardless of whether `h` is pure
  * `pat=⌜h'⌝` introduces `h' : φ`  to the pure local context if `h : ⌜φ⌝` (c.f. `IsPure`)
  * `pat=h'` is like `pat=⌜h'⌝` if `h` is pure (c.f. `IsPure`), otherwise it is like `pat=□h'`.
  * `pat=_` renames `h` to an inaccessible name
  * `pat=-` discards `h`
  * `⟨pat₁, pat₂⟩` matches on conjunctions and existential quantifiers and recurses via
    `pat₁` and `pat₂`.
  * `⟨pat₁ | pat₂⟩` matches on disjunctions, matching the left alternative via `pat₁` and the right
    alternative via `pat₂`.
-/
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

syntax (name := mrefine) "mrefine" mrefinePat : tactic

declare_syntax_cat mintroPat
syntax mcasesPat : mintroPat
syntax "∀" binderIdent : mintroPat

/--
  Like `intro`, but introducing stateful hypotheses into the stateful context.
  That is, given a stateful goal `(hᵢ : Hᵢ)* ⊢ₛ P → T`, `mintro h` transforms
  intro `(hᵢ : Hᵢ)*, (h : P) ⊢ₛ T`.

  Furthermore, `mintro ∀s` is like `intro s`, but preserves the stateful goal.
  That is, `mintro ∀s` brings the topmost state variable `s:σ` in scope and transforms
  `(hᵢ : Hᵢ)* ⊢ₛ T` (where the entailment is in `SPred (σ::σs)`) into
  `(hᵢ : Hᵢ s)* ⊢ₛ T s` (where the entailment is in `SPred σs`).

  Beyond that, `mintro` supports the full syntax of `mcases` patterns
  (`mintro pat = (mintro h; mcases h with pat`), and can perform multiple
  introductions in sequence.
-/
syntax (name := mintro) "mintro" (ppSpace colGt mintroPat)+ : tactic
