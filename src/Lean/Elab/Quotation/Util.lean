/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.Term
public import Lean.Linter.Init
import Init.Omega
import Init.Data.Array.Mem

public section

namespace Lean.Elab.Term.Quotation
open Lean.Syntax

register_builtin_option hygiene : Bool := {
  defValue := true
  descr    := "Annotate identifiers in quotations such that they are resolved relative to the scope at their declaration, not that at their eventual use/expansion, to avoid accidental capturing. Note that quotations/notations already defined are unaffected."
}

def getAntiquotationIds (stx : Syntax) : TermElabM (Array Ident) := do
  let mut ids := #[]
  for stx in stx.topDown (firstChoiceOnly := true) do
    if (isAntiquot stx || isTokenAntiquot stx) && !isEscapedAntiquot stx then
      let anti := getAntiquotTerm stx
      if anti.isIdent then ids := ids.push ⟨anti⟩
      else if anti.isOfKind ``Parser.Term.hole then pure ()
      else throwErrorAt stx "complex antiquotation not allowed here"
  return ids

/-- Get all pattern vars (as `Syntax.ident`s) in `stx` -/
partial def getPatternVars (stx : Syntax) : TermElabM (Array Syntax) :=
  if stx.isQuot then
    getAntiquotationIds stx
  else match stx with
    | `(_)            => return #[]
    | `($id:ident)    => return #[id]
    | `($id:ident@$e) => return (← getPatternVars e).push id
    | _               => throwErrorAt stx "unsupported pattern in syntax match{indentD stx}"

def getPatternsVars (pats : Array Syntax) : TermElabM (Array Syntax) :=
  pats.foldlM (fun vars pat => do return vars ++ (← getPatternVars pat)) #[]

/--
Given an antiquotation like `$e:term` (i.e. `Syntax.antiquotKind?` returns `some`),
returns the `"term"` atom if present.
-/
def getAntiquotKindSpec? (antiquot : Syntax) : Option Syntax :=
  let name := antiquot[3][1]
  if name.isMissing then none else some name

def resolveSectionVariable (sectionVars : NameMap Name) (id : Name) : List (Name × List String) :=
  -- decode macro scopes from name before recursion
  let extractionResult := extractMacroScopes id
  let rec loop : Name → List String → List (Name × List String)
    | id@(.str p s), projs =>
      -- NOTE: we assume that macro scopes always belong to the projected constant, not the projections
      let id := { extractionResult with name := id }.review
      match sectionVars.find? id with
      | some newId => [(newId, projs)]
      | none       => loop p (s::projs)
    | _, _ => []
  loop extractionResult.name []

/-- Collect named `?x` synthetic holes inside ordinary quotation content, ignoring `?_`,
antiquotations, nested quotations, and `expr` quotations. -/
def collectNamedSyntaxHoles (stx : Syntax) : Array (Syntax × Name) :=
  go stx #[]
where
  go (cur : Syntax) (acc : Array (Syntax × Name)) : Array (Syntax × Name) :=
    if cur.isOfKind `Lean.Parser.Term.syntheticHole then
      if cur[1].isIdent then acc.push (cur, cur[1].getId.eraseMacroScopes) else acc
    else if cur.isAntiquot || cur.isTokenAntiquot || cur.isAntiquotSplice ||
        cur.isAntiquotSuffixSplice || cur.isQuot ||
        cur.isOfKind `Lean.Parser.Term.exprQuot then
      acc
    else
      match cur with
      | .node _ _ args =>
        args.foldl (init := acc) fun a child => go child a
      | _ => acc
  termination_by sizeOf cur
  decreasing_by
    simp_wf
    have := Array.sizeOf_lt_of_mem ‹_›
    omega

/-- Emit `linter.exprQuot.syntaxHole` warnings for named `?x` holes inside ordinary syntax
quotation content `quotContent` appearing in an `Expr` context. -/
def warnNamedSyntaxHolesInQuot (quotContent : Syntax) : TermElabM Unit := do
  unless Linter.getLinterValue Linter.linter.exprQuot.syntaxHole (← Linter.getLinterOptions) do
    return
  for (holeStx, name) in collectNamedSyntaxHoles quotContent do
    Linter.logLintIf Linter.linter.exprQuot.syntaxHole holeStx
      m!"named pattern variable `?{name}` inside ordinary syntax quotation in an `Expr` \
         context; did you mean `` `(expr| ...) ``?"

end Lean.Elab.Term.Quotation
