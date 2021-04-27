/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Elab.Term

namespace Lean.Elab.Term.Quotation
open Lean.Syntax

register_builtin_option hygiene : Bool := {
  defValue := true
  descr    := "Annotate identifiers in quotations such that they are resolved relative to the scope at their declaration, not that at their eventual use/expansion, to avoid accidental capturing. Note that quotations/notations already defined are unaffected."
}

partial def getAntiquotationIds (stx : Syntax) : TermElabM (Array Syntax) := do
  let mut ids := #[]
  for stx in stx.topDown do
    if (isAntiquot stx || isTokenAntiquot stx) && !isEscapedAntiquot stx then
      let anti := getAntiquotTerm stx
      if anti.isIdent then ids := ids.push anti
      else throwErrorAt stx "complex antiquotation not allowed here"
  return ids

-- Get all pattern vars (as `Syntax.ident`s) in `stx`
partial def getPatternVars (stx : Syntax) : TermElabM (Array Syntax) :=
  if stx.isQuot then
    getAntiquotationIds stx
  else match stx with
    | `(_)            => #[]
    | `($id:ident)    => #[id]
    | `($id:ident@$e) => do (← getPatternVars e).push id
    | _               => throwErrorAt stx "unsupported pattern in syntax match{indentD stx}"

partial def getPatternsVars (pats : Array Syntax) : TermElabM (Array Syntax) :=
  pats.foldlM (fun vars pat => do return vars ++ (← getPatternVars pat)) #[]

end Lean.Elab.Term.Quotation
