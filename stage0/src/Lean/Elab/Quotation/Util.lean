/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Elab.Term

namespace Lean.Elab.Term.Quotation
open Lean.Syntax

partial def getAntiquotationIds : Syntax → TermElabM (Array Syntax) :=
  go #[]
  where go (ids : Array Syntax) : Syntax → TermElabM (Array Syntax)
    | stx@(Syntax.node k args) =>
      if isAntiquot stx && !isEscapedAntiquot stx then
        let anti := getAntiquotTerm stx
        if anti.isIdent then ids.push anti
        else throwErrorAt stx "complex antiquotation not allowed here"
      else
        args.foldlM go ids
    | _ => ids

-- Get all pattern vars (as `Syntax.ident`s) in `stx`
partial def getPatternVars (stx : Syntax) : TermElabM (Array Syntax) :=
  if stx.isQuot then
    getAntiquotationIds stx
  else match stx with
    | `($id:ident)    => #[id]
    | `($id:ident@$e) => do (← getPatternVars e).push id
    | _               => throwErrorAt stx "unsupported pattern in syntax match"

partial def getPatternsVars (pats : Array Syntax) : TermElabM (Array Syntax) :=
  pats.foldlM (fun vars pat => do return vars ++ (← getPatternVars pat)) #[]

end Lean.Elab.Term.Quotation
