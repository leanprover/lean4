/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term

namespace Lean
namespace Elab
namespace Term

private def expandSimpleMatch (stx discr lhsVar rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
newStx ← `(let $lhsVar := $discr; $rhs);
withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private def expandSimpleMatchWithType (stx discr lhsVar type rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
newStx ← `(let $lhsVar : $type := $discr; $rhs);
withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private def expandMatchOptTypeAux (ref : Syntax) : Nat → MacroM Syntax
| 0   => pure $ mkHole ref
| n+1 => do t ← expandMatchOptTypeAux n; r ← `(forall _, $t); pure (r.copyInfo ref)

private def expandMatchOptType (ref : Syntax) (optType : Syntax) (numDiscrs : Nat) : MacroM Syntax :=
if optType.isNone then
  expandMatchOptTypeAux ref numDiscrs
else
  pure $ (optType.getArg 0).getArg 1

/-
```
def matchDiscr := optIdent >> termParser
parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
```
Remark the `optIdent` must be `none` at `matchDiscr`. They are expanded by `expandMatchDiscr?`.
-/
private def elabMatchCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
tryPostponeIfNoneOrMVar expectedType?;
let discrs := (stx.getArg 1).getArgs.getSepElems.map fun d => d.getArg 1;
typeStx ← liftMacroM $ expandMatchOptType stx (stx.getArg 2) discrs.size;
type ← elabType typeStx;
throwError stx ("WIP type: " ++ type ++ "\n" ++ stx ++ "\n" ++ toString discrs)

/-- Expand discriminants of the form `h : t` -/
private def expandMatchDiscr? (stx : Syntax) : MacroM (Option Syntax) := do
pure none -- TODO

-- parser! "match " >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermElab «match»] def elabMatch : TermElab :=
fun stx expectedType? => match_syntax stx with
  | `(match $discr:term with $y:ident => $rhs:term)           => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term with | $y:ident => $rhs:term)         => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term : $type with $y:ident => $rhs:term)   => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | `(match $discr:term : $type with | $y:ident => $rhs:term) => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | _ => do
    stxNew? ← liftMacroM $ expandMatchDiscr? stx;
    match stxNew? with
    | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
    | none        => elabMatchCore stx expectedType?

end Term
end Elab
end Lean
