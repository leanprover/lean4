/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Syntax
import Lean.Elab.AuxDef
import Lean.Elab.BuiltinNotation

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

/- Wrap all occurrences of the given `ident` nodes in antiquotations -/
private partial def antiquote (vars : Array Syntax) : Syntax → Syntax
  | stx => match stx with
  | `($id:ident) =>
    if (vars.findIdx? (fun var => var.getId == id.getId)).isSome then
      mkAntiquotNode id (kind := `term) (isPseudoKind := true)
    else
      stx
  | _ => match stx with
    | Syntax.node i k args => Syntax.node i k (args.map (antiquote vars))
    | stx => stx

/- Convert `notation` command lhs item into a `syntax` command item -/
def expandNotationItemIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    pure $ mkNode `Lean.Parser.Syntax.cat #[mkIdentFrom stx `term,  stx[1]]
  else if k == strLitKind then
    pure $ mkNode `Lean.Parser.Syntax.atom #[stx]
  else
    Macro.throwUnsupported

/- Convert `notation` command lhs item into a pattern element -/
def expandNotationItemIntoPattern (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    return mkAntiquotNode stx[0] (kind := `term) (isPseudoKind := true)
  else if k == strLitKind then
    strLitToPattern stx
  else
    Macro.throwUnsupported

def removeParenthesesAux (parens body : Syntax) : Syntax :=
  match parens.getHeadInfo, body.getHeadInfo, body.getTailInfo, parens.getTailInfo with
  | .original lead _ _ _, .original _ pos trail pos',
    .original endLead endPos _ endPos', .original _ _ endTrail _ =>
      body.setHeadInfo (.original lead pos trail pos') |>.setTailInfo (.original endLead endPos endTrail endPos')
  | _, _, _, _ => body

partial def removeParentheses (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(($e)) => pure $ removeParenthesesAux stx (←removeParentheses $ (←Term.expandCDot? e).getD e)
  | _ =>
    match stx with
    | .node info kind args => pure $ .node info kind (←args.mapM removeParentheses)
    | _ => pure stx

partial def hasDuplicateAntiquot (stxs : Array Syntax) : Bool := Id.run do
  let mut seen := NameSet.empty
  for stx in stxs do
    for node in Syntax.topDown stx true do
      if node.isAntiquot then
        let ident := node.getAntiquotTerm.getId
        if seen.contains ident then
          return true
        else
          seen := seen.insert ident
  pure false

/-- Try to derive a `SimpleDelab` from a notation.
    The notation must be of the form `notation ... => c body`
    where `c` is a declaration in the current scope and `body` any syntax
    that contains each variable from the LHS at most once. -/
def mkSimpleDelab (attrKind : Syntax) (pat qrhs : Syntax) : OptionT MacroM Syntax := do
  match qrhs with
  | `($c:ident $args*) =>
    let [(c, [])] ← Macro.resolveGlobalName c.getId | failure
    /-
    Try to remove all non semantic parenthesis. Since the parenthesizer
    runs after appUnexpanders we should not match on parenthesis that the user
    syntax inserted here for example the right hand side of:
    notation "{" x "|" p "}" => setOf (fun x => p)
    Should be matched as: setOf fun x => p
    -/
    let args ← args.mapM (liftM ∘ removeParentheses)
    /-
    The user could mention the same antiquotation from the lhs multiple
    times on the rhs, this heuristic does not support this.
    -/
    let dup := hasDuplicateAntiquot args
    guard !dup
    -- replace head constant with (unused) antiquotation so we're not dependent on the exact pretty printing of the head
    -- The reference is attached to the syntactic representation of the called function itself, not the entire function application
    `(@[$attrKind:attrKind appUnexpander $(mkIdent c):ident]
      aux_def unexpand $(mkIdent c) : Lean.PrettyPrinter.Unexpander := fun
       | `($$f:ident $args*) => withRef f `($pat)
       | _                   => throw ())
  | `($c:ident)        =>
    let [(c, [])] ← Macro.resolveGlobalName c.getId | failure
    `(@[$attrKind:attrKind appUnexpander $(mkIdent c):ident]
      aux_def unexpand $(mkIdent c) : Lean.PrettyPrinter.Unexpander := fun
       | `($$f:ident) => withRef f `($pat)
       | _            => throw ())
  | _                  => failure

private def isLocalAttrKind (attrKind : Syntax) : Bool :=
  match attrKind with
  | `(Parser.Term.attrKind| local) => true
  | _ => false

private def expandNotationAux (ref : Syntax)
    (currNamespace : Name) (attrKind : Syntax) (prec? : Option Syntax) (name? : Option Syntax) (prio? : Option Syntax) (items : Array Syntax) (rhs : Syntax) : MacroM Syntax := do
  let prio ← evalOptPrio prio?
  -- build parser
  let syntaxParts ← items.mapM expandNotationItemIntoSyntaxItem
  let cat := mkIdentFrom ref `term
  let name ←
    match name? with
    | some name => pure name.getId
    | none => mkNameFromParserSyntax `term (mkNullNode syntaxParts)
  -- build macro rules
  let vars := items.filter fun item => item.getKind == `Lean.Parser.Command.identPrec
  let vars := vars.map fun var => var[0]
  let qrhs := antiquote vars rhs
  let patArgs ← items.mapM expandNotationItemIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let fullName := currNamespace ++ name
  let pat := mkNode fullName patArgs
  let stxDecl ← `($attrKind:attrKind syntax $[: $prec?]? (name := $(mkIdent name)) (priority := $(quote prio):num) $[$syntaxParts]* : $cat)
  let mut macroDecl ← `(macro_rules | `($pat) => ``($qrhs))
  if isLocalAttrKind attrKind then
    -- Make sure the quotation pre-checker takes section variables into account for local notation.
    macroDecl ← `(section set_option quotPrecheck.allowSectionVars true $macroDecl end)
  match (← mkSimpleDelab attrKind pat qrhs |>.run) with
  | some delabDecl => return mkNullNode #[stxDecl, macroDecl, delabDecl]
  | none           => return mkNullNode #[stxDecl, macroDecl]

@[builtinMacro Lean.Parser.Command.notation] def expandNotation : Macro
  | stx@`($attrKind:attrKind notation $[: $prec? ]? $[(name := $name?)]? $[(priority := $prio?)]? $items* => $rhs) => do
    -- trigger scoped checks early and only once
    let _ ← toAttributeKind attrKind
    expandNotationAux stx (← Macro.getCurrNamespace) attrKind prec? name? prio? items rhs
  | _ => Macro.throwUnsupported

end Lean.Elab.Command
