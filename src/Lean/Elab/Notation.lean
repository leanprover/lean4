/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Syntax
import Lean.Elab.AuxDef
import Lean.Elab.BuiltinNotation

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

/-- Wrap all occurrences of the given `ident` nodes in antiquotations -/
private partial def antiquote (vars : Array Syntax) : Syntax → Syntax
  | stx => match stx with
  | `($id:ident) =>
    if vars.any (fun var => var.getId == id.getId) then
      mkAntiquotNode id (kind := `term) (isPseudoKind := true)
    else
      stx
  | _ => match stx with
    | Syntax.node i k args => Syntax.node i k (args.map (antiquote vars))
    | stx => stx

 def addInheritDocDefault (rhs : Term) (attrs? : Option (TSepArray ``attrInstance ",")) :
    Option (TSepArray ``attrInstance ",") :=
  attrs?.map fun attrs =>
    match rhs with
    | `($f:ident $_args*) | `($f:ident) =>
      attrs.getElems.map fun stx => Unhygienic.run do
        if let `(attrInstance| $attr:ident) := stx then
          if attr.getId.eraseMacroScopes == `inherit_doc then
            return ← `(attrInstance| $attr:ident $f:ident)
        pure ⟨stx⟩
    | _ => attrs

/-- Convert `notation` command lhs item into a `syntax` command item -/
def expandNotationItemIntoSyntaxItem : TSyntax ``notationItem → MacroM (TSyntax `stx)
  | `(notationItem| $_:ident$[:$prec?]?) => `(stx| term $[:$prec?]?)
  | `(notationItem| $s:str)              => `(stx| $s:str)
  | _                                    => Macro.throwUnsupported

/-- Convert `notation` command lhs item into a pattern element -/
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

/-- Try to derive an unexpander from a notation.
    The notation must be of the form `notation ... => c body`
    where `c` is a declaration in the current scope and `body` any syntax
    that contains each variable from the LHS at most once. -/
def mkUnexpander (attrKind : TSyntax ``attrKind) (pat qrhs : Term) : OptionT MacroM Syntax := do
  let (c, args) ← match qrhs with
    | `($c:ident $args*) => pure (c, args)
    | `($c:ident)        => pure (c, #[])
    | _                  => failure
  let [(c, [])] ← Macro.resolveGlobalName c.getId | failure
  /-
  Try to remove all non semantic parenthesis. Since the parenthesizer
  runs after appUnexpanders we should not match on parenthesis that the user
  syntax inserted here for example the right hand side of:
  notation "{" x "|" p "}" => setOf (fun x => p)
  Should be matched as: setOf fun x => p
  -/
  let args ← liftM <| args.mapM removeParentheses
  /-
  The user could mention the same antiquotation from the lhs multiple
  times on the rhs, this heuristic does not support this.
  -/
  guard !hasDuplicateAntiquot args
  -- replace head constant with antiquotation so we're not dependent on the exact pretty printing of the head
  -- The reference is attached to the syntactic representation of the called function itself, not the entire function application
  let lhs ← `($$f:ident)
  let lhs := Syntax.mkApp lhs (.mk args)
  `(@[$attrKind app_unexpander $(mkIdent c)]
    aux_def unexpand $(mkIdent c) : Lean.PrettyPrinter.Unexpander := fun
      | `($lhs)             => withRef f `($pat)
      | _                   => throw ())

private def expandNotationAux (ref : Syntax) (currNamespace : Name)
    (doc? : Option (TSyntax ``docComment))
    (attrs? : Option (TSepArray ``attrInstance ","))
    (attrKind : TSyntax ``attrKind)
    (prec? : Option Prec) (name? : Option Ident) (prio? : Option Prio)
    (items : Array (TSyntax ``notationItem)) (rhs : Term) : MacroM Syntax := do
  let prio ← evalOptPrio prio?
  -- build parser
  let syntaxParts ← items.mapM expandNotationItemIntoSyntaxItem
  let cat := mkIdentFrom ref `term
  let name ←
    match name? with
    | some name => pure name.getId
    | none => addMacroScopeIfLocal (← mkNameFromParserSyntax `term (mkNullNode syntaxParts)) attrKind
  -- build macro rules
  let vars := items.filter fun item => item.raw.getKind == ``identPrec
  let vars := vars.map fun var => var.raw[0]
  let qrhs := ⟨antiquote vars rhs⟩
  let attrs? := addInheritDocDefault rhs attrs?
  let patArgs ← items.mapM expandNotationItemIntoPattern
  /- The command `syntax [<kind>] ...` adds the current namespace to the syntax node kind.
     So, we must include current namespace when we create a pattern for the following `macro_rules` commands. -/
  let fullName := currNamespace ++ name
  let pat : Term := ⟨mkNode fullName patArgs⟩
  let stxDecl ← `($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
    syntax $[: $prec?]? (name := $(name?.getD (mkIdent name))) (priority := $(quote prio)) $[$syntaxParts]* : $cat)
  let macroDecl ← `(macro_rules | `($pat) => ``($qrhs))
  let macroDecls ←
    if isLocalAttrKind attrKind then
      -- Make sure the quotation pre-checker takes section variables into account for local notation.
      `(section set_option quotPrecheck.allowSectionVars true $macroDecl end)
    else
      pure ⟨mkNullNode #[macroDecl]⟩
  match (← mkUnexpander attrKind pat qrhs |>.run) with
  | some delabDecl => return mkNullNode #[stxDecl, macroDecls, delabDecl]
  | none           => return mkNullNode #[stxDecl, macroDecls]

@[builtin_macro Lean.Parser.Command.notation] def expandNotation : Macro
  | stx@`($[$doc?:docComment]? $[@[$attrs?,*]]? $attrKind:attrKind
      notation $[: $prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $items* => $rhs) => do
    -- trigger scoped checks early and only once
    let _ ← toAttributeKind attrKind
    expandNotationAux stx (← Macro.getCurrNamespace) doc? attrs? attrKind prec? name? prio? items rhs
  | _ => Macro.throwUnsupported

end Lean.Elab.Command
