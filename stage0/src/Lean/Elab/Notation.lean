/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Syntax

namespace Lean.Elab.Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

/- Wrap all occurrences of the given `ident` nodes in antiquotations -/
private partial def antiquote (vars : Array Syntax) : Syntax → Syntax
  | stx => match stx with
  | `($id:ident) =>
    if (vars.findIdx? (fun var => var.getId == id.getId)).isSome then
      mkAntiquotNode id
    else
      stx
  | _ => match stx with
    | Syntax.node k args => Syntax.node k (args.map (antiquote vars))
    | stx => stx

/- Convert `notation` command lhs item into a `syntax` command item -/
def expandNotationItemIntoSyntaxItem (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    pure $ Syntax.node `Lean.Parser.Syntax.cat #[mkIdentFrom stx `term,  stx[1]]
  else if k == strLitKind then
    pure $ Syntax.node `Lean.Parser.Syntax.atom #[stx]
  else
    Macro.throwUnsupported

/- Convert `notation` command lhs item into a pattern element -/
def expandNotationItemIntoPattern (stx : Syntax) : MacroM Syntax :=
  let k := stx.getKind
  if k == `Lean.Parser.Command.identPrec then
    mkAntiquotNode stx[0]
  else if k == strLitKind then
    strLitToPattern stx
  else
    Macro.throwUnsupported

/-- Try to derive a `SimpleDelab` from a notation.
    The notation must be of the form `notation ... => c var_1 ... var_n`
    where `c` is a declaration in the current scope and the `var_i` are a permutation of the LHS vars. -/
def mkSimpleDelab (attrKind : Syntax) (vars : Array Syntax) (pat qrhs : Syntax) : OptionT MacroM Syntax := do
  match qrhs with
  | `($c:ident $args*) =>
    let [(c, [])] ← Macro.resolveGlobalName c.getId | failure
    guard <| args.all (Syntax.isIdent ∘ getAntiquotTerm)
    guard <| args.allDiff
    -- replace head constant with (unused) antiquotation so we're not dependent on the exact pretty printing of the head
    `(@[$attrKind:attrKind appUnexpander $(mkIdent c):ident] def unexpand : Lean.PrettyPrinter.Unexpander := fun
       | `($$(_):ident $args*) => `($pat)
       | _                     => throw ())
  | `($c:ident)        =>
    let [(c, [])] ← Macro.resolveGlobalName c.getId | failure
    `(@[$attrKind:attrKind appUnexpander $(mkIdent c):ident] def unexpand : Lean.PrettyPrinter.Unexpander
       | `($$(_):ident) => `($pat)
       | _              => throw ())
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
  let pat := Syntax.node fullName patArgs
  let stxDecl ← `($attrKind:attrKind syntax $[: $prec?]? (name := $(mkIdent name)) (priority := $(quote prio):numLit) $[$syntaxParts]* : $cat)
  let mut macroDecl ← `(macro_rules | `($pat) => ``($qrhs))
  if isLocalAttrKind attrKind then
    -- Make sure the quotation pre-checker takes section variables into account for local notation.
    macroDecl ← `(section set_option quotPrecheck.allowSectionVars true $macroDecl end)
  match (← mkSimpleDelab attrKind vars pat qrhs |>.run) with
  | some delabDecl => mkNullNode #[stxDecl, macroDecl, delabDecl]
  | none           => mkNullNode #[stxDecl, macroDecl]

@[builtinMacro Lean.Parser.Command.notation] def expandNotation : Macro
  | stx@`($attrKind:attrKind notation $[: $prec? ]? $[(name := $name?)]? $[(priority := $prio?)]? $items* => $rhs) => do
    -- trigger scoped checks early and only once
    let _ ← toAttributeKind attrKind
    expandNotationAux stx (← Macro.getCurrNamespace) attrKind prec? name? prio? items rhs
  | _ => Macro.throwUnsupported


end Lean.Elab.Command
