import Lean.Elab.Command
import Lean.Linter.Util
import Lean.Elab.InfoTree
import Lean.Server.InfoUtils
import Lean.Server.References
import Std.Data.HashMap

namespace Lean.Linter
open Lean.Server Std

register_builtin_option linter.unusedVariables : Bool := {
  defValue := true,
  descr := "enable the 'unused variables' linter"
}
register_builtin_option linter.unusedVariables.funArgs : Bool := {
  defValue := true,
  descr := "enable the 'unused variables' linter to mark unused function arguments"
}
register_builtin_option linter.unusedVariables.patternVars : Bool := {
  defValue := true,
  descr := "enable the 'unused variables' linter to mark unused pattern variables"
}

def getLinterUnusedVariables (o : Options) : Bool := o.get linter.unusedVariables.name (getLinterAll o)
def getLinterUnusedVariablesFunArgs (o : Options) : Bool := o.get linter.unusedVariables.funArgs.name (getLinterUnusedVariables o)
def getLinterUnusedVariablesPatternVars (o : Options) : Bool := o.get linter.unusedVariables.patternVars.name (getLinterUnusedVariables o)

def unusedVariables : Linter := fun stx => do
  -- NOTE: `messages` is local to the current command
  if (← get).messages.hasErrors then
    return

  let some stxRange := stx.getRange?
    | pure ()

  let infoTrees := (← get).infoState.trees.toArray
  let fileMap := (← read).fileMap

  if (← infoTrees.anyM (·.hasSorry)) then
    return

  -- collect references
  let refs := findModuleRefs fileMap infoTrees

  let mut vars : HashMap FVarId RefInfo := .empty
  let mut constDecls : HashSet String.Range := .empty

  for (ident, info) in refs.toList do
    match ident with
    | .fvar id =>
      vars := vars.insert id info
    | .const _ =>
      if let some definition := info.definition then
        if let some range := definition.stx.getRange? then
          constDecls := constDecls.insert range

  -- collect uses from tactic infos
  let tacticMVarAssignments : HashMap MVarId Expr :=
    infoTrees.foldr (init := .empty) fun tree assignments =>
      tree.foldInfo (init := assignments) (fun _ i assignments => match i with
        | .ofTacticInfo ti =>
          ti.mctxAfter.eAssignment.foldl (init := assignments) fun assignments mvar expr =>
            if assignments.contains mvar then
              assignments
            else
              assignments.insert mvar expr
        | _ =>
          assignments)

  let tacticFVarUses : HashSet FVarId ←
    tacticMVarAssignments.foldM (init := .empty) fun uses _ expr => do
      let (_, s) ← StateT.run (s := uses) <| expr.forEach fun
        | .fvar id => modify (·.insert id)
        | _        => pure ()
      return s

  -- determine unused variables
  for (id, ⟨decl?, uses⟩) in vars.toList do
    let some decl := decl?
      | continue
    let declStx := skipDeclIdIfPresent decl.stx
    let some range := declStx.getRange?
      | continue
    let some localDecl := decl.info.lctx.find? id
      | continue
    if !stxRange.contains range.start || localDecl.userName.hasMacroScopes then
      continue

    let opts := decl.ci.options
    if !getLinterUnusedVariables opts then
      continue

    let mut ignoredPatternFns := #[
      isTopLevelDecl constDecls,
      matchesUnusedPattern,
      isVariable,
      isInStructure,
      isInInductive,
      isInCtorOrStructBinder,
      isInConstantOrAxiom,
      isInDefWithForeignDefinition,
      isInDepArrow
    ]
    if !getLinterUnusedVariablesFunArgs opts then
      ignoredPatternFns := ignoredPatternFns.append #[
        isInLetDeclaration,
        isInDeclarationSignature,
        isInFun
      ]
    if !getLinterUnusedVariablesPatternVars opts then
      ignoredPatternFns := ignoredPatternFns.append #[
        isPatternVar
      ]

    let some stack := findSyntaxStack? stx declStx
      | continue
    if ignoredPatternFns.any (· declStx stack) then
      continue

    if uses.isEmpty && !tacticFVarUses.contains id &&
        decl.aliases.all (match · with | .fvar id => !tacticFVarUses.contains id | _ => false) then
      publishMessage s!"unused variable `{localDecl.userName}`" range

  return ()
where
  skipDeclIdIfPresent (stx : Syntax) : Syntax :=
    if stx.isOfKind ``Lean.Parser.Command.declId then
      stx[0]
    else
      stx

  isTopLevelDecl (constDecls : HashSet String.Range) (stx : Syntax) (stack : SyntaxStack) := Id.run <| do
    let some declRange := stx.getRange?
      | false
    constDecls.contains declRange &&
    !stackMatches stack [``Lean.Parser.Term.letIdDecl]
  matchesUnusedPattern (stx : Syntax) (_ : SyntaxStack) :=
    stx.getId.toString.startsWith "_"
  isVariable (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, ``Lean.Parser.Command.variable]
  isInStructure (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, ``Lean.Parser.Command.structure]
  isInInductive (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, none, ``Lean.Parser.Command.inductive] &&
    (stack.get? 3 |>.any fun (stx, pos) =>
      pos == 0 &&
      [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·))
  isInCtorOrStructBinder (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, ``Lean.Parser.Command.optDeclSig, none] &&
    (stack.get? 4 |>.any fun (stx, _) =>
      [``Lean.Parser.Command.ctor, ``Lean.Parser.Command.structSimpleBinder].any (stx.isOfKind ·))
  isInConstantOrAxiom (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, ``Lean.Parser.Command.declSig, none] &&
    (stack.get? 4 |>.any fun (stx, _) =>
      [``Lean.Parser.Command.opaque, ``Lean.Parser.Command.axiom].any (stx.isOfKind ·))
  isInDefWithForeignDefinition (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, none, none, ``Lean.Parser.Command.declaration] &&
    (stack.get? 3 |>.any fun (stx, _) =>
      stx.isOfKind ``Lean.Parser.Command.optDeclSig ||
      stx.isOfKind ``Lean.Parser.Command.declSig) &&
    (stack.get? 5 |>.any fun (stx, _) => Id.run <| do
      let declModifiers := stx[0]
      if !declModifiers.isOfKind ``Lean.Parser.Command.declModifiers then
        return false
      let termAttributes := declModifiers[1][0]
      if !termAttributes.isOfKind ``Lean.Parser.Term.attributes then
        return false
      let termAttrInstance := termAttributes[1][0]
      if !termAttrInstance.isOfKind ``Lean.Parser.Term.attrInstance then
        return false

      let attr := termAttrInstance[1]
      if attr.isOfKind ``Lean.Parser.Attr.extern then
        return true
      else if attr.isOfKind ``Lean.Parser.Attr.simple then
        return attr[0].getId == `implementedBy
      else
        return false)
  isInDepArrow (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, ``Lean.Parser.Term.explicitBinder, ``Lean.Parser.Term.depArrow]

  isInLetDeclaration (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, ``Lean.Parser.Term.letIdDecl, none] &&
    (stack.get? 3 |>.any fun (_, pos) => pos == 1) &&
    (stack.get? 5 |>.any fun (stx, _) => !stx.isOfKind ``Lean.Parser.Command.whereStructField)
  isInDeclarationSignature (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, none] &&
    (stack.get? 3 |>.any fun (stx, pos) =>
      pos == 0 &&
      [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·))
  isInFun (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, ``Lean.Parser.Term.basicFun] ||
    stackMatches stack [`null, ``Lean.Parser.Term.paren, `null, ``Lean.Parser.Term.basicFun]

  isPatternVar (_ : Syntax) (stack : SyntaxStack) :=
    stack.any fun (stx, pos) =>
      (stx.isOfKind ``Lean.Parser.Term.matchAlt && pos == 1) ||
      (stx.isOfKind ``Lean.Parser.Tactic.inductionAltLHS && pos == 2)

builtin_initialize addLinter unusedVariables

end Lean.Linter
