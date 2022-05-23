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

def getLinterUnusedVariables (o : Options) : Bool := o.get linter.unusedVariables.name (getLinterAll o)

def unusedVariables : Linter := fun stx => do
  let some stxRange := stx.getRange?
    | pure ()

  let fileMap := (← read).fileMap
  let refs := findModuleRefs fileMap (← get).infoState.trees.toArray

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

  for (id, ⟨decl?, uses⟩) in vars.toList do
    let some decl := decl?
      | continue
    let declStx := skipDeclIdIfPresent decl.stx
    let some range := declStx.getRange?
      | continue
    let some localDecl := decl.info.lctx.find? id
      | continue
    if !stxRange.contains range.start then
      continue

    if !getLinterUnusedVariables decl.ci.options then
      continue

    let some stack := findSyntaxStack? stx declStx
      | continue
    let ignoredPatternFns := [
      isTopLevelDecl constDecls,
      matchesUnusedPattern,
      isVariable,
      isInCtor,
      isInStructBinder,
      isInConstantWithoutDef,
      isInAxiom,
      isInDefWithForeignDefinition,
      isInDepArrow
    ]
    if ignoredPatternFns.any (· declStx stack) then
      continue

    if uses.isEmpty then
      publishMessage s!"unused variable `{localDecl.userName}`" range

  return ()
where
  skipDeclIdIfPresent (stx : Syntax) : Syntax :=
    if stx.isOfKind `Lean.Parser.Command.declId then
      stx[0]
    else
      stx

  isTopLevelDecl (constDecls : HashSet String.Range) (stx : Syntax) (stack : SyntaxStack) := Id.run <| do
    let some declRange := stx.getRange?
      | false
    constDecls.contains declRange &&
    !stackMatches stack [`Lean.Parser.Term.letIdDecl]
  matchesUnusedPattern (stx : Syntax) (_ : SyntaxStack) :=
    stx.getId.toString.startsWith "_"
  isVariable (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, `Lean.Parser.Command.variable]
  isInCtor (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, `Lean.Parser.Command.optDeclSig, `Lean.Parser.Command.ctor]
  isInStructBinder (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, `Lean.Parser.Command.optDeclSig, `Lean.Parser.Command.structSimpleBinder]
  isInConstantWithoutDef (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, `Lean.Parser.Command.declSig, `Lean.Parser.Command.constant] &&
    (stack.get? 4 |>.any fun (stx, _) => stx[3].getNumArgs == 0)
  isInAxiom (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, `Lean.Parser.Command.declSig, `Lean.Parser.Command.axiom]
  isInDefWithForeignDefinition (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, none, none, `Lean.Parser.Command.declaration] &&
    (stack.get? 3 |>.any fun (stx, _) =>
      stx.isOfKind `Lean.Parser.Command.optDeclSig ||
      stx.isOfKind `Lean.Parser.Command.declSig) &&
    (stack.get? 5 |>.any fun (stx, _) => Id.run <| do
      let declModifiers := stx[0]
      if !declModifiers.isOfKind `Lean.Parser.Command.declModifiers then
        return false
      let termAttributes := declModifiers[1][0]
      if !termAttributes.isOfKind `Lean.Parser.Term.attributes then
        return false
      let termAttrInstance := termAttributes[1][0]
      if !termAttrInstance.isOfKind `Lean.Parser.Term.attrInstance then
        return false

      let attr := termAttrInstance[1]
      if attr.isOfKind `Lean.Parser.Attr.extern then
        return true
      else if attr.isOfKind `Lean.Parser.Attr.simple then
        return attr[0].getId == `implementedBy
      else
        return false)
  isInDepArrow (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, `Lean.Parser.Term.explicitBinder, `Lean.Parser.Term.depArrow]

builtin_initialize addLinter unusedVariables

end Lean.Linter
