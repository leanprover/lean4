import Lean.Elab.Command
import Lean.Linter.Util
import Lean.Elab.InfoTree
import Lean.Server.InfoUtils
import Lean.Server.References
import Std.Data.HashMap

namespace Lean.Linter
open Lean.Server Std

register_builtin_option linter.unusedVariables.nolint : Bool := {
  defValue := false,
  descr := "disable the 'unused variables' linter"
}

def unusedVariables : Linter := fun stx => do
  let some stxRange := stx.getRange?
    | pure ()

  let fileMap := (← read).fileMap
  let refs := dedupReferences <| combineFvars <| findReferences fileMap (← get).infoState.trees.toArray

  let mut vars : HashMap FVarId (Option Reference × Array Reference) := .empty
  let mut constDecls : HashSet String.Range := .empty

  for ref in refs do
    match ref.ident with
    | .fvar id =>
      let var := vars.findD id (none, #[])
      let var := match (var, ref.isBinder) with
      | ((none , usages), true ) => (some ref, usages)
      | ((decl?, usages), false) => (decl?, usages.push ref)
      | _ => var
      vars := vars.insert id var
    | .const _ =>
      if ref.isBinder then
        if let some range := ref.stx.getRange? then
          constDecls := constDecls.insert range

  for (id, (decl?, uses)) in vars.toList do
    let some decl := decl?
      | continue
    let some range := decl.stx.getRange?
      | continue
    let some localDecl := decl.info.lctx.find? id
      | continue
    if !stxRange.contains range.start then
      continue

    let opts := decl.ci.options
    if linter.nolint.get opts || linter.unusedVariables.nolint.get opts then
      continue

    if anyWithStack (stx := stx) (fun stx stack =>
      stx.getRange?.isEqSome range &&
      stx.isOfKind decl.stx.getKind && (
        matchesUnusedPattern stx stack ||
        isTopLevelDecl constDecls stx stack ||
        isVariable stx stack ||
        isInCtor stx stack ||
        isInStructBinder stx stack ||
        isInConstantWithoutDef stx stack ||
        isInAxiom stx stack ||
        isInDefWithForeignDefinition stx stack
    )) then continue

    if uses.isEmpty then
      let pos := fileMap.toPosition range.start
      publishMessage s!"unused variable `{localDecl.userName}` at {pos.line}:{pos.column + 1}" range

  return ()
where
  skipDeclIdIfPresent (stx : Syntax) : Syntax :=
    if stx.isOfKind `Lean.Parser.Command.declId then
      stx[0]
    else
      stx

  matchesUnusedPattern (stx : Syntax) (_ : SyntaxStack) :=
    stx.getId.toString.startsWith "_"
  isTopLevelDecl (constDecls : HashSet String.Range) (stx : Syntax) (stack : SyntaxStack) := Id.run <| do
    let stx := skipDeclIdIfPresent stx
    let some declRange := stx.getRange?
      | false
    constDecls.contains declRange &&
    !stackMatches stack [`Lean.Parser.Term.letIdDecl]
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

builtin_initialize addLinter unusedVariables

end Lean.Linter
