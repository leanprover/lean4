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
      isInStructure,
      isInLetDeclaration,
      isInDeclarationSignature,
      isInFun,
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
  isInStructure (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, `Lean.Parser.Command.structure]
  isInLetDeclaration (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, `Lean.Parser.Term.letIdDecl, none] &&
    (stack.get? 3 |>.any fun (_, pos) => pos == 1) &&
    (stack.get? 5 |>.any fun (stx, _) => !stx.isOfKind `Lean.Parser.Command.whereStructField)
  isInDeclarationSignature (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, none, `null, none] &&
    (stack.get? 3 |>.any fun (stx, pos) =>
      pos == 0 &&
      [`Lean.Parser.Command.optDeclSig, `Lean.Parser.Command.declSig].any (stx.isOfKind ·))
  isInFun (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, `Lean.Parser.Term.basicFun]
  isInDepArrow (_ : Syntax) (stack : SyntaxStack) :=
    stackMatches stack [`null, `Lean.Parser.Term.explicitBinder, `Lean.Parser.Term.depArrow]

builtin_initialize addLinter unusedVariables

end Lean.Linter
