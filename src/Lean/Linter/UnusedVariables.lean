import Lean.Elab.Command
import Lean.Linter.Util
import Lean.Elab.InfoTree
import Lean.Server.InfoUtils
import Lean.Server.References
import Std.Data.HashMap

namespace Lean.Linter
open Lean.Elab.Command Lean.Server Std

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

def getLinterUnusedVariables (o : Options) : Bool := getLinterValue linter.unusedVariables o
def getLinterUnusedVariablesFunArgs (o : Options) : Bool := o.get linter.unusedVariables.funArgs.name (getLinterUnusedVariables o)
def getLinterUnusedVariablesPatternVars (o : Options) : Bool := o.get linter.unusedVariables.patternVars.name (getLinterUnusedVariables o)


builtin_initialize builtinUnusedVariablesIgnoreFnsRef : IO.Ref <| Array IgnoreFunction ← IO.mkRef #[]

def addBuiltinUnusedVariablesIgnoreFn (ignoreFn : IgnoreFunction) : IO Unit := do
  (← builtinUnusedVariablesIgnoreFnsRef.get) |> (·.push ignoreFn) |> builtinUnusedVariablesIgnoreFnsRef.set


-- matches builtinUnused variable pattern
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun stx _ _ =>
    stx.getId.toString.startsWith "_")

-- is variable
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
    stackMatches stack [`null, none, `null, ``Lean.Parser.Command.variable])

-- is in structure
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stackMatches stack [`null, none, `null, ``Lean.Parser.Command.structure])

-- is in inductive
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stackMatches stack [`null, none, `null, none, ``Lean.Parser.Command.inductive] &&
  (stack.get? 3 |>.any fun (stx, pos) =>
    pos == 0 &&
    [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·)))

-- in in constructor or structure binder
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stackMatches stack [`null, none, `null, ``Lean.Parser.Command.optDeclSig, none] &&
  (stack.get? 4 |>.any fun (stx, _) =>
    [``Lean.Parser.Command.ctor, ``Lean.Parser.Command.structSimpleBinder].any (stx.isOfKind ·)))

-- is in opaque or axiom
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stackMatches stack [`null, none, `null, ``Lean.Parser.Command.declSig, none] &&
  (stack.get? 4 |>.any fun (stx, _) =>
    [``Lean.Parser.Command.opaque, ``Lean.Parser.Command.axiom].any (stx.isOfKind ·)))

-- is in definition with foreign definition
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stackMatches stack [`null, none, `null, none, none, ``Lean.Parser.Command.declaration] &&
  (stack.get? 3 |>.any fun (stx, _) =>
    stx.isOfKind ``Lean.Parser.Command.optDeclSig ||
    stx.isOfKind ``Lean.Parser.Command.declSig) &&
  (stack.get? 5 |>.any fun (stx, _) => match stx[0] with
    | `(Lean.Parser.Command.declModifiersT| $[$_:docComment]? @[$[$attrs:attr],*] $[$vis]? $[noncomputable]?) =>
      attrs.any (fun attr => attr.raw.isOfKind ``Parser.Attr.extern || attr matches `(attr| implementedBy $_))
    | _ => false))

-- is in dependent arrow
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stackMatches stack [`null, ``Lean.Parser.Term.explicitBinder, ``Lean.Parser.Term.depArrow])

-- is in let declaration
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  stackMatches stack [`null, none, `null, ``Lean.Parser.Term.letIdDecl, none] &&
  (stack.get? 3 |>.any fun (_, pos) => pos == 1) &&
  (stack.get? 5 |>.any fun (stx, _) => !stx.isOfKind ``Lean.Parser.Command.whereStructField))

-- is in declaration signature
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  stackMatches stack [`null, none, `null, none] &&
  (stack.get? 3 |>.any fun (stx, pos) =>
    pos == 0 &&
    [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·)))

-- is in function definition
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  (stackMatches stack [`null, ``Lean.Parser.Term.basicFun] ||
  stackMatches stack [`null, ``Lean.Parser.Term.paren, `null, ``Lean.Parser.Term.basicFun]))

-- is pattern variable
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesPatternVars opts &&
  stack.any fun (stx, pos) =>
    (stx.isOfKind ``Lean.Parser.Term.matchAlt && pos == 1) ||
    (stx.isOfKind ``Lean.Parser.Tactic.inductionAltLHS && pos == 2))


builtin_initialize unusedVariablesIgnoreFnsExt : SimplePersistentEnvExtension Name Unit ←
  registerSimplePersistentEnvExtension {
    name          := `unusedVariablesIgnoreFns
    addEntryFn    := fun _ _ => ()
    addImportedFn := fun _ => ()
  }

builtin_initialize
  registerBuiltinAttribute {
    name  := `unusedVariablesIgnoreFn
    descr := "Marks a function of type `Lean.Linter.IgnoreFunction` for suppressing unused variable warnings"
    add   := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute 'unusedVariablesIgnoreFn', must be global"
      unless (← getConstInfo decl).type.isConstOf ``IgnoreFunction do
        throwError "invalid attribute 'unusedVariablesIgnoreFn', must be of type `Lean.Linter.IgnoreFunction`"
      let env ← getEnv
      setEnv <| unusedVariablesIgnoreFnsExt.addEntry env decl
  }

unsafe def getUnusedVariablesIgnoreFnsImpl : CommandElabM (Array IgnoreFunction) := do
  let ents := unusedVariablesIgnoreFnsExt.getEntries (← getEnv)
  let ents ← ents.mapM (evalConstCheck IgnoreFunction ``IgnoreFunction)
  return (← builtinUnusedVariablesIgnoreFnsRef.get) ++ ents

@[implementedBy getUnusedVariablesIgnoreFnsImpl]
opaque getUnusedVariablesIgnoreFns : CommandElabM (Array IgnoreFunction)


def unusedVariables : Linter := fun cmdStx => do
  unless getLinterUnusedVariables (← getOptions) do
    return

  -- NOTE: `messages` is local to the current command
  if (← get).messages.hasErrors then
    return

  let some cmdStxRange := cmdStx.getRange?
    | pure ()

  let infoTrees := (← get).infoState.trees.toArray
  let fileMap := (← read).fileMap

  if (← infoTrees.anyM (·.hasSorry)) then
    return

  -- collect references
  let refs := findModuleRefs fileMap infoTrees (allowSimultaneousBinderUse := true)

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

  -- collect ignore functions
  let ignoreFns := (← getUnusedVariablesIgnoreFns)
    |>.insertAt 0 (isTopLevelDecl constDecls)

  -- determine unused variables
  for (id, ⟨decl?, uses⟩) in vars.toList do
    -- process declaration
    let some decl := decl?
      | continue
    let declStx := skipDeclIdIfPresent decl.stx
    let some range := declStx.getRange?
      | continue
    let some localDecl := decl.info.lctx.find? id
      | continue
    if !cmdStxRange.contains range.start || localDecl.userName.hasMacroScopes then
      continue

    -- check if variable is used
    if !uses.isEmpty || tacticFVarUses.contains id || decl.aliases.any (match · with | .fvar id => tacticFVarUses.contains id | _ => false) then
        continue

    -- check linter options
    let opts := decl.ci.options
    if !getLinterUnusedVariables opts then
      continue

    -- evaluate ignore functions on original syntax
    if let some stack := findSyntaxStack? cmdStx declStx then
      if ignoreFns.any (· declStx stack opts) then
        continue
    else
      continue

    -- evaluate ignore functions on macro expansion outputs
    if ← infoTrees.anyM fun tree => do
      if let some macroExpansions ← collectMacroExpansions? range tree then
        return macroExpansions.any fun expansion =>
          if let some stack := findSyntaxStack? expansion.output declStx then
            ignoreFns.any (· declStx stack opts)
          else
            false
      else
        return false
    then
      continue

    -- publish warning if variable is unused and not ignored
    publishMessage (.tagged decl_name%
      m!"unused variable `{localDecl.userName}` [linter.unusedVariables]") range

  return ()
where
  skipDeclIdIfPresent (stx : Syntax) : Syntax :=
    if stx.isOfKind ``Lean.Parser.Command.declId then
      stx[0]
    else
      stx
  isTopLevelDecl (constDecls : HashSet String.Range) : IgnoreFunction := fun stx stack _ => Id.run <| do
    let some declRange := stx.getRange?
      | false
    constDecls.contains declRange &&
    !stackMatches stack [``Lean.Parser.Term.letIdDecl]

builtin_initialize addLinter unusedVariables

end Linter

def MessageData.isUnusedVariableWarning (msg : MessageData) : Bool :=
  msg.hasTag (· == ``Linter.unusedVariables)
