import Lean.Elab.Command
import Lean.Linter.Util

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

abbrev IgnoreFunction := Syntax → Syntax.Stack → Options → Bool

builtin_initialize builtinUnusedVariablesIgnoreFnsRef : IO.Ref <| Array IgnoreFunction ← IO.mkRef #[]

def addBuiltinUnusedVariablesIgnoreFn (ignoreFn : IgnoreFunction) : IO Unit := do
  (← builtinUnusedVariablesIgnoreFnsRef.get) |> (·.push ignoreFn) |> builtinUnusedVariablesIgnoreFnsRef.set


-- is variable
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
    stack.matches [`null, none, `null, ``Lean.Parser.Command.variable])

-- is in structure
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, ``Lean.Parser.Command.structure])

-- is in inductive
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, none, ``Lean.Parser.Command.inductive] &&
  (stack.get? 3 |>.any fun (stx, pos) =>
    pos == 0 &&
    [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·)))

-- in in constructor or structure binder
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, ``Lean.Parser.Command.optDeclSig, none] &&
  (stack.get? 4 |>.any fun (stx, _) =>
    [``Lean.Parser.Command.ctor, ``Lean.Parser.Command.structSimpleBinder].any (stx.isOfKind ·)))

-- is in opaque or axiom
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, ``Lean.Parser.Command.declSig, none] &&
  (stack.get? 4 |>.any fun (stx, _) =>
    [``Lean.Parser.Command.opaque, ``Lean.Parser.Command.axiom].any (stx.isOfKind ·)))

-- is in definition with foreign definition
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, none, `null, none, none, ``Lean.Parser.Command.declaration] &&
  (stack.get? 3 |>.any fun (stx, _) =>
    stx.isOfKind ``Lean.Parser.Command.optDeclSig ||
    stx.isOfKind ``Lean.Parser.Command.declSig) &&
  (stack.get? 5 |>.any fun (stx, _) => match stx[0] with
    | `(Lean.Parser.Command.declModifiersT| $[$_:docComment]? @[$[$attrs:attr],*] $[$vis]? $[noncomputable]?) =>
      attrs.any (fun attr => attr.raw.isOfKind ``Parser.Attr.extern || attr matches `(attr| implemented_by $_))
    | _ => false))

-- is in dependent arrow
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack _ =>
  stack.matches [`null, ``Lean.Parser.Term.explicitBinder, ``Lean.Parser.Term.depArrow])

-- is in let declaration
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  stack.matches [`null, none, `null, ``Lean.Parser.Term.letIdDecl, none] &&
  (stack.get? 3 |>.any fun (_, pos) => pos == 1) &&
  (stack.get? 5 |>.any fun (stx, _) => !stx.isOfKind ``Lean.Parser.Command.whereStructField))

-- is in declaration signature
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  stack.matches [`null, none, `null, none] &&
  (stack.get? 3 |>.any fun (stx, pos) =>
    pos == 0 &&
    [``Lean.Parser.Command.optDeclSig, ``Lean.Parser.Command.declSig].any (stx.isOfKind ·)))

-- is in function definition
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesFunArgs opts &&
  (stack.matches [`null, ``Lean.Parser.Term.basicFun] ||
  stack.matches [``Lean.Parser.Term.typeAscription, `null, ``Lean.Parser.Term.basicFun]))

-- is pattern variable
builtin_initialize addBuiltinUnusedVariablesIgnoreFn (fun _ stack opts =>
  !getLinterUnusedVariablesPatternVars opts &&
  stack.any fun (stx, pos) =>
    (stx.isOfKind ``Lean.Parser.Term.matchAlt && pos == 1) ||
    (stx.isOfKind ``Lean.Parser.Tactic.inductionAltLHS && pos == 2))

builtin_initialize unusedVariablesIgnoreFnsExt : SimplePersistentEnvExtension Name Unit ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun _ _ => ()
    addImportedFn := fun _ => ()
  }

builtin_initialize
  registerBuiltinAttribute {
    name  := `unused_variables_ignore_fn
    descr := "Marks a function of type `Lean.Linter.IgnoreFunction` for suppressing unused variable warnings"
    add   := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute 'unused_variables_ignore_fn', must be global"
      unless (← getConstInfo decl).type.isConstOf ``IgnoreFunction do
        throwError "invalid attribute 'unused_variables_ignore_fn', must be of type `Lean.Linter.IgnoreFunction`"
      let env ← getEnv
      setEnv <| unusedVariablesIgnoreFnsExt.addEntry env decl
  }

unsafe def getUnusedVariablesIgnoreFnsImpl : CommandElabM (Array IgnoreFunction) := do
  let ents := unusedVariablesIgnoreFnsExt.getEntries (← getEnv)
  let ents ← ents.mapM (evalConstCheck IgnoreFunction ``IgnoreFunction)
  return (← builtinUnusedVariablesIgnoreFnsRef.get) ++ ents

@[implemented_by getUnusedVariablesIgnoreFnsImpl]
opaque getUnusedVariablesIgnoreFns : CommandElabM (Array IgnoreFunction)

namespace UnusedVariables

abbrev ObjectSet := IO.Ref (HashSet USize)

unsafe def ObjectSet.insertImpl {α : Type} (s : ObjectSet) (a : α) : IO Bool := do
  if (← s.get).contains (ptrAddrUnsafe a) then
    return false
  s.modify fun s => s.insert (ptrAddrUnsafe a)
  return true

@[implemented_by ObjectSet.insertImpl]
opaque ObjectSet.insert {α : Type} (s : ObjectSet) (a : α) : IO Bool

unsafe def insertObjImpl {α : Type} (set : IO.Ref (HashSet USize)) (a : α) : IO Bool := do
  if (← set.get).contains (ptrAddrUnsafe a) then
    return false
  set.modify (·.insert (ptrAddrUnsafe a))
  return true

@[implemented_by insertObjImpl]
opaque insertObj {α : Type} (set : IO.Ref (HashSet USize)) (a : α) : IO Bool

partial def visitAssignments (set : IO.Ref (HashSet USize))
    (fvarUses : IO.Ref (HashSet FVarId))
    (assignments : Array (PersistentHashMap MVarId Expr)) : IO Unit := do
  MonadCacheT.run do
    for assignment in assignments do
      visitNode assignment.root
where
  visitNode node : MonadCacheT Expr Unit IO Unit := do
    if ← insertObj set node then
      match node with
      | .entries entries => for e in entries do visitEntry e
      | .collision _ vs _ => for e in vs do visitExpr e
  visitEntry e : MonadCacheT Expr Unit IO Unit := do
    if ← insertObj set e then
      match e with
      | .entry _ e => visitExpr e
      | .ref node => visitNode node
      | .null => pure ()
  visitExpr e : MonadCacheT Expr Unit IO Unit := do
    if ← insertObj set e then
      ForEachExpr.visit (e := e) fun e => do
        match e with
        | .fvar id => fvarUses.modify (·.insert id); return false
        | _ => return e.hasFVar

partial def followAliases (aliases : HashMap FVarId FVarId) (x : FVarId) : FVarId :=
  match aliases.find? x with
  | none => x
  | some y => followAliases aliases y

structure FVarDefinition where
  userName : Name
  stx : Syntax
  opts : Options
  aliases : Array FVarId

structure References where
  constDecls : HashSet String.Range := .empty
  fvarDefs : HashMap String.Range FVarDefinition := .empty
  fvarUses : HashSet FVarId := .empty
  fvarAliases : HashMap FVarId FVarId := .empty
  assignments : Array (PersistentHashMap MVarId Expr) := #[]

def collectReferences (infoTrees : Array Elab.InfoTree) (cmdStxRange : String.Range) :
    StateRefT References IO Unit := do
  for tree in infoTrees do
    tree.visitM' (preNode := fun ci info _ => do
      match info with
      | .ofTermInfo ti =>
        match ti.expr with
        | .const .. =>
          if ti.isBinder then
            let some range := info.range? | return
            let .original .. := info.stx.getHeadInfo | return -- we are not interested in canonical syntax here
            modify fun s => { s with constDecls := s.constDecls.insert range }
        | .fvar id .. =>
          let some range := info.range? | return
          let .original .. := info.stx.getHeadInfo | return -- we are not interested in canonical syntax here
          if ti.isBinder then
            let some ldecl := ti.lctx.find? id | return
            if !cmdStxRange.contains range.start || ldecl.userName.hasMacroScopes then return
            let opts := ci.options
            if !getLinterUnusedVariables opts then return
            let stx := skipDeclIdIfPresent info.stx
            if let .str _ s := stx.getId then
              if s.startsWith "_" then return
            modify fun s =>
              if let some ref := s.fvarDefs.find? range then
                { s with fvarDefs := s.fvarDefs.insert range { ref with aliases := ref.aliases.push id } }
              else
                { s with fvarDefs := s.fvarDefs.insert range { userName := ldecl.userName, stx, opts, aliases := #[id] } }
          else
            modify fun s => { s with fvarUses := s.fvarUses.insert id }
        | _ => pure ()
      | .ofTacticInfo ti =>
        modify fun s => { s with assignments := s.assignments.push ti.mctxAfter.eAssignment }
      | .ofFVarAliasInfo i =>
        modify fun s =>
          let id := followAliases s.fvarAliases i.baseId
          { s with fvarAliases := s.fvarAliases.insert i.id id }
      | _ => pure ())
where
  skipDeclIdIfPresent (stx : Syntax) : Syntax :=
    if stx.isOfKind ``Lean.Parser.Command.declId then
      stx[0]
    else
      stx

def unusedVariables : Linter where
  run cmdStx := do
    unless getLinterUnusedVariables (← getOptions) do
      return

    -- NOTE: `messages` is local to the current command
    if (← get).messages.hasErrors then
      return

    let some cmdStxRange := cmdStx.getRange?
      | return

    let infoTrees := (← get).infoState.trees.toArray

    if (← infoTrees.anyM (·.hasSorry)) then
      return

    -- collect references
    let (_, s) ← (collectReferences infoTrees cmdStxRange).run {}

    if s.fvarDefs.isEmpty then return

    let fvarAliases : HashMap FVarId FVarId := s.fvarAliases.fold (init := {}) fun m id baseId =>
      m.insert id (followAliases s.fvarAliases baseId)

    let fvarUsesRef ← IO.mkRef <| fvarAliases.fold (init := s.fvarUses) fun fvarUses id baseId =>
      if fvarUses.contains id then fvarUses.insert baseId else fvarUses

    -- -- collect ignore functions
    let ignoreFns ← getUnusedVariablesIgnoreFns

    -- determine unused variables
    let mut initializedMVars := false
    let mut unused := #[]
    for (range, { userName, stx := declStx, opts, aliases }) in s.fvarDefs.toArray do
      let fvarUses ← fvarUsesRef.get
      if aliases.any fun id => fvarUses.contains (fvarAliases.findD id id) then continue
      if s.constDecls.contains range then continue

      -- evaluate ignore functions on original syntax
      let some ((id', _) :: stack) := cmdStx.findStack? (·.getRange?.any (·.includes range))
        | continue

      if id'.isIdent && ignoreFns.any (· declStx stack opts) then continue

      -- evaluate ignore functions on macro expansion outputs
      if ← infoTrees.anyM fun tree => do
        let some macroExpansions ← collectMacroExpansions? range tree | return false
        return macroExpansions.any fun expansion =>
          -- in a macro expansion, there may be multiple leafs whose (synthetic) range
          -- includes `range`, so accept strict matches only
          if let some (_ :: stack) :=
            expansion.output.findStack?
              (·.getRange?.any (·.includes range))
              (fun stx => stx.isIdent && stx.getRange?.any (· == range))
          then
            ignoreFns.any (· declStx stack opts)
          else
            false
      then
        continue

      if !initializedMVars then
        visitAssignments (← IO.mkRef {}) fvarUsesRef s.assignments
        initializedMVars := true
        let fvarUses ← fvarUsesRef.get
        if aliases.any fun id => fvarUses.contains (fvarAliases.findD id id) then continue

      -- publish warning if variable is unused and not ignored
      unused := unused.push (declStx, userName)

    for (declStx, userName) in unused.qsort (·.1.getPos?.get! < ·.1.getPos?.get!) do
      logLint linter.unusedVariables declStx m!"unused variable `{userName}`"

builtin_initialize addLinter unusedVariables

end UnusedVariables
end Linter

def MessageData.isUnusedVariableWarning (msg : MessageData) : Bool :=
  msg.hasTag (· == Linter.linter.unusedVariables.name)
