/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.ForEachExpr
import Lean.Elab.Command
import Lean.Elab.DeclUtil
import Lean.Meta.CollectFVars

namespace Lean.Elab

inductive DefKind where
  | def | theorem | example | opaque | abbrev
  deriving Inhabited, BEq

def DefKind.isTheorem : DefKind → Bool
  | .theorem => true
  | _        => false

def DefKind.isDefOrAbbrevOrOpaque : DefKind → Bool
  | .def    => true
  | .opaque => true
  | .abbrev => true
  | _       => false

def DefKind.isExample : DefKind → Bool
  | .example => true
  | _        => false

structure DefView where
  kind          : DefKind
  ref           : Syntax
  modifiers     : Modifiers
  declId        : Syntax
  binders       : Syntax
  type?         : Option Syntax
  value         : Syntax
  deriving?     : Option (Array Syntax) := none
  deriving Inhabited

def DefView.isInstance (view : DefView) : Bool :=
  view.modifiers.attrs.any fun attr => attr.name == `instance

namespace Command
open Meta

def mkDefViewOfAbbrev (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "abbrev " >> declId >> optDeclSig >> declVal
  let (binders, type) := expandOptDeclSig stx[2]
  let modifiers       := modifiers.addAttribute { name := `inline }
  let modifiers       := modifiers.addAttribute { name := `reducible }
  { ref := stx, kind := DefKind.abbrev, modifiers,
    declId := stx[1], binders, type? := type, value := stx[3] }

def mkDefViewOfDef (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "def " >> declId >> optDeclSig >> declVal >> optDefDeriving
  let (binders, type) := expandOptDeclSig stx[2]
  let deriving? := if stx[4].isNone then none else some stx[4][1].getSepArgs
  { ref := stx, kind := DefKind.def, modifiers,
    declId := stx[1], binders, type? := type, value := stx[3], deriving? }

def mkDefViewOfTheorem (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "theorem " >> declId >> declSig >> declVal
  let (binders, type) := expandDeclSig stx[2]
  { ref := stx, kind := DefKind.theorem, modifiers,
    declId := stx[1], binders, type? := some type, value := stx[3] }

/--
State for `mkInstanceNameFromExpr`.
-/
private structure MkInstState where
  /-- Keeps track of name parts that have already appeared in the generated name. -/
  nameParts : HashSet String := {}
  /-- Keeps track of constants that appear in the generated name. -/
  consts : NameSet := {}

/--
Monad for `mkInstanceNameFromExpr`.
-/
private abbrev MkInstM := StateRefT MkInstState MetaM

/--
Collect the binder infos for each argument supplied to `f`.
-/
private partial def getBinderInfos (f : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
  try
    withTransparency TransparencyMode.all do
      forallBoundedTelescope (← inferType f) args.size fun xs _ => do
        let bis ← xs.mapM fun arg => arg.fvarId!.getBinderInfo
        if xs.isEmpty || xs.size == args.size then
          return bis
        else
          return bis ++ (← getBinderInfos (mkAppN f $ args.shrink xs.size) (args.extract xs.size args.size))
  catch _ =>
    return #[]

/--
Uses heuristics to generate an informative but terse name for an instance given its namespace, supplied binders, and class expression.
It tries to make these relatively unique.
-/
private partial def mkInstanceNameFromExpr (binders : Array Expr) (e : Expr) : MkInstM String := do
  let e ← instantiateMVars e
  visitNamespace (← getCurrNamespace)
  let mut s ← go e
  let fvars := (collectFVars {} e).fvarSet
  for binder in binders do
    -- Only mention binders that aren't implied by `e`.
    unless fvars.contains binder.fvarId! do
      let s' ← go (← inferType binder)
      s := if s'.isEmpty then s else s!"{s}Of{s'}"
  return "inst" ++ s
where
  /--
  Intitializes the seen strings and seen constants from the parts of the current namespace.
  The theory here is that the namespace parts correspond to types that the instance is about.
  -/
  visitNamespace (ns : Name) : MkInstM Unit :=
    match ns with
    | .str ns' s => modify (fun st => {st with nameParts := st.nameParts.insert s, consts := st.consts.insert ns}) *> visitNamespace ns'
    | .num ns' _ => visitNamespace ns'
    | .anonymous => pure ()
  /--
  Generates a name for `e`, but returns "" if this expression generates a string that has already been generated.
  This cuts down on unnecessary duplication, though it is potentially too severe.
  -/
  go (e : Expr) : MkInstM String := do
    let strings := (← get).nameParts
    let s ← go' e
    modify (fun st => {st with nameParts := st.nameParts.insert s})
    return if strings.contains s then "" else s
  /--
  Core function that generates a name for `e`.
  -/
  go' (e : Expr) : MkInstM String := do
    match e with
    | .app .. =>
      if let .const name .. := e.getAppFn then
        -- Record the head constant even if `getParentProjArg` applies.
        modify (fun st => {st with consts := st.consts.insert name})
      if let some e' ← getParentProjArg e then
        return (← go' e')
      e.withApp fun f args => do
        -- Visit only the explicit arguments to `f` and also its type arguments.
        -- The reason we visit type arguments is so that, for example, `Decidable (_ < _)` has
        -- a chance to insert type information.
        let bis ← getBinderInfos f args
        let mut s ← go f
        for arg in args, bi in bis do
          let isTy ← Meta.isType arg
          if bi.isExplicit || (isTy && !arg.isSort) then
            s := s ++ (← go arg)
        return s
    | .forallE n ty body bi =>
      withLocalDecl n bi ty fun arg => do
        let sty ← go ty
        let sbody ← go (body.instantiate1 arg)
        return "Forall" ++ sty ++ sbody
    | .lam n ty body bi =>
      if let some e := Expr.etaExpandedStrict? e then
        go' e
      else
        withLocalDecl n bi ty fun arg => go (body.instantiate1 arg)
    | .sort .. =>
      if e.isProp then return "Prop"
      else if e.isType then return "Type"
      else return "Sort"
    | .const name .. =>
      modify (fun st => {st with consts := st.consts.insert name})
      return match name with
              | .str _ str => str.capitalize
              | _ => ""
    | .mdata _ e' => go' e'
    | _ => return ""
  /--
  If `e` is an application of a projection to a parent structure, returns the term being projected.
  -/
  getParentProjArg (e : Expr) : MetaM (Option Expr) := do
    let .const c@(.str _ field) _ := e.getAppFn | return none
    let some info := (← getEnv).getProjectionFnInfo? c | return none
    if info.fromClass then return none
    unless e.getAppNumArgs == info.numParams + 1 do return none
    let some structName := (← getEnv).getProjectionStructureName? c | return none
    if (isSubobjectField? (← getEnv) structName field).isNone then return none
    return e.appArg!

/--
Generates a name for an instance with the given type.
Note that we elaborate the type twice. Once for producing the name, and another when elaborating the declaration.
-/
def mkInstanceName (binders : Array Syntax) (type : Syntax) : CommandElabM Name := do
  let savedState ← get
  let (name, isModuleLocal, isProjectLocal) ←
    try
      runTermElabM fun _ => Term.withAutoBoundImplicit <| Term.elabBinders binders fun binds => Term.withoutErrToSorry do
        let type ← Term.elabType type
        -- Unfortunately we can't include any of the binders from `runTermElabM` since, without
        -- elaborating the body of the instance, we have no idea which of these binders are
        -- actually used.
        forallTelescopeReducing type fun binds' type' => do
          let (name, st) ← mkInstanceNameFromExpr (binds ++ binds') type' |>.run {}
          -- We can avoid adding the module suffix if the instance refers to module-local names.
          let isModuleLocal ← st.consts.foldM (init := false) fun b name => pure b <||> do
            if (← getEnv).contains name then
              return (← findModuleOf? name).isNone
            return false
          let project := (← getMainModule).getRoot
          let isProjectLocal ← st.consts.foldM (init := false) fun b name => pure b <||> do
            if (← getEnv).contains name then
              return (← findModuleOf? name).map (·.getRoot == project) |>.getD true
            return false
          return (name, isModuleLocal, isProjectLocal)
    catch _ =>
      pure (s!"inst", false, false)
  set savedState
  let name' :=
    if !isProjectLocal then
      s!"{name}{nameToSuffix (← getMainModule)}"
    else if !isModuleLocal then
      s!"{name}{nameToSuffix (← getMainModule).getRoot}"
    else
      name
  liftMacroM <| mkUnusedBaseName <| Name.mkSimple name'
where
  nameToSuffix : Name → String
  | .anonymous => ""
  | .num n _ => nameToSuffix n
  | .str n s => nameToSuffix n ++ "_" ++ s

def mkDefViewOfInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
  -- leading_parser Term.attrKind >> "instance " >> optNamedPrio >> optional declId >> declSig >> declVal
  let attrKind        ← liftMacroM <| toAttributeKind stx[0]
  let prio            ← liftMacroM <| expandOptNamedPrio stx[2]
  let attrStx         ← `(attr| instance $(quote prio):num)
  let (binders, type) := expandDeclSig stx[4]
  let modifiers       := modifiers.addAttribute { kind := attrKind, name := `instance, stx := attrStx }
  let declId ← match stx[3].getOptional? with
    | some declId => pure declId
    | none        =>
      let id ← mkInstanceName binders.getArgs type
      pure <| mkNode ``Parser.Command.declId #[mkIdentFrom stx id, mkNullNode]
  return {
    ref := stx, kind := DefKind.def, modifiers := modifiers,
    declId := declId, binders := binders, type? := type, value := stx[5]
  }

def mkDefViewOfOpaque (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView := do
  -- leading_parser "opaque " >> declId >> declSig >> optional declValSimple
  let (binders, type) := expandDeclSig stx[2]
  let val ← match stx[3].getOptional? with
    | some val => pure val
    | none     =>
      let val ← if modifiers.isUnsafe then `(default_or_ofNonempty% unsafe) else `(default_or_ofNonempty%)
      `(Parser.Command.declValSimple| := $val)
  return {
    ref := stx, kind := DefKind.opaque, modifiers := modifiers,
    declId := stx[1], binders := binders, type? := some type, value := val
  }

def mkDefViewOfExample (modifiers : Modifiers) (stx : Syntax) : DefView :=
  -- leading_parser "example " >> declSig >> declVal
  let (binders, type) := expandOptDeclSig stx[1]
  let id              := mkIdentFrom stx `_example
  let declId          := mkNode ``Parser.Command.declId #[id, mkNullNode]
  { ref := stx, kind := DefKind.example, modifiers := modifiers,
    declId := declId, binders := binders, type? := type, value := stx[2] }

def isDefLike (stx : Syntax) : Bool :=
  let declKind := stx.getKind
  declKind == ``Parser.Command.abbrev ||
  declKind == ``Parser.Command.def ||
  declKind == ``Parser.Command.theorem ||
  declKind == ``Parser.Command.opaque ||
  declKind == ``Parser.Command.instance ||
  declKind == ``Parser.Command.example

def mkDefView (modifiers : Modifiers) (stx : Syntax) : CommandElabM DefView :=
  let declKind := stx.getKind
  if declKind == ``Parser.Command.«abbrev» then
    return mkDefViewOfAbbrev modifiers stx
  else if declKind == ``Parser.Command.def then
    return mkDefViewOfDef modifiers stx
  else if declKind == ``Parser.Command.theorem then
    return mkDefViewOfTheorem modifiers stx
  else if declKind == ``Parser.Command.opaque then
    mkDefViewOfOpaque modifiers stx
  else if declKind == ``Parser.Command.instance then
    mkDefViewOfInstance modifiers stx
  else if declKind == ``Parser.Command.example then
    return mkDefViewOfExample modifiers stx
  else
    throwError "unexpected kind of definition"

builtin_initialize registerTraceClass `Elab.definition

end Command
end Lean.Elab
