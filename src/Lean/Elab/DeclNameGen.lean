/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Elab.Command

/-!
# Name generator for declarations

This module provides functionality to generate a name for a declaration using its binders and its type.
This is used to generate names for anonymous instances.

It uses heuristics to generate an informative but terse name given its namespace, supplied binders, and type.
It tries to make these relatively unique,
and it uses suffixes derived from the module to ensure cross-project uniqueness
when the instance doesn't refer to anything defined in the current project.

The name generator can be thought of as a kind of pretty printer, rendering an expression in textual form.
The general structure of this generator is
1. `Lean.Elab.Command.NameGen.winnowExpr` takes an expression and re-uses `Expr` as a data structure
   to record the "Syntax"-like structure.
2. `Lean.Elab.Command.NameGen.mkBaseNameCore` formats the result of that as a string.
   It actually does a bit more computation than that, since it further removes duplicate expressions,
   reporting only the first occurrence of each subexpression.
-/

namespace Lean.Elab.Command

open Meta

namespace NameGen

/--
If `e` is an application of a projection to a parent structure, returns the term being projected.
-/
private def getParentProjArg (e : Expr) : MetaM (Option Expr) := do
  let .const c@(.str _ field) _ := e.getAppFn | return none
  let env ← getEnv
  let some info := env.getProjectionFnInfo? c | return none
  unless e.getAppNumArgs == info.numParams + 1 do return none
  let some (.ctorInfo cVal) := env.find? info.ctorName | return none
  if isSubobjectField? env cVal.induct (Name.mkSimple field) |>.isNone then return none
  return e.appArg!

/--
Strips out universes and arguments we decide are unnecessary for naming.
The resulting expression can have loose fvars and be mangled in other ways.
Expressions can also be replaced by `.bvar 0` if they shouldn't be mentioned.
-/
private partial def winnowExpr (e : Expr) : MetaM Expr := do
  let rec visit (e : Expr) : MonadCacheT Expr Expr MetaM Expr := checkCache e fun _ => do
    if ← isProof e then
      return .bvar 0
    match e with
    | .app .. =>
      if let some e' ← getParentProjArg e then
        return (← visit e')
      e.withApp fun f args => do
        -- Visit only the explicit arguments to `f` and also its type (and type family) arguments.
        -- The reason we visit type arguments is so that, for example, `Decidable (_ < _)` has
        -- a chance to insert type information. Type families are for reporting things such as type constructors and monads.
        let mut fty ← inferType f
        let mut j := 0
        let mut e' ← visit f
        for h : i in [0:args.size] do
          unless fty.isForall do
            fty ← withTransparency .all <| whnf <| fty.instantiateRevRange j i args
            j := i
          let .forallE _ _ fty' bi := fty | failure
          fty := fty'
          let arg := args[i]
          if ← pure bi.isExplicit <||> (pure !arg.isSort <&&> isTypeFormer arg) then
            unless (← isProof arg) do
              e' := .app e' (← visit arg)
        return e'
    | .forallE n ty body bi =>
      withLocalDecl n bi ty fun arg => do
        -- In a dependent forall the body implies `ty`, so we won't mention it.
        let ty' ← if body.hasLooseBVars then pure (.bvar 0) else visit ty
        return .forallE n ty' (← visit (body.instantiate1 arg)) bi
    | .lam n ty body bi =>
      if let some e := Expr.etaExpandedStrict? e then
        visit e
      else
        withLocalDecl n bi ty fun arg => do
          -- Don't record the `.lam` since `ty` should be recorded elsewhere in the expression.
          visit (body.instantiate1 arg)
    | .letE _n _t v b _ => visit (b.instantiate1 v)
    | .sort .. =>
      if e.isProp then return .sort levelZero
      else if e.isType then return .sort levelOne
      else return .sort (.param `u)
    | .const name .. => return .const name []
    | .mdata _ e' => visit e'
    | _ => return .bvar 0
  visit e |>.run

/--
State for name generation.
-/
private structure MkNameState where
  /-- Keeps track of expressions already visited so that we do not include them again. -/
  seen : ExprSet := {}
  /-- Keeps track of constants that appear in the generated name. -/
  consts : NameSet := {}

/--
Monad for name generation.
-/
private abbrev MkNameM := StateRefT MkNameState MetaM

/--
Core algorithm for generating a name. The provided expression should be a winnowed expression.

- `omitTopForall` if true causes "Forall" to not be included if the binding type results in an empty string.
-/
private def mkBaseNameCore (e : Expr) (omitTopForall : Bool := false) : MkNameM String :=
  visit e omitTopForall
where
  visit (e : Expr) (omitTopForall : Bool := false) : MkNameM String := do
    if (← get).seen.contains e then
      return ""
    else
      let s ← visit' e omitTopForall
      modify fun st => {st with seen := st.seen.insert e}
      return s
  visit' (e : Expr) (omitTopForall : Bool) : MkNameM String := do
    match e with
    | .const name .. =>
      modify (fun st => {st with consts := st.consts.insert name})
      return match name.eraseMacroScopes with
              | .str _ str => str.capitalize
              | _ => ""
    | .app f x => (· ++ ·) <$> visit f <*> visit x
    | .forallE _ ty body _ =>
      let sty ← visit ty
      if omitTopForall && sty == "" then
        visit body true
      else
        ("Forall" ++ sty ++ ·) <$> visit body
    | .sort .zero => return "Prop"
    | .sort (.succ _) => return "Type"
    | .sort _ => return "Sort"
    | _ => return ""

/--
Generate a name, while naming the top-level foralls using "Of".
The provided expression should be a winnowed expression.
-/
private partial def mkBaseNameAux (e : Expr) : MkNameM String := do
  let (foralls, sb) ← visit e
  return sb ++ String.join foralls
where
  visit (e : Expr) : MkNameM (List String × String) := do
    match e with
    | .forallE _ ty body _ =>
      let (foralls, sb) ← visit body
      let st ← mkBaseNameCore ty (omitTopForall := true)
      if st == "" then
        return (foralls, sb)
      else
        return (("Of" ++ st) :: foralls, sb)
    | _ => return ([], ← mkBaseNameCore e)

/--
Adds all prefixes of `ns` as seen constants.
-/
private def visitNamespace (ns : Name) : MkNameM Unit := do
  match ns with
  | .anonymous => pure ()
  | .num ns' _ => visitNamespace ns'
  | .str ns' _ =>
    let env ← getEnv
    if env.contains ns then
      modify fun st => {st with seen := st.seen.insert (.const ns []), consts := st.consts.insert ns}
    visitNamespace ns'

/--
Given an expression, generates a "base name" for a declaration.
The top-level foralls in `e` are treated as being binders, so use the `...Of...` naming convention.
The current namespace is used to seed the seen expressions with each prefix of the namespace that's a global constant.

Collects all constants that contribute to the name in the `MkInstM` state.
This can be used to decide whether to further transform the generated name;
in particular, this enables checking whether the generated name mentions declarations
from the current module or project.
-/
def mkBaseName (e : Expr) : MkNameM String := do
  let e ← instantiateMVars e
  visitNamespace (← getCurrNamespace)
  mkBaseNameAux (← winnowExpr e)

/--
Converts a module name into a suffix. Includes a leading `_`,
so for example `Lean.Elab.DefView` becomes `_lean_elab_defView`.
-/
private def moduleToSuffix : Name → String
  | .anonymous => ""
  | .num n _ => moduleToSuffix n
  | .str n s => moduleToSuffix n ++ "_" ++ s.decapitalize

/--
Uses heuristics to generate an informative but terse base name for a term of the given type, using `mkBaseName`.
Makes use of the current namespace.
It tries to make these names relatively unique ecosystem-wide,
and it adds suffixes using the current module if the resulting name doesn't refer to anything defined in this module.

If any constant in `type` has a name with macro scopes, then the result will be a name with fresh macro scopes.
While in this case we could skip the naming heuristics, we still want informative names for debugging purposes.
-/
def mkBaseNameWithSuffix (pre : String) (type : Expr) : MetaM Name := do
  let (name, st) ← mkBaseName type |>.run {}
  let name := pre ++ name
  let project := (← getMainModule).getRoot
  -- Collect the modules for each constant that appeared.
  let modules ← st.consts.foldM (init := Array.mkEmpty st.consts.size) fun mods name => return mods.push (← findModuleOf? name)
  -- We can avoid adding the suffix if the instance refers to module-local names.
  let isModuleLocal := modules.any Option.isNone
  -- We can also avoid adding the full module suffix if the instance refers to "project"-local names.
  let isProjectLocal := isModuleLocal || modules.any fun mod? => mod?.map (·.getRoot) == project
  let name := Name.mkSimple <|
    if !isProjectLocal then
      s!"{name}{moduleToSuffix project}"
    else
      name
  if Option.isSome <| type.find? (fun e => if let .const n _ := e then n.hasMacroScopes else false) then
    mkFreshUserName name
  else
    return name

/--
Elaborates the binders and type and then uses `mkBaseNameWithSuffix` to generate a name.
Furthermore, uses `mkUnusedBaseName` on the result.
-/
def mkBaseNameWithSuffix' (pre : String) (binders : Array Syntax) (type : Syntax) : TermElabM Name := do
  let name ←
    try
      Term.withAutoBoundImplicit <| Term.elabBinders binders fun binds => Term.withoutErrToSorry do
        let ty ← mkForallFVars binds (← Term.elabType type)
        mkBaseNameWithSuffix pre ty
    catch _ =>
      mkFreshUserName <| Name.mkSimple pre
  liftMacroM <| mkUnusedBaseName name

end NameGen

/--
Generates an instance name for a declaration that has the given binders and type.
It tries to make these names relatively unique ecosystem-wide.

Note that this elaborates the binders and the type.
This means that when elaborating an instance declaration, we elaborate these twice.
-/
def mkInstanceName (binders : Array Syntax) (type : Syntax) : CommandElabM Name := do
  let savedState ← get
  try
    -- Unfortunately we can't include any of the binders from `runTermElabM` since, without
    -- elaborating the body of the instance, we have no idea which of these binders are
    -- actually used.
    runTermElabM fun _ => NameGen.mkBaseNameWithSuffix' "inst" binders type
  finally
    set savedState
