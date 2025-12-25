/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Arthur Paulino, Gabriel Ebner
-/
import Lean.Util.CollectLevelParams
import Lean.Util.ForEachExpr
import Lean.Util.Recognizers
import Lean.Meta.Check
import Lean.Meta.ForEachExpr
import Lean.Meta.GlobalInstances
import Lean.DocString
import Lean.Linter.OtherLinter.Basic

open Lean Meta

namespace Std.Tactic.Lint

/-!
# Various linters

This file defines several small linters.
-/

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[std_linter] def dupNamespace : Linter where
  noErrorsFound := "No declarations have a duplicate namespace."
  errorsFound := "DUPLICATED NAMESPACES IN NAME:"
  test declName := do
    if ← isAutoDecl declName then return none
    if isGlobalInstance (← getEnv) declName then return none
    let nm := declName.components
    let some (dup, _) := nm.zip nm.tail! |>.find? fun (x, y) => x == y
      | return none
    return m!"The namespace {dup} is duplicated in the name"

/-- A linter for checking for unused arguments.
We skip all declarations that contain `sorry` in their value. -/
@[std_linter] def unusedArguments : Linter where
  noErrorsFound := "No unused arguments."
  errorsFound := "UNUSED ARGUMENTS."
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isProjectionFn declName then return none
    let info ← getConstInfo declName
    let ty := info.type
    let some val := info.value? | return none
    if val.hasSorry || ty.hasSorry then return none
    forallTelescope ty fun args ty => do
      let mut e := (mkAppN val args).headBeta
      e := mkApp e ty
      for arg in args do
        let ldecl ← getFVarLocalDecl arg
        e := mkApp e ldecl.type
        if let some val := ldecl.value? then
          e := mkApp e val
      let unused := args.zip (.range args.size) |>.filter fun (arg, _) =>
        !e.containsFVar arg.fvarId!
      if unused.isEmpty then return none
      addMessageContextFull <| .joinSep (← unused.toList.mapM fun (arg, i) =>
          return m!"argument {i+1} {arg} : {← inferType arg}") m!", "

/-- A linter for checking definition doc strings. -/
@[std_linter] def docBlame : Linter where
  noErrorsFound := "No definitions are missing documentation."
  errorsFound := "DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:"
  test declName := do
    if (← isAutoDecl declName) || isGlobalInstance (← getEnv) declName then
      return none -- FIXME: scoped/local instances should also not be linted
    if let .str _ s := declName then
      if s == "parenthesizer" || s == "formatter" || s == "delaborator" || s == "quot" then
      return none
    let kind ← match ← getConstInfo declName with
      | .axiomInfo .. => pure "axiom"
      | .opaqueInfo .. => pure "constant"
      | .defnInfo info =>
          -- leanprover/lean4#2575:
          -- projections are generated as `def`s even when they should be `theorem`s
          if ← isProjectionFn declName <&&> isProp info.type then
            return none
          pure "definition"
      | .inductInfo .. => pure "inductive"
      | _ => return none
    let (none) ← findDocString? (← getEnv) declName | return none
    return m!"{kind} missing documentation string"

/-- A linter for checking theorem doc strings. -/
@[std_linter disabled] def docBlameThm : Linter where
  noErrorsFound := "No theorems are missing documentation."
  errorsFound := "THEOREMS ARE MISSING DOCUMENTATION STRINGS:"
  test declName := do
    if ← isAutoDecl declName then
      return none
    let kind ← match ← getConstInfo declName with
      | .thmInfo .. => pure "theorem"
      | .defnInfo info =>
          -- leanprover/lean4#2575:
          -- projections are generated as `def`s even when they should be `theorem`s
          if ← isProjectionFn declName <&&> isProp info.type then
            pure "Prop projection"
          else
            return none
      | _ => return none
    let (none) ← findDocString? (← getEnv) declName | return none
    return m!"{kind} missing documentation string"

/-- A linter for checking whether the correct declaration constructor (definition or theorem)
has been used. -/
@[std_linter] def defLemma : Linter where
  noErrorsFound := "All declarations correctly marked as def/lemma."
  errorsFound := "INCORRECT DEF/LEMMA:"
  test declName := do
    if (← isAutoDecl declName) || isGlobalInstance (← getEnv) declName then
      return none
    -- leanprover/lean4#2575:
    -- projections are generated as `def`s even when they should be `theorem`s
    if ← isProjectionFn declName then return none
    let info ← getConstInfo declName
    let isThm ← match info with
      | .defnInfo .. => pure false
      | .thmInfo .. => pure true
      | _ => return none
    match isThm, ← isProp info.type with
    | true, false => pure "is a lemma/theorem, should be a def"
    | false, true => pure "is a def, should be lemma/theorem"
    | _, _ => return none

/-- A linter for checking whether statements of declarations are well-typed. -/
@[std_linter] def checkType : Linter where
  noErrorsFound :=
    "The statements of all declarations type-check with default reducibility settings."
  errorsFound := "THE STATEMENTS OF THE FOLLOWING DECLARATIONS DO NOT TYPE-CHECK."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isTypeCorrect (← getConstInfo declName).type then return none
    return m!"the statement doesn't type check."

/--
`univParamsGrouped e` computes for each `level` `u` of `e` the parameters that occur in `u`,
and returns the corresponding set of lists of parameters.
In pseudo-mathematical form, this returns `{{p : parameter | p ∈ u} | (u : level) ∈ e}`
FIXME: We use `Array Name` instead of `HashSet Name`, since `HashSet` does not have an equality
instance. It will ignore `nm₀.proof_i` declarations.
-/
private def univParamsGrouped (e : Expr) (nm₀ : Name) : Lean.HashSet (Array Name) :=
  runST fun σ => do
    let res ← ST.mkRef (σ := σ) {}
    e.forEach fun
      | .sort u =>
        res.modify (·.insert (CollectLevelParams.visitLevel u {}).params)
      | .const n us => do
        if let .str n s .. := n then
          if n == nm₀ && s.startsWith "proof_" then
            return
        res.modify <| us.foldl (·.insert <| CollectLevelParams.visitLevel · {} |>.params)
      | _ => pure ()
    res.get

/--
The good parameters are the parameters that occur somewhere in the set as a singleton or
(recursively) with only other good parameters.
All other parameters in the set are bad.
-/
private partial def badParams (l : Array (Array Name)) : Array Name :=
  let goodLevels := l.filterMap fun
    | #[u] => some u
    | _ => none
  if goodLevels.isEmpty then
    l.flatten.toList.eraseDups.toArray
  else
    badParams <| l.map (·.filter (!goodLevels.contains ·))

/-- A linter for checking that there are no bad `max u v` universe levels.
Checks whether all universe levels `u` in the type of `d` are "good".
This means that `u` either occurs in a `level` of `d` by itself, or (recursively)
with only other good levels.
When this fails, usually this means that there is a level `max u v`, where neither `u` nor `v`
occur by themselves in a level. It is ok if *one* of `u` or `v` never occurs alone. For example,
`(α : Type u) (β : Type (max u v))` is a occasionally useful method of saying that `β` lives in
a higher universe level than `α`.
-/
@[std_linter] def checkUnivs : Linter where
  noErrorsFound :=
    "All declarations have good universe levels."
  errorsFound := "THE STATEMENTS OF THE FOLLOWING DECLARATIONS HAVE BAD UNIVERSE LEVELS. \
    This usually means that there is a `max u v` in the type where neither `u` nor `v` \
    occur by themselves. Solution: Find the type (or type bundled with data) that has this \
    universe argument and provide the universe level explicitly. If this happens in an implicit \
    argument of the declaration, a better solution is to move this argument to a `variables` \
    command (then it's not necessary to provide the universe level).\n\n\
    It is possible that this linter gives a false positive on definitions where the value of the \
    definition has the universes occur separately, and the definition will usually be used with \
    explicit universe arguments. In this case, feel free to add `@[nolint checkUnivs]`."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    let bad := badParams (univParamsGrouped (← getConstInfo declName).type declName).toArray
    if bad.isEmpty then return none
    return m!"universes {bad} only occur together."

/-- A linter for checking that declarations aren't syntactic tautologies.
Checks whether a lemma is a declaration of the form `∀ a b ... z, e₁ = e₂`
where `e₁` and `e₂` are identical exprs.
We call declarations of this form syntactic tautologies.
Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving basic facts
with rfl when elaboration results in a different term than the user intended. -/
@[std_linter] def synTaut : Linter where
  noErrorsFound :=
    "No declarations are syntactic tautologies."
  errorsFound := "THE FOLLOWING DECLARATIONS ARE SYNTACTIC TAUTOLOGIES. \
    This usually means that they are of the form `∀ a b ... z, e₁ = e₂` where `e₁` and `e₂` are \
    identical expressions. We call declarations of this form syntactic tautologies. \
    Such lemmas are (mostly) useless and sometimes introduced unintentionally when proving \
    basic facts using `rfl`, when elaboration results in a different term than the user intended. \
    You should check that the declaration really says what you think it does."
  isFast := true
  test declName := do
    if ← isAutoDecl declName then return none
    forallTelescope (← getConstInfo declName).type fun _ ty => do
      let some (lhs, rhs) := ty.eq?.map (fun (_, l, r) => (l, r)) <|> ty.iff?
        | return none
      if lhs == rhs then
        return m!"LHS equals RHS syntactically"
      return none

/--
Return a list of unused `let_fun` terms in an expression.
-/
def findUnusedHaves (e : Expr) : MetaM (Array MessageData) := do
  let res ← IO.mkRef #[]
  forEachExpr e fun e => do
    match e.letFun? with
    | some (n, t, _, b) =>
      if n.isInternal then return
      if b.hasLooseBVars then return
      let msg ← addMessageContextFull m!"unnecessary have {n.eraseMacroScopes} : {t}"
      res.modify (·.push msg)
    | _ => return
  res.get

/-- A linter for checking that declarations don't have unused term mode have statements. We do not
tag this as `@[std_linter]` so that it is not in the default linter set as it is slow and an
uncommon problem. -/
@[std_linter] def unusedHavesSuffices : Linter where
  noErrorsFound := "No declarations have unused term mode have statements."
  errorsFound := "THE FOLLOWING DECLARATIONS HAVE INEFFECTUAL TERM MODE HAVE/SUFFICES BLOCKS. \
    In the case of `have` this is a term of the form `have h := foo, bar` where `bar` does not \
    refer to `foo`. Such statements have no effect on the generated proof, and can just be \
    replaced by `bar`, in addition to being ineffectual, they may make unnecessary assumptions \
    in proofs appear as if they are used. \
    For `suffices` this is a term of the form `suffices h : foo, proof_of_goal, proof_of_foo` \
    where `proof_of_goal` does not refer to `foo`. \
    Such statements have no effect on the generated proof, and can just be replaced by \
    `proof_of_goal`, in addition to being ineffectual, they may make unnecessary assumptions \
    in proofs appear as if they are used."
  test declName := do
    if ← isAutoDecl declName then return none
    let info ← getConstInfo declName
    let mut unused ← findUnusedHaves info.type
    if let some value := info.value? then
      unused := unused ++ (← findUnusedHaves value)
    unless unused.isEmpty do
      return some <| .joinSep unused.toList ", "
    return none

/--
A linter for checking if variables appearing on both sides of an iff are explicit. Ideally, such
variables should be implicit instead.
-/
@[std_linter disabled] def explicitVarsOfIff : Linter where
  noErrorsFound := "No explicit variables on both sides of iff"
  errorsFound := "EXPLICIT VARIABLES ON BOTH SIDES OF IFF"
  test declName := do
    if ← isAutoDecl declName then return none
    forallTelescope (← getConstInfo declName).type fun args ty => do
      let some (lhs, rhs) := ty.iff? | return none
      let explicit ← args.filterM fun arg =>
        return (← getFVarLocalDecl arg).binderInfo.isExplicit &&
          lhs.containsFVar arg.fvarId! && rhs.containsFVar arg.fvarId!
      if explicit.isEmpty then return none
      addMessageContextFull m!"should be made implicit: {
        MessageData.joinSep (explicit.toList.map (m!"{·}")) ", "}"
