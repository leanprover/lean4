/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

prelude
public meta import Lean.Linter.EnvLinter.Basic
public meta import Lean.MonadEnv
public meta import Lean.ReducibilityAttrs
public meta import Lean.ProjFns
public meta import Lean.Meta.InferType
public meta import Lean.Util.CollectLevelParams
public meta import Lean.Util.ForEachExpr
public meta import Lean.Meta.Instances

open Lean Meta

public meta section

namespace Lean.Linter.EnvLinter

/-- A linter for checking whether the correct declaration constructor (`def` or `theorem`)
has been used. A `def` whose type is a `Prop` should be a `theorem`, and vice versa. -/
@[builtin_env_linter] def defLemma : EnvLinter where
  noErrorsFound := "All declarations correctly marked as def/lemma."
  errorsFound := "INCORRECT DEF/LEMMA:"
  test declName := do
    if ← isAutoDecl declName then return none
    let info ← getConstInfo declName
    if info.isDefinition then
      if ← isProp info.type then return some "is a def, should be a lemma/theorem"
    return none

/--
`univParamsGrouped e nm₀` computes for each `Level` occurring in `e` the set of level parameters
that appear in it, returning the collection of such parameter sets.
In pseudo-mathematical form, this returns `{{p : parameter | p ∈ u} | (u : level) ∈ e}`.
Ignores `nm₀.proof_*` sub-constants.
-/
private def univParamsGrouped (e : Expr) (nm₀ : Name) : Std.HashSet (Array Name) :=
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
This means that `u` either occurs in a `Level` of `d` by itself, or (recursively)
with only other good levels.
When this fails, usually this means that there is a level `max u v`, where neither `u` nor `v`
occur by themselves in a level. It is ok if *one* of `u` or `v` never occurs alone. For example,
`(α : Type u) (β : Type (max u v))` is an occasionally useful method of saying that `β` lives in
a higher universe level than `α`. -/
@[builtin_env_linter] def checkUnivs : EnvLinter where
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
    explicit universe arguments. In this case, feel free to add `@[builtin_nolint checkUnivs]`."
  test declName := do
    if ← isAutoDecl declName then return none
    let bad := badParams (univParamsGrouped (← getConstInfo declName).type declName).toArray
    if bad.isEmpty then return none
    return m!"universes {bad} only occur together."

/-- A linter for checking whether a declaration has a namespace twice consecutively in its name. -/
@[builtin_env_linter clippy] def dupNamespace : EnvLinter where
  noErrorsFound := "No declarations have a duplicate namespace."
  errorsFound := "DUPLICATED NAMESPACES IN NAME:"
  test declName := do
    if ← isAutoDecl declName then return none
    if ← isImplicitReducible declName then return none
    let nm := declName.components
    let some (dup, _) := nm.zip nm.tail! |>.find? fun (x, y) => x == y
      | return none
    return m!"The namespace {dup} is duplicated in the name"

end Lean.Linter.EnvLinter

end
