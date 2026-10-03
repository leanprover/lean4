/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.Order
import Lake.Util.Name
import Init.Data.String.Search
import Init.Data.Iterators.Consumers

namespace Lake
open Lean (Name)

/-- The type of keys in the Lake build store. -/
public inductive BuildKey
| module (module : Name)
| package (package : Name)
| packageModule (package module : Name)
| packageTarget (package target : Name)
| facet (target : BuildKey) (facet : Name)
deriving Inhabited, Repr, DecidableEq, Hashable

/--
Whether every module key includes its package key.

## Intent
Describe the key shape used to register resolved module facets. Package and facet
names are checked separately by their workspace lookups.
-/
public def BuildKey.moduleKeysResolved : BuildKey → Prop
  | .module _ => False
  | .facet target _ => target.moduleKeysResolved
  | _ => True

/--
Resolve unscoped module keys with the supplied workspace lookup.

## Intent
Use the same package-scoped key for full-key and partial-key facet registration.
The lookup supplies package identity; an absent module refuses resolution.
-/
public def BuildKey.resolveModuleKeys? (package? : Name → Option Name) :
    BuildKey → Option BuildKey
  | .module name => (package? name).map (.packageModule · name)
  | .facet target facetName =>
    (target.resolveModuleKeys? package?).map (.facet · facetName)
  | key => some key

/--
Successful module-key resolution removes every unscoped module key.

## Intent
Establish the shape of the actual key passed to facet registration, including
nested facets, without assuming that an arbitrary workspace is coherent.
-/
public theorem BuildKey.resolveModuleKeys?_resolved
    (package? : Name → Option Name) (self resolved : BuildKey)
    (h : self.resolveModuleKeys? package? = some resolved) :
    resolved.moduleKeysResolved := by
  induction self generalizing resolved with
  | module name =>
    cases hp : package? name with
    | none => simp [resolveModuleKeys?, hp] at h
    | some package =>
      simp [resolveModuleKeys?, hp] at h
      cases h
      trivial
  | facet target facet ih =>
    cases ht : target.resolveModuleKeys? package? with
    | none => simp [resolveModuleKeys?, ht] at h
    | some key =>
      simp [resolveModuleKeys?, ht] at h
      cases h
      exact ih key ht
  | package name | packageModule name mod | packageTarget name target =>
    simp [resolveModuleKeys?] at h
    cases h
    trivial

/--
Resolving an already scoped key preserves it independently of the lookup.

## Intent
Make repeated normalization preserve the memoization key.
-/
public theorem BuildKey.resolveModuleKeys?_of_resolved
    (package? : Name → Option Name) (self : BuildKey)
    (h : self.moduleKeysResolved) : self.resolveModuleKeys? package? = some self := by
  induction self with
  | module name => exact False.elim h
  | facet target facet ih => simp [resolveModuleKeys?, ih h]
  | package name | packageModule name mod | packageTarget name target => rfl

/--
A build key with some missing info.

* Package names may be elided (replaced by `Name.anonymous`).
* Facet names are unqualified (they do not include the input target kind)
  and may also be ellided.
-/
@[expose]  -- for codegen
public def PartialBuildKey := BuildKey

namespace PartialBuildKey

/-- Cast a `BuildKey` to a `PartialBuildKey`. -/
@[inline] public def mk (key : BuildKey) : PartialBuildKey := key

public instance : Coe BuildKey PartialBuildKey := ⟨mk⟩

public instance : Repr PartialBuildKey :=
  private_decl% (@id (Repr PartialBuildKey) (inferInstanceAs (Repr BuildKey)))

public instance : Inhabited PartialBuildKey := ⟨mk <| .package .anonymous⟩

/--
Parses a `PartialBuildKey` from a `String`.
Uses the same syntax as the `lake build` / `lake query` CLI.
-/
public def parse (s : String) : Except String PartialBuildKey := do
  if s.isEmpty then
    throw "ill-formed target: empty string"
  match s.split ':' |>.toStringList with
  | target :: facets =>
    let target ← parseTarget target
    facets.foldlM (init := target) fun target facet => do
      if facet.isEmpty then
        throw "ill-formed target: empty facet"
      else
        return .facet target (stringToLegalOrSimpleName facet)
  | [] =>
    -- ∀ str, length (str.splitOn sep) > 0
    unreachable!
where
  parseTarget s := do
    match s.split '/' |>.toList with
    | [target] =>
      if target.isEmpty then
        return .package .anonymous
      if target.startsWith "@" then
        let pkg := target.drop 1
        if pkg.isEmpty then
          return .package .anonymous
        else
          return .package (stringToLegalOrSimpleName pkg.copy)
      else if target.startsWith "+" then
        let mod := target.drop 1
        if mod.isEmpty then
          throw "ill-formed target: expected module name after '+'"
        else
          return .module (stringToLegalOrSimpleName mod.copy)
      else
        parsePackageTarget .anonymous target
    | [pkg, target] =>
      let pkg := if pkg.startsWith "@" then pkg.drop 1 else pkg
      if pkg.isEmpty then
        parsePackageTarget .anonymous target
      else
        parsePackageTarget (stringToLegalOrSimpleName pkg.copy) target
    | _ =>
      throw "ill-formed target: too many '/'"
  parsePackageTarget pkg target :=
    if target.isEmpty then
      throw s!"ill-formed target: default package targets are not supported in partial build keys"
    else if target.startsWith "+" then
      let target := target.drop 1 |>.copy |> stringToLegalOrSimpleName
      return .packageModule pkg target
    else
      let target := stringToLegalOrSimpleName target.copy
      return .packageTarget pkg target

public def toString : (self : PartialBuildKey) → String
| .module m => s!"+{m}"
| .package p => match (getPkgName p) with | .anonymous => "" | p => s!"@{p}"
| .packageModule p m => match (getPkgName p) with | .anonymous => s!"+{m}" | p => s!"{p}/+{m}"
| .packageTarget p t => match (getPkgName p) with | .anonymous => t.toString | p => s!"{p}/{t}"
| .facet t f => if f.isAnonymous then toString t else s!"{toString t}:{f}"
where
  /-- Utility for extracting a package's base name from its key name. -/
  getPkgName (p : Name) : Name :=
    match p with
    | .anonymous | .num .anonymous _ => .anonymous
    | .num p _ | p => p

public instance : ToString PartialBuildKey := ⟨PartialBuildKey.toString⟩

end PartialBuildKey

namespace BuildKey

@[match_pattern] public abbrev moduleFacet (module facet : Name) : BuildKey :=
  .facet (.module module) facet

@[match_pattern] public abbrev packageFacet (package facet : Name) : BuildKey :=
  .facet (.package package) facet

@[match_pattern] public abbrev packageModuleFacet (package module facet : Name) : BuildKey :=
  .facet (.packageModule package module) facet

attribute [deprecated packageModuleFacet +typeChanged (since := "2025-11-13")] moduleFacet

@[match_pattern] public abbrev targetFacet (package target facet : Name) : BuildKey :=
  .facet (.packageTarget package target) facet

@[match_pattern] public abbrev customTarget (package target : Name) : BuildKey :=
  .packageTarget package target

public def toString : (self : BuildKey) → String
| module m => s!"+{m}"
| package p => s!"@{p.getPrefix}"
| packageModule p m => s!"{p.getPrefix}/+{m}"
| packageTarget p t => s!"{p.getPrefix}/{t}"
| facet t f => s!"{toString t}:{Name.eraseHead f}"

/-- Like the default `toString`, but without disambiguation markers. -/
public def toSimpleString : (self : BuildKey) → String
| module m => s!"{m}"
| package p => s!"{p.getPrefix}"
| packageModule p m => s!"{p.getPrefix}/{m}"
| packageTarget p t => s!"{p.getPrefix}/{t}"
| facet t f => s!"{toSimpleString t}:{Name.eraseHead f}"

public instance : ToString BuildKey := ⟨(·.toString)⟩

public def quickCmp (k k' : BuildKey) : Ordering :=
  match k with
  | module m =>
    match k' with
    | module m' => m.quickCmp m'
    | _ => .lt
  | package p =>
    match k' with
    | module .. => .gt
    | package p' => p.quickCmp p'
    | _ => .lt
  | packageModule p m =>
    match k' with
    | facet .. => .lt
    | packageTarget .. => .lt
    | packageModule p' m' =>
      -- Remark: Comparing by module then package instead of vice-versa
      -- provides a significant performance improvement in the common case.
      -- https://github.com/leanprover/lean4/pull/11169#issuecomment-3535316226
      match m.quickCmp m' with
      | .eq => p.quickCmp p'
      | ord => ord
    | _ => .gt
  | packageTarget p t =>
    match k' with
    | facet .. => .lt
    | packageTarget p' t' =>
      match p.quickCmp p' with
      | .eq => t.quickCmp t'
      | ord => ord
    | _=> .gt
  | facet t f =>
    match k' with
    | facet t' f' =>
      match t.quickCmp t' with
      | .eq => f.quickCmp f'
      | ord => ord
    | _ => .gt

public theorem eq_of_quickCmp :
  quickCmp k k' = Ordering.eq → k = k'
:= by
  revert k'
  induction k with
  | module m =>
    unfold quickCmp
    intro k'; cases k'
    case module m' => simp
    all_goals (intro; contradiction)
  | package p =>
    unfold quickCmp
    intro k'; cases k'
    case package p' => simp
    all_goals (intro; contradiction)
  | packageModule p m =>
    unfold quickCmp
    intro k'; cases k'
    case packageModule p' m' =>
      dsimp only; split
      next p_eq => intro t_eq; rw [Std.LawfulEqCmp.eq_of_compare p_eq, Std.LawfulEqCmp.eq_of_compare t_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)
  | packageTarget p t =>
    unfold quickCmp
    intro k'; cases k'
    case packageTarget p' t' =>
      dsimp only; split
      next p_eq => intro t_eq; rw [Std.LawfulEqCmp.eq_of_compare p_eq, Std.LawfulEqCmp.eq_of_compare t_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)
  | facet t f ih =>
    unfold quickCmp
    intro k'; cases k'
    case facet t' f'' =>
      dsimp only; split
      next t_eq => intro f_eq; rw [ih t_eq, Std.LawfulEqCmp.eq_of_compare f_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)

public instance : Std.LawfulEqCmp quickCmp where
  eq_of_compare := eq_of_quickCmp
  compare_self {k} := by
    induction k
    · simp [quickCmp]
    · simp [quickCmp]
    · simp only [quickCmp]
      split <;> simp_all
    · simp only [quickCmp]
      split <;> simp_all
    · simp_all [quickCmp]
