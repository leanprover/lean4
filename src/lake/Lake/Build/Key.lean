/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.Order
import Lake.Util.Name
import Lake.Config.Kinds
import Init.Data.String.TakeDrop

namespace Lake
open Lean (Name)

/-- The type of keys in the Lake build store. -/
public inductive BuildKey
| module (module : Name)
| package (package : Name)
| packageTarget (package target : Name)
| facet (target : BuildKey) (facet : Name)
deriving Inhabited, Repr, DecidableEq, Hashable

public def PartialBuildKey.moduleTargetIndicator := `«_+»

/--
A build key with some missing info.

* Package names may be elided (replaced by `Name.anonymous`).
* Facet names are unqualified (they do not include the input target kind)
  and may also be ellided.
* Module package targets are supported via a fake `packageTarget` with
  a target name ending in `moduleTargetIndicator`.
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
  match s.splitOn ":" with
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
    match s.splitOn "/" with
    | [target] =>
      if target.isEmpty then
        return .package .anonymous
      if target.startsWith "@" then
        let pkg := target.drop 1
        if pkg.isEmpty then
          return .package .anonymous
        else
          return .package (stringToLegalOrSimpleName pkg)
      else if target.startsWith "+" then
        return .module (stringToLegalOrSimpleName (target.drop 1))
      else
        parsePackageTarget .anonymous target
    | [pkg, target] =>
      let pkg := if pkg.startsWith "@" then pkg.drop 1 else pkg
      if pkg.isEmpty then
        parsePackageTarget .anonymous target
      else
        parsePackageTarget (stringToLegalOrSimpleName pkg) target
    | _ =>
      throw "ill-formed target: too many '/'"
  parsePackageTarget pkg target :=
    if target.isEmpty then
      throw s!"ill-formed target: default package targets are not supported in partial build keys"
    else if target.startsWith "+" then
      let target := target.drop 1 |> stringToLegalOrSimpleName
      let target := target ++ moduleTargetIndicator
      return .packageTarget pkg target
    else
      let target := stringToLegalOrSimpleName target
      return .packageTarget pkg target

public def toString : (self : PartialBuildKey) → String
| .module m => s!"+{m}"
| .package p => if p.isAnonymous then "" else s!"@{p}"
| .packageTarget p t =>
  let t :=
    if let some t := t.eraseSuffix? moduleTargetIndicator then
      s!"+{t}"
    else t.toString
  if p.isAnonymous then t else s!"{p}/{t}"
| .facet t f => if f.isAnonymous then toString t else s!"{toString t}:{f}"

public instance : ToString PartialBuildKey := ⟨PartialBuildKey.toString⟩

end PartialBuildKey

namespace BuildKey

@[match_pattern] public abbrev moduleFacet (module facet : Name) : BuildKey :=
  .facet (.module module) facet

@[match_pattern] public abbrev packageFacet (package facet : Name) : BuildKey :=
  .facet (.package package) facet

@[match_pattern] public abbrev targetFacet (package target facet : Name) : BuildKey :=
  .facet (.packageTarget package target) facet

@[match_pattern] public abbrev customTarget (package target : Name) : BuildKey :=
  .packageTarget package target

public def toString : (self : BuildKey) → String
| module m => s!"+{m}"
| package p => s!"@{p}"
| packageTarget p t => s!"{p}/{t}"
| facet t f => s!"{toString t}:{Name.eraseHead f}"

/-- Like the default `toString`, but without disambiguation markers. -/
public def toSimpleString : (self : BuildKey) → String
| module m => s!"{m}"
| package p => s!"{p}"
| packageTarget p t => s!"{p}/{t}"
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
    · simp_all [quickCmp]
