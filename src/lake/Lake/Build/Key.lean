/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Name
import Lake.Config.Kinds

namespace Lake
open Lean (Name)

/-- The type of keys in the Lake build store. -/
inductive BuildKey
| module (module : Name)
| package (package : Name)
| packageTarget (package target : Name)
| facet (target : BuildKey) (facet : Name)
deriving Inhabited, Repr, DecidableEq, Hashable

/--
A build key with some missing info.
Package names may be elided (replaced by `Name.anonymous`),
and facet names are unqualified (they do not include the input target kind).
-/
def PartialBuildKey := BuildKey

/--
Parses a `PartialBuildKey` from a `String`.
Uses the same syntax as the `lake build` / `lake query` CLI.
-/
def PartialBuildKey.parse (s : String) : Except String PartialBuildKey := do
  let decodeTarget s := do
    match s.splitOn "/" with
    | [target] =>
      if target.isEmpty then
        return .package .anonymous
      if target.startsWith "@" then
        let pkg := target.drop 1 |> stringToLegalOrSimpleName
        return .package pkg
      else if target.startsWith "+" then
        throw s!"ill-formed target: module targets are not allowed in partial build keys"
      else
        let target := stringToLegalOrSimpleName target
        return .packageTarget .anonymous target
    | [pkg, target] =>
      if target.isEmpty then
        throw s!"ill-formed target: default package targets are not supported in partial build keys"
      let pkg :=
        if pkg.isEmpty then
          .anonymous
        else
          let pkg := if pkg.startsWith "@" then pkg.drop 1 else pkg
          stringToLegalOrSimpleName pkg
      let target := stringToLegalOrSimpleName target
      return .packageTarget pkg target
    | _ =>
      throw "ill-formed target: too many '/'"
  match s.splitOn ":" with
  | [target] =>
    decodeTarget target
  | [target, facetSpec] =>
    let target ← decodeTarget target
    let facet := stringToLegalOrSimpleName facetSpec
    return .facet target facet
  | _ =>
    throw "ill-formed target: too many':'"

def PartialBuildKey.toString : (self : PartialBuildKey) → String
| .module m => s!"+{m}"
| .package p => if p.isAnonymous then "" else s!"@{p}"
| .packageTarget p t => if p.isAnonymous then s!"{t}" else s!"{p}/{t}"
| .facet t f => if f.isAnonymous then toString t else s!"{toString t}:{f}"

instance : ToString PartialBuildKey := ⟨PartialBuildKey.toString⟩

namespace BuildKey

@[match_pattern] abbrev moduleFacet (module facet : Name) : BuildKey :=
  .facet (.module module) facet

@[match_pattern] abbrev packageFacet (package facet : Name) : BuildKey :=
  .facet (.package package) facet

@[match_pattern] abbrev targetFacet (package target facet : Name) : BuildKey :=
  .facet (.packageTarget package target) facet

@[match_pattern] abbrev customTarget (package target : Name) : BuildKey :=
  .packageTarget package target

def toString : (self : BuildKey) → String
| module m => s!"+{m}"
| package p => s!"@{p}"
| packageTarget p t => s!"{p}/{t}"
| facet t f => s!"{toString t}:{Name.eraseHead f}"

/-- Like the default `toString`, but without disambiguation markers. -/
def toSimpleString : (self : BuildKey) → String
| module m => s!"{m}"
| package p => s!"{p}"
| packageTarget p t => s!"{p}/{t}"
| facet t f => s!"{toSimpleString t}:{Name.eraseHead f}"

instance : ToString BuildKey := ⟨(·.toString)⟩

def quickCmp (k k' : BuildKey) : Ordering :=
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

theorem eq_of_quickCmp :
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
      next p_eq => intro t_eq; rw [eq_of_cmp p_eq, eq_of_cmp t_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)
  | facet t f ih =>
    unfold quickCmp
    intro k'; cases k'
    case facet t' f'' =>
      dsimp only; split
      next t_eq => intro f_eq; rw [ih t_eq, eq_of_cmp f_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)

instance : LawfulCmpEq BuildKey quickCmp where
  eq_of_cmp := eq_of_quickCmp
  cmp_rfl {k} := by induction k <;> simp_all [quickCmp]
