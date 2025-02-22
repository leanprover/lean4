/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Name

namespace Lake
open Lean (Name)

/-- The type of keys in the Lake build store. -/
inductive BuildKey
| module (module : Name)
| package (package : Name)
| packageTarget (package : Name) (target : Name)
| facet (key : BuildKey) (facet : Name)
deriving Inhabited, Repr, DecidableEq, Hashable

namespace BuildKey

abbrev moduleFacet (module facet : Name) : BuildKey :=
  .facet (.module module) (`module ++ facet)

abbrev packageFacet (package facet : Name) : BuildKey :=
  .facet (.package package) (`package ++ facet)

@[match_pattern] abbrev targetFacet (package target facet : Name) : BuildKey :=
  .facet (.packageTarget package target) facet

@[match_pattern] abbrev customTarget (package target : Name) : BuildKey :=
  .packageTarget package target

private def eraseHead : Name → Name
| .anonymous | .str .anonymous _  | .num .anonymous _  => .anonymous
| .str p s => .str (eraseHead p) s
| .num p s => .num (eraseHead p) s

def toString : (self : BuildKey) → String
| module m => s!"+{m}"
| package p => s!"@{p}"
| packageTarget p t => s!"{p}/{t}"
| facet k f => s!"{toString k}:{eraseHead f}"

/-- Like the default `toString`, but without disambiguation markers. -/
def toSimpleString : (self : BuildKey) → String
| module m => s!"{m}"
| package p => s!"{p}"
| packageTarget p t => s!"{p}/{t}"
| facet k f => s!"{toSimpleString k}:{eraseHead f}"

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
  | facet k f =>
    match k' with
    | facet k' f' =>
      match k.quickCmp k' with
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
  | facet k f ih =>
    unfold quickCmp
    intro k'; cases k'
    case facet k' f' =>
      dsimp only; split
      next k_eq => intro f_eq; rw [ih k_eq, eq_of_cmp f_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)

instance : LawfulCmpEq BuildKey quickCmp where
  eq_of_cmp := eq_of_quickCmp
  cmp_rfl {k} := by induction k <;> simp_all [quickCmp]
