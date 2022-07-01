/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Name

namespace Lake

/-- The type of keys in the Lake build store. -/
inductive BuildKey
| moduleFacet (module : WfName) (facet : WfName)
| packageFacet (package : WfName) (facet : WfName)
| targetFacet (package : WfName) (target : WfName) (facet : WfName)
| customTarget (package : WfName) (target : WfName)
deriving Inhabited, Repr, DecidableEq, Hashable

namespace BuildKey

def toString : (self : BuildKey) → String
| moduleFacet m f => s!"+{m}:{f}"
| packageFacet p f => s!"@{p}:{f}"
| targetFacet p t f => s!"{p}/{t}:{f}"
| customTarget p t => s!"{p}/{t}"

instance : ToString BuildKey := ⟨(·.toString)⟩

def quickCmp (k k' : BuildKey) : Ordering :=
  match k with
  | moduleFacet m f =>
    match k' with
    | moduleFacet m' f' =>
      match m.quickCmp m' with
      | .eq => f.quickCmp f'
      | ord => ord
    | _ => .lt
  | packageFacet p f =>
    match k' with
    | moduleFacet .. => .gt
    | packageFacet p' f' =>
      match p.quickCmp p' with
      | .eq => f.quickCmp f'
      | ord => ord
    | _ => .lt
  | targetFacet p t f =>
    match k' with
    | customTarget .. => .lt
    | targetFacet p' t' f' =>
      match p.quickCmp p' with
      | .eq =>
        match t.quickCmp t' with
        | .eq => f.quickCmp f'
        | ord => ord
      | ord => ord
    | _=> .gt
  | customTarget p t =>
    match k' with
    | customTarget p' t' =>
      match p.quickCmp p' with
      | .eq => t.quickCmp t'
      | ord => ord
    | _ => .gt

theorem eq_of_quickCmp {k k' : BuildKey}  :
quickCmp k k' = Ordering.eq → k = k' := by
  unfold quickCmp
  cases k with
  | moduleFacet m f =>
    cases k'
    case moduleFacet m' f' =>
      dsimp; split
      next m_eq => intro f_eq; simp [eq_of_cmp m_eq, eq_of_cmp f_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)
  | packageFacet p f =>
    cases k'
    case packageFacet p' f' =>
      dsimp; split
      next p_eq => intro f_eq; simp [eq_of_cmp p_eq, eq_of_cmp f_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)
  | targetFacet p t f =>
    cases k'
    case targetFacet p' t' f' =>
      dsimp; split
      next p_eq =>
        split
        next t_eq =>
          intro f_eq
          simp [eq_of_cmp p_eq, eq_of_cmp t_eq, eq_of_cmp f_eq]
        next => intro; contradiction
      next => intro; contradiction
    all_goals (intro; contradiction)
  | customTarget p t =>
    cases k'
    case customTarget p' t' =>
      dsimp; split
      next p_eq => intro t_eq; simp [eq_of_cmp p_eq, eq_of_cmp t_eq]
      next => intro; contradiction
    all_goals (intro; contradiction)

instance : EqOfCmp BuildKey quickCmp where
  eq_of_cmp := eq_of_quickCmp
