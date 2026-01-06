/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
namespace Lean.Meta.Grind
/-!
Given an auto-generated `grind` tactic script, collect params for
single shot `finish` or top-level `grind` tactic.
-/
public abbrev TParam := TSyntax ``Parser.Tactic.grindParam
abbrev TAnchor := TSyntax ``Parser.Tactic.anchor

namespace Collector

structure State where
  params : Array TParam := #[]
  anchors : Array TAnchor := #[]
  hasSorry : Bool := false

abbrev Collect := StateRefT State CoreM

def pushParam (p : TParam) : Collect Unit := do
  if (← get).params.contains p then
    return ()
  modify fun s => { s with params := s.params.push p }

def pushAnchor (a : TAnchor) : Collect Unit := do
  if (← get).anchors.contains a then
    return ()
  modify fun s => { s with anchors := s.anchors.push a }

def collectInstantiateParams (params : Syntax.TSepArray `Lean.Parser.Tactic.Grind.thm ",") : Collect Unit := do
  for p in params.getElems do
    match p with
    | `(Lean.Parser.Tactic.Grind.thm| $lemma:grindLemma) =>
      let p ← `(Parser.Tactic.grindParam| $lemma:grindLemma)
      pushParam p
    | `(Lean.Parser.Tactic.Grind.thm| $lemma:grindLemmaMin) =>
      let p ← `(Parser.Tactic.grindParam| $lemma:grindLemmaMin)
      pushParam p
    | `(Lean.Parser.Tactic.Grind.thm| $a:anchor) =>
      pushAnchor a
    | _ =>
      -- Namespace references (thmNs) are handled elsewhere, skip them
      pure ()

partial def collect (tac : TGrind) : Collect Unit := do
  match tac with
  | `(grind| sorry) => modify fun s => { s with hasSorry := true }
  | `(grind| next => $$seq;*)
  | `(grind| · $$seq;*) =>
    for step in seq.getElems do
      match step with
      | `(Parser.Tactic.Grind.grindStep| $tac:grind $[| $_:grind_filter]?) => collect tac
      | _ => return ()
  | `(grind| $tac₁:grind <;> $tac₂:grind) => collect tac₁; collect tac₂
  | `(grind| cases $a:anchor) => pushAnchor a
  | `(grind| use [$params,*]) =>
    collectInstantiateParams params
  | `(grind| instantiate $[only]? $[approx]? $[[$params?,*]]?) =>
    let some params := params? | return ()
    collectInstantiateParams params
  | _ => return ()

def main (seq : List TGrind) : Collect Unit :=
  seq.forM collect

end Collector

def collectParamsCore (seq : List TGrind) : CoreM (Bool × Array TParam × Array TParam) := do
  let (_, s) ← Collector.main seq |>.run {}
  let anchors ← s.anchors.mapM fun anchor =>
    `(Parser.Tactic.grindParam| $anchor:anchor)
  return (s.hasSorry, s.params, anchors)

def collectParams (seq : List TGrind) : CoreM (Array TParam) := do
  let (_, params, anchors) ← collectParamsCore seq
  return params ++ anchors

/--
Given a `grind` tactic sequence, extracts parameters and builds an terminal `finish only` tactic.
-/
public def mkFinishTactic (seq : List TGrind) : CoreM TGrind := do
  let params ← collectParams seq
  `(grind| finish only [$params,*])

/--
Given a `grind` tactic sequence, extracts parameters and builds a `grind only` tactics.
It returns at most two. The first tactic uses anchors to restrict the search if applicable.
The second does not restrict the search using anchors. The second option is included only if there
are anchors.

The `extraParams` are additional parameters (e.g., term arguments from the original `grind?` call)
that should always be included in the suggestion.
-/
public def mkGrindOnlyTactics (cfg : TSyntax `Lean.Parser.Tactic.optConfig) (seq : List TGrind)
    (extraParams : Array TParam := #[]) : CoreM (Array (TSyntax `tactic)) := do
  let (hasSorry, params, anchors) ← collectParamsCore seq
  if hasSorry then return #[]
  let allParams := params ++ anchors ++ extraParams
  let s₁ ← mkTac allParams
  if anchors.isEmpty then
    return #[s₁]
  else
    let s₂ ← mkTac (params ++ extraParams)
    return #[s₁, s₂]
where
  mkTac (params : Array TParam) : CoreM (TSyntax `tactic) :=
    if params.isEmpty then
      `(tactic| grind $cfg:optConfig only)
    else
      `(tactic| grind $cfg:optConfig only [$params,*])

end Lean.Meta.Grind
