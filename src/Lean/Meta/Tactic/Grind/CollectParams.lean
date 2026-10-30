/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Syntax
namespace Lean.Meta.Grind
/-!
Given an auto-generated `grind` tactic script, collect params for
single shot `finish` or top-level `grind` tactic.

**Note**: The collector interprets the tactics that `grind?` and `finish?` generate. It must be
updated whenever they generate a new kind of tactic, in particular one that instantiates theorems
or performs case-splits. See `Collector.collect`.
-/
public abbrev TParam := TSyntax ``Parser.Tactic.grindParam
abbrev TAnchor := TSyntax ``Parser.Tactic.anchor

namespace Collector

structure State where
  params : Array TParam := #[]
  anchors : Array TAnchor := #[]
  hasSorry : Bool := false
  /-- E-matching rounds performed since the last case-split in the current branch. -/
  rounds : Nat := 0
  /-- Maximum value of `rounds` in all branches. -/
  maxRounds : Nat := 0

abbrev Collect := StateRefT State CoreM

def pushParam (p : TParam) : Collect Unit := do
  if (← get).params.contains p then
    return ()
  modify fun s => { s with params := s.params.push p }

def pushAnchor (a : TAnchor) : Collect Unit := do
  if (← get).anchors.contains a then
    return ()
  modify fun s => { s with anchors := s.anchors.push a }

/-- Records an E-matching round. -/
def pushRound : Collect Unit :=
  modify fun s => { s with rounds := s.rounds + 1, maxRounds := max s.maxRounds (s.rounds + 1) }

/-- Records a case-split. Like `grind`, it resets the E-matching round counter. -/
def resetRounds : Collect Unit :=
  modify fun s => { s with rounds := 0 }

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

def isAlternative (tac : TGrind) : Bool :=
  match tac with
  | `(grind| next => $$_;*) | `(grind| · $$_;*) => true
  | _ => false

mutual
/--
Collects the parameters, anchors, and E-matching rounds of a generated tactic.

**Note**: This function must handle every kind of tactic that `grind?` and `finish?` generate.
Tactics it does not know are conservatively counted as one E-matching round, see
`mkGrindOnlyTactics`, but their parameters and anchors are lost.
-/
partial def collect (tac : TGrind) : Collect Unit := do
  match tac with
  | `(grind| sorry) => modify fun s => { s with hasSorry := true }
  | `(grind| next => $$seq;*)
  | `(grind| · $$seq;*) =>
    collectSeq <| seq.getElems.toList.filterMap fun (step : TSyntax ``Parser.Tactic.Grind.grindStep) =>
      match step with
      | `(Parser.Tactic.Grind.grindStep| $tac:grind $[| $_:grind_filter]?) => some (tac : TGrind)
      | _ => none
  | `(grind| $tac₁:grind <;> $tac₂:grind) => collect tac₁; collect tac₂
  | `(grind| cases $a:anchor) => pushAnchor a; resetRounds
  | `(grind| cases $a:anchor/$_:num) => pushAnchor a; resetRounds
  | `(grind| use [$params,*]) =>
    pushRound
    collectInstantiateParams params
  | `(grind| instantiate $[only]? $[approx]? $[[$params?,*]]?) =>
    pushRound
    let some params := params? | return ()
    collectInstantiateParams params
  | `(grind| ring) | `(grind| lia) | `(grind| linarith) | `(grind| ac) | `(grind| mbtc)
  | `(grind| done) | `(grind| skip) | `(grind| intros) | `(grind| by_contra) => return ()
  | _ => pushRound

/--
Collects a tactic sequence. Consecutive `·` and `next` tactics are the alternatives of a case-split,
and each one starts with the E-matching round counter of the case-split.
-/
partial def collectSeq : List TGrind → Collect Unit
  | [] => return ()
  | tac :: rest => do
    if isAlternative tac then
      let (alts, rest) := (tac :: rest).span isAlternative
      let rounds := (← get).rounds
      let mut roundsAfter := rounds
      for alt in alts do
        modify fun s => { s with rounds }
        collect alt
        roundsAfter := max roundsAfter (← get).rounds
      modify fun s => { s with rounds := roundsAfter }
      collectSeq rest
    else
      collect tac
      collectSeq rest
end

def main (seq : List TGrind) : Collect Unit :=
  collectSeq seq

end Collector

structure CollectResult where
  hasSorry  : Bool
  params    : Array TParam
  anchors   : Array TParam
  /-- Maximum number of E-matching rounds between case-splits in a branch. -/
  maxRounds : Nat

def collectParamsCore (seq : List TGrind) : CoreM CollectResult := do
  let (_, s) ← Collector.main seq |>.run {}
  let anchors ← s.anchors.mapM fun anchor =>
    `(Parser.Tactic.grindParam| $anchor:anchor)
  return { s with anchors }

def collectParams (seq : List TGrind) : CoreM (Array TParam) := do
  let { params, anchors, .. } ← collectParamsCore seq
  return params ++ anchors

/--
Given a `grind` tactic sequence, extracts parameters and builds a terminal `finish only` tactic.
The `extraParams` are additional parameters (e.g., from the original `finish?` call) that
should always be included.
-/
public def mkFinishTactic (seq : List TGrind) (extraParams : Array TParam := #[]) : CoreM TGrind := do
  let params := (← collectParams seq) ++ extraParams
  `(grind| finish only [$params,*])

/--
Given a `grind` tactic sequence, extracts parameters and builds a `grind only` tactics.
It returns at most two. The first tactic uses anchors to restrict the search if applicable.
The second does not restrict the search using anchors. The second option is included only if there
are anchors.

The `extraParams` are additional parameters (e.g., term arguments from the original `grind?` call)
that should always be included in the suggestion.

If `seq` performs more than `ematchLimit` E-matching rounds between case-splits, the suggestions
set the `ematch` limit to that number. The search that produced `seq` may have performed more
rounds because case-splits reset the round counter, even if they were pruned from `seq`.
-/
public def mkGrindOnlyTactics (cfg : TSyntax `Lean.Parser.Tactic.optConfig) (seq : List TGrind)
    (extraParams : Array TParam := #[]) (ematchLimit : Nat) : CoreM (Array (TSyntax `tactic)) := do
  let { hasSorry, params, anchors, maxRounds } ← collectParamsCore seq
  if hasSorry then return #[]
  let params := if grind.debug.dropParams.get (← getOptions) then #[] else params
  let cfg ← if maxRounds > ematchLimit then
    let item ← `(Parser.Tactic.configItem| ($(mkIdent `ematch):ident := $(quote maxRounds)))
    pure ⟨cfg.raw.setArg 0 (cfg.raw[0].setArgs (cfg.raw[0].getArgs.push item))⟩
  else
    pure cfg
  let allParams := params ++ anchors ++ extraParams
  let s₁ ← mkTac cfg allParams
  if anchors.isEmpty then
    return #[s₁]
  else
    let s₂ ← mkTac cfg (params ++ extraParams)
    return #[s₁, s₂]
where
  mkTac (cfg : TSyntax `Lean.Parser.Tactic.optConfig) (params : Array TParam) : CoreM (TSyntax `tactic) :=
    if params.isEmpty then
      `(tactic| grind $cfg:optConfig only)
    else
      `(tactic| grind $cfg:optConfig only [$params,*])

end Lean.Meta.Grind
