/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context

/-!
The `@[frameproc]` attribute: register a frame inference metaprogram for `vcgen`.

A `FrameProc` bundles the inference procedure, the head constant of the frame operator it frames
with, and the lattice split that decomposes that operator. The mechanism mirrors `@[simproc]`: the
attribute records the declaration name, and the compiled `FrameProc` value is recovered from the
environment via `evalConst`, so it works across modules.
-/

open Lean Meta Elab Sym
open Lean.Elab.Tactic.Do.Internal

public section

namespace Lean.Elab.Tactic.Do.Internal.VCGen

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator. -/
structure FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the registry; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- The frame inference metaprogram. -/
  proc : FrameInferenceProc
  /-- Head constant of the frame operator framed with; keys `split`/`impSplit` for `splitLatticeOp?`. -/
  conj : Name
  /-- Builds the frame operator (head constant `conj`) for the goal's assertion type. -/
  op : WPInfo → MetaM Expr
  /-- The lattice split decomposing `conj F R` on the RHS of an entailment. -/
  split : LatticeSplit
  /-- The lattice split decomposing the residual `PreservesSup.upperAdjoint conj F R` (the frame's magic wand)
  on the RHS of an entailment, so the wand never surfaces in a VC. -/
  impSplit : LatticeSplit
  /-- Optional equation `conj r b = <built-in connective>` (e.g. a `meet`). A fallback to *reduce*
  `conj r b` over a nested-base lattice, where the direct `split` cannot peel the extra state
  coordinate; reducing it to the built-in connective lets the meet/ofProp splits decompose it over all
  coordinates. `none` for frames whose flat `split` always suffices. -/
  conjReduce : Option Name := none
  /-- Optional equation `upperAdjoint (conj r) b = <closed form>` (e.g. a cost shift `fun m => b (m+r)`).
  A fallback to *reduce* the residual wand over a nested-base lattice, where the direct `impSplit`
  cannot peel the extra state coordinate; reducing it exposes the body `b` (with its inner `wp`) so the
  normal spec step runs. `none` for frames whose flat `impSplit` always suffices. -/
  impReduce : Option Name := none

unsafe def getFrameProcFromDeclImpl (declName : Name) : ImportM FrameProc := do
  let ctx ← read
  match ctx.env.find? declName with
  | none => throw <| .userError s!"unknown constant '{declName}'"
  | some info =>
    unless info.type.isConstOf ``FrameProc do
      throw <| .userError s!"`{declName}` is not a `FrameProc`"
    IO.ofExcept <| ctx.env.evalConst FrameProc ctx.opts declName

/-- Recover the compiled `FrameProc` value of a `@[frameproc]`-annotated declaration. -/
@[implemented_by getFrameProcFromDeclImpl]
opaque getFrameProcFromDecl (declName : Name) : ImportM FrameProc

/-- The registered frame inference procedures, keyed by the head constant of the program type they
frame, and their splits keyed by frame-operator head constant. -/
structure FrameProcs where
  procs : Std.HashMap Name FrameProc := {}
  /-- Splits for the frame operators `conj F R`, keyed by `conj` head. -/
  splits : Std.HashMap Name LatticeSplit := {}
  /-- Splits for the residual wands `PreservesSup.upperAdjoint conj F R`, keyed by `conj` head. -/
  impSplits : Std.HashMap Name LatticeSplit := {}
  /-- Optional conj-reduction equations (`FrameProc.conjReduce`), keyed by `conj` head. -/
  conjReduces : Std.HashMap Name Name := {}
  /-- Optional wand-reduction equations (`FrameProc.impReduce`), keyed by `conj` head. -/
  impReduces : Std.HashMap Name Name := {}

instance : Inhabited FrameProcs := ⟨{}⟩

def FrameProcs.insert (s : FrameProcs) (_declName : Name) (fp : FrameProc) : FrameProcs :=
  { procs := s.procs.insert fp.prog fp
    splits := s.splits.insert fp.conj fp.split
    impSplits := s.impSplits.insert fp.conj fp.impSplit
    conjReduces := match fp.conjReduce with
      | some eq => s.conjReduces.insert fp.conj eq
      | none => s.conjReduces
    impReduces := match fp.impReduce with
      | some eq => s.impReduces.insert fp.conj eq
      | none => s.impReduces }

abbrev FrameProcExtension := ScopedEnvExtension Name (Name × FrameProc) FrameProcs

def toFrameProcEntry (declName : Name) : ImportM (Name × FrameProc) := do
  return (declName, ← getFrameProcFromDecl declName)

builtin_initialize frameProcExt : FrameProcExtension ←
  registerScopedEnvExtension {
    name         := by exact decl_name%
    mkInitial    := return {}
    ofOLeanEntry := fun _ declName => toFrameProcEntry declName
    toOLeanEntry := fun (declName, _) => declName
    addEntry     := fun s (declName, fp) => s.insert declName fp
  }

/-- The frame inference procedures in scope. -/
def getFrameProcs {m : Type → Type} [Monad m] [MonadEnv m] : m FrameProcs :=
  return frameProcExt.getState (← getEnv)

def addFrameProcAttr (declName : Name) (kind : AttributeKind) : AttrM Unit := do
  ensureAttrDeclIsMeta `frameproc declName kind
  let fp ← getFrameProcFromDecl declName
  frameProcExt.add (declName, fp) kind

builtin_initialize registerBuiltinAttribute {
  ref             := by exact decl_name%
  name            := `frameproc
  descr           := "register a frame inference procedure for `vcgen`"
  applicationTime := .afterCompilation
  add             := fun declName _stx kind => addFrameProcAttr declName kind
}

end Lean.Elab.Tactic.Do.Internal.VCGen
