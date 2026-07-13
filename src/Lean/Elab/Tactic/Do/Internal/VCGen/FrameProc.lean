/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.WPApp

/-!
The metadata a frame inference procedure operates on: the `wp` application metadata `WPApp` and the
`FrameProc` bundling an inference procedure with its frame operator and lattice-split rules.
`@[frameproc]` registration lives in `FrameProcAttr`.
-/

open Lean Meta Sym

namespace Lean.Elab.Tactic.Do.Internal

/-- A frame inference procedure: given the resource type `R` of the applicable frame operator
`op : R → Pred → Pred`, the goal's precondition, the `wp` metadata of a spec-ready program, and the
spec's precondition instantiated at the call site (the RHS of the spec's precondition VC `pre ⊑ ·`),
optionally produce a frame `F : R` to peel off. `none` leaves the spec to apply directly. -/
public abbrev VCGen.FrameInferenceProc :=
  Expr → Expr → VCGen.WPApp → Expr → SymM (Option Expr)

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator. The
`vcgen` frontend selects the one whose `prog` matches the goal program's monad. -/
public structure VCGen.FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the `byProg` index; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- Head constant of the frame operator. Keys the procedure in the `byOp` index, consulted by
  `splitLatticeOp?` to decompose a frame residual `op F R`. -/
  op : Name
  /-- Builds the frame operator (head constant `op`) applied to the goal's assertion type. -/
  mkOpAppM : VCGen.WPApp → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`, i.e. the domain of `mkOpAppM`'s
  result. Provided directly so `vcgen` reads it without building the operator, which it does only when
  a frame actually applies. -/
  resourceTy : VCGen.WPApp → MetaM Expr
  /-- Distribution and unfolding equalities that saturate the frame operator applied to state
  arguments during a lattice split, added to the built-in connective rewrites. -/
  rewrites : Array Name := #[]
  /-- Terminal `⊑`-introduction rules for the frame operator, added to the built-in connective
  terminals during a lattice split. -/
  terminals : Array Name := #[]
  /-- The frame inference metaprogram, or `none` for an operator framed only through an explicit
  `frames` clause. -/
  proc : Option VCGen.FrameInferenceProc

/-- The registered frame inference procedures, indexed two ways into the same database: `byProg` by
the program monad's head constant (selected per node in `solve`), and `byOp` by the frame operator's
head constant (consulted by `splitLatticeOp?` to decompose a frame residual). -/
public structure VCGen.FrameProcs where
  byProg : Std.HashMap Name VCGen.FrameProc := {}
  byOp : Std.HashMap Name VCGen.FrameProc := {}

public instance : Inhabited VCGen.FrameProcs := ⟨{}⟩

public def VCGen.FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp
    byOp := s.byOp.insert fp.op fp }

end Lean.Elab.Tactic.Do.Internal
