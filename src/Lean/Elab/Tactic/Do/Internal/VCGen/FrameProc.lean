/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.WPApp
import Std.Internal.Do.Order.Basic
import Lean.Meta.AppBuilder

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
optionally produce a frame `F : R` to peel off. `none` leaves the spec to apply directly.

The caller instantiates and hash-conses `F` before the speculative spec application's metavariable
context is reset, so `F` may mention metavariables assigned during that application. -/
public abbrev VCGen.FrameInferenceProc :=
  Expr → Expr → VCGen.WPApp → Expr → SymM (Option Expr)

/-- How to decompose a lattice operator `head … s⃗` on the RHS of an entailment: the distribution and
unfolding `rewrites` that saturate it, and the terminal `⊑`-introduction `terminals` that close the
reduced form. `head` keys the split in the `latticeOps` table. A built-in connective contributes an
empty split (the shared built-in rewrites and terminals cover it); a frame operator adds its own. -/
public structure VCGen.LatticeOp where
  /-- Head constant of the operator this split decomposes. Keys the `latticeOps` table. -/
  head : Name
  /-- The number of leading arguments held constant during rule construction: the operator's carrier
  type and its typeclass instances. The operands and excess state arguments after them become the
  rule's schematic parameters. `2` for a connective over a `CompleteLattice` carrier; `0` for a
  monomorphic operator. -/
  numConst : Nat := 2
  /-- Distribution and unfolding equalities that saturate the operator applied to state arguments. -/
  rewrites : Array Name := #[]
  /-- The operator's terminal `⊑`-introduction rule, or `none` when it saturates to another operator's
  terminal. -/
  terminal? : Option Name := none

/-- A frame inference procedure registered with `@[frameproc]`, together with its frame operator. The
`vcgen` frontend selects the one whose `prog` matches the goal program's monad. -/
public structure VCGen.FrameProc where
  /-- Head constant of the program type (the monad) whose `wp` this procedure frames. Keys the
  procedure in the `byProg` index; `vcgen` consults it for a program with that head. -/
  prog : Name
  /-- Builds the frame operator (head constant `op.head`) applied to the goal's assertion type. -/
  mkOpAppM : VCGen.WPApp → MetaM Expr
  /-- The resource type `R` of the operator `op : R → Pred → Pred`, i.e. the domain of `mkOpAppM`'s
  result. Provided directly so `vcgen` reads it without building the operator, which it does only when
  a frame actually applies. -/
  resourceTy : VCGen.WPApp → MetaM Expr
  /-- The lattice split decomposing the frame operator on the RHS of an entailment. -/
  op : VCGen.LatticeOp
  /-- The frame inference metaprogram, or `none` for an operator framed only through an explicit
  `frames` clause. -/
  proc : Option VCGen.FrameInferenceProc

/-- The registered frame inference procedures: `byProg` indexes the procedure by the program monad's
head constant (selected per node in `solve`); `latticeOps` indexes each frame operator's split by
its operator head (consulted by `splitLatticeOp?`). -/
public structure VCGen.FrameProcs where
  byProg : Std.HashMap Name VCGen.FrameProc := {}
  latticeOps : Std.HashMap Name VCGen.LatticeOp := {}

public instance : Inhabited VCGen.FrameProcs := ⟨{}⟩

public def VCGen.FrameProcs.insert (s : FrameProcs) (fp : FrameProc) : FrameProcs :=
  { byProg := s.byProg.insert fp.prog fp
    latticeOps := s.latticeOps.insert fp.op.head fp.op }

/-- The default frame operator: lattice meet `pre ⊓ F`, the Hoare frame every complete lattice carries.
Framed only through an explicit `frames` clause (`proc := none`); used for a monad with no registered
`@[frameproc]`. -/
public def VCGen.meetFrameProc : VCGen.FrameProc where
  prog := ``Lean.Order.meet
  mkOpAppM info := Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
  resourceTy info := pure info.Pred
  op := { head := ``Lean.Order.meet }
  proc := none

end Lean.Elab.Tactic.Do.Internal
