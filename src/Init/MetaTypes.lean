/-
Copyright (c) Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

namespace Lean

structure NameGenerator where
  namePrefix : Name := `_uniq
  idx        : Nat  := 1
  deriving Inhabited

/-- Syntax objects for a Lean module. -/
structure Module where
  header   : Syntax
  commands : Array Syntax

namespace Meta

inductive TransparencyMode where
  /-- unfold all constants, even those tagged as `@[irreducible]`. -/
  | all
  /-- unfold all constants except those tagged as `@[irreducible]`. -/
  | default
  /-- unfold only constants tagged with the `@[reducible]` attribute. -/
  | reducible
  /-- unfold reducible constants and constants tagged with the `@[instance]` attribute. -/
  | instances
  deriving Inhabited, BEq

inductive EtaStructMode where
  /-- Enable eta for structure and classes. -/
  | all
  /-- Enable eta only for structures that are not classes. -/
  | notClasses
  /-- Disable eta for structures and classes. -/
  | none
  deriving Inhabited, BEq

namespace DSimp

structure Config where
  zeta              : Bool := true
  beta              : Bool := true
  eta               : Bool := true
  etaStruct         : EtaStructMode := .all
  iota              : Bool := true
  proj              : Bool := true
  decide            : Bool := false
  autoUnfold        : Bool := false
  /-- If `failIfUnchanged := true`, then calls to `simp`, `dsimp`, or `simp_all`
  will fail if they do not make progress. -/
  failIfUnchanged   : Bool := true
  /-- If `unfoldPartialApp := true`, then calls to `simp`, `dsimp`, or `simp_all`
  will unfold even partial applications of `f` when we request `f` to be unfolded. -/
  unfoldPartialApp  : Bool := false
  deriving Inhabited, BEq

end DSimp

namespace Simp

def defaultMaxSteps := 100000

structure Config where
  maxSteps          : Nat  := defaultMaxSteps
  maxDischargeDepth : Nat  := 2
  contextual        : Bool := false
  memoize           : Bool := true
  singlePass        : Bool := false
  zeta              : Bool := true
  beta              : Bool := true
  eta               : Bool := true
  etaStruct         : EtaStructMode := .all
  iota              : Bool := true
  proj              : Bool := true
  decide            : Bool := false
  arith             : Bool := false
  autoUnfold        : Bool := false
  /--
    If `dsimp := true`, then switches to `dsimp` on dependent arguments where there is no congruence theorem that allows
    `simp` to visit them. If `dsimp := false`, then argument is not visited.
  -/
  dsimp             : Bool := true
  /-- If `failIfUnchanged := true`, then calls to `simp`, `dsimp`, or `simp_all`
  will fail if they do not make progress. -/
  failIfUnchanged   : Bool := true
  /-- If `ground := true`, then ground terms are reduced. A term is ground when
  it does not contain free or meta variables. Reduction is interrupted at a function application `f ...`
  if `f` is marked to not be unfolded. -/
  ground            : Bool := false
  /-- If `unfoldPartialApp := true`, then calls to `simp`, `dsimp`, or `simp_all`
  will unfold even partial applications of `f` when we request `f` to be unfolded. -/
  unfoldPartialApp  : Bool := false
  deriving Inhabited, BEq

-- Configuration object for `simp_all`
structure ConfigCtx extends Config where
  contextual := true

def neutralConfig : Simp.Config := {
  zeta              := false
  beta              := false
  eta               := false
  iota              := false
  proj              := false
  decide            := false
  arith             := false
  autoUnfold        := false
  ground            := false
}

end Simp

inductive Occurrences where
  | all
  | pos (idxs : List Nat)
  | neg (idxs : List Nat)
  deriving Inhabited, BEq

end Lean.Meta
