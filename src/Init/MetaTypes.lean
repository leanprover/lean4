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

/--
The configuration for `dsimp`.
Passed to `dsimp` using, for example, the `dsimp (config := {zeta := false})` syntax.

Implementation note: this structure is only used for processing the `(config := ...)` syntax, and it is not used internally.
It is immediately converted to `Lean.Meta.Simp.Config` by `Lean.Elab.Tactic.elabSimpConfig`.
-/
structure Config where
  /--
  When `true` (default: `true`), performs zeta reduction of let expressions.
  That is, `let x := v; e[x]` reduces to `e[v]`.
  See also `zetaDelta`.
  -/
  zeta              : Bool := true
  /--
  When `true` (default: `true`), performs beta reduction of applications of `fun` expressions.
  That is, `(fun x => e[x]) v` reduces to `e[v]`.
  -/
  beta              : Bool := true
  /--
  TODO (currently unimplemented). When `true` (default: `true`), performs eta reduction for `fun` expressions.
  That is, `(fun x => f x)` reduces to `f`.
  -/
  eta               : Bool := true
  /--
  Configures how to determine definitional equality between two structure instances.
  See documentation for `Lean.Meta.EtaStructMode`.
  -/
  etaStruct         : EtaStructMode := .all
  /--
  When `true` (default: `true`), reduces `match` expressions applied to constructors.
  -/
  iota              : Bool := true
  /--
  When `true` (default: `true`), reduces projections of structure constructors.
  -/
  proj              : Bool := true
  /--
  When `true` (default: `false`), rewrites a proposition `p` to `True` or `False` by inferring
  a `Decidable p` instance and reducing it.
  -/
  decide            : Bool := false
  /--
  When `true` (default: `false`), unfolds definitions.
  This can be enabled using the `simp!` syntax.
  -/
  autoUnfold        : Bool := false
  /--
  If `failIfUnchanged` is `true` (default: `true`), then calls to `simp`, `dsimp`, or `simp_all`
  will fail if they do not make progress.
  -/
  failIfUnchanged   : Bool := true
  /--
  If `unfoldPartialApp` is `true` (default: `false`), then calls to `simp`, `dsimp`, or `simp_all`
  will unfold even partial applications of `f` when we request `f` to be unfolded.
  -/
  unfoldPartialApp  : Bool := false
  /--
  When `true` (default: `false`), local definitions are unfolded.
  That is, given a local context containing entry `x : t := e`, the free variable `x` reduces to `e`.
  -/
  zetaDelta         : Bool := false
  /--
  When `index` (default : `true`) is `false`, `simp` will only use the root symbol
  to find candidate `simp` theorems. It approximates Lean 3 `simp` behavior.
  -/
  index             : Bool := true
  deriving Inhabited, BEq

end DSimp

namespace Simp

def defaultMaxSteps := 100000

/--
The configuration for `simp`.
Passed to `simp` using, for example, the `simp (config := {contextual := true})` syntax.

See also `Lean.Meta.Simp.neutralConfig` and `Lean.Meta.DSimp.Config`.
-/
structure Config where
  /--
  The maximum number of subexpressions to visit when performing simplification.
  The default is 100000.
  -/
  maxSteps          : Nat  := defaultMaxSteps
  /--
  When simp discharges side conditions for conditional lemmas, it can recursively apply simplification.
  The `maxDischargeDepth` (default: 2) is the maximum recursion depth when recursively applying simplification to side conditions.
  -/
  maxDischargeDepth : Nat  := 2
  /--
  When `contextual` is true (default: `false`) and simplification encounters an implication `p → q`
  it includes `p` as an additional simp lemma when simplifying `q`.
  -/
  contextual        : Bool := false
  /--
  When true (default: `true`) then the simplifier caches the result of simplifying each subexpression, if possible.
  -/
  memoize           : Bool := true
  /--
  When `singlePass` is `true` (default: `false`), the simplifier runs through a single round of simplification,
  which consists of running pre-methods, recursing using congruence lemmas, and then running post-methods.
  Otherwise, when it is `false`, it iteratively applies this simplification procedure.
  -/
  singlePass        : Bool := false
  /--
  When `true` (default: `true`), performs zeta reduction of let expressions.
  That is, `let x := v; e[x]` reduces to `e[v]`.
  See also `zetaDelta`.
  -/
  zeta              : Bool := true
  /--
  When `true` (default: `true`), performs beta reduction of applications of `fun` expressions.
  That is, `(fun x => e[x]) v` reduces to `e[v]`.
  -/
  beta              : Bool := true
  /--
  TODO (currently unimplemented). When `true` (default: `true`), performs eta reduction for `fun` expressions.
  That is, `(fun x => f x)` reduces to `f`.
  -/
  eta               : Bool := true
  /--
  Configures how to determine definitional equality between two structure instances.
  See documentation for `Lean.Meta.EtaStructMode`.
  -/
  etaStruct         : EtaStructMode := .all
  /--
  When `true` (default: `true`), reduces `match` expressions applied to constructors.
  -/
  iota              : Bool := true
  /--
  When `true` (default: `true`), reduces projections of structure constructors.
  -/
  proj              : Bool := true
  /--
  When `true` (default: `false`), rewrites a proposition `p` to `True` or `False` by inferring
  a `Decidable p` instance and reducing it.
  -/
  decide            : Bool := false
  /--  When `true` (default: `false`), simplifies simple arithmetic expressions. -/
  arith             : Bool := false
  /--
  When `true` (default: `false`), unfolds definitions.
  This can be enabled using the `simp!` syntax.
  -/
  autoUnfold        : Bool := false
  /--
  When `true` (default: `true`) then switches to `dsimp` on dependent arguments
  if there is no congruence theorem that would allow `simp` to visit them.
  When `dsimp` is `false`, then the argument is not visited.
  -/
  dsimp             : Bool := true
  /--
  If `failIfUnchanged` is `true` (default: `true`), then calls to `simp`, `dsimp`, or `simp_all`
  will fail if they do not make progress.
  -/
  failIfUnchanged   : Bool := true
  /--
  If `ground` is `true` (default: `false`), then ground terms are reduced.
  A term is ground when it does not contain free or meta variables.
  Reduction is interrupted at a function application `f ...` if `f` is marked to not be unfolded.
  Ground term reduction applies `@[seval]` lemmas.
  -/
  ground            : Bool := false
  /--
  If `unfoldPartialApp` is `true` (default: `false`), then calls to `simp`, `dsimp`, or `simp_all`
  will unfold even partial applications of `f` when we request `f` to be unfolded.
  -/
  unfoldPartialApp  : Bool := false
  /--
  When `true` (default: `false`), local definitions are unfolded.
  That is, given a local context containing entry `x : t := e`, the free variable `x` reduces to `e`.
  -/
  zetaDelta         : Bool := false
  /--
  When `index` (default : `true`) is `false`, `simp` will only use the root symbol
  to find candidate `simp` theorems. It approximates Lean 3 `simp` behavior.
  -/
  index             : Bool := true
  /--
  This option does not have any effect (yet).
  -/
  implicitDefEqProofs : Bool := true
  deriving Inhabited, BEq

-- Configuration object for `simp_all`
structure ConfigCtx extends Config where
  contextual := true

/--
A neutral configuration for `simp`, turning off all reductions and other built-in simplifications.
-/
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
  zetaDelta         := false
}

end Simp

inductive Occurrences where
  | all
  | pos (idxs : List Nat)
  | neg (idxs : List Nat)
  deriving Inhabited, BEq

end Lean.Meta
