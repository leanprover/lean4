/-
Copyright (c) Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Core

public section

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

/--
Controls which constants `isDefEq` (definitional equality) and `whnf` (weak head normal form)
are allowed to unfold.

## Background: "try-hard" vs "speculative" modes

During **type checking of user input**, we assume the input is most likely correct, and we want
Lean to try hard before reporting a failure. Here, it is fine to unfold `[semireducible]` definitions
(the `.default` setting).

During **proof automation** (`simp`, `rw`, type class resolution), we perform many speculative
`isDefEq` calls — most of which *fail*. In this setting, we do *not* want to try hard: unfolding
too many definitions is a performance footgun. This is why `.reducible` exists.

## The transparency hierarchy

The levels form a linear order: `none < reducible < instances < default < all`.
Each level unfolds everything the previous level does, plus more:

- **`reducible`**: Only unfolds `[reducible]` definitions. Used for speculative `isDefEq` checks
  (e.g., discrimination tree lookups in `simp`, type class resolution). Think of `[reducible]` as
  `[inline]` for type checking and indexing.

- **`instances`**: Also unfolds `[implicit_reducible]` definitions. Instance diamonds are common:
  for example, `Add Nat` can come from a direct instance or via `Semiring`. These instances are all
  definitionally equal but structurally different, so `isDefEq` must unfold them to confirm equality.
  This level also handles definitions used in types that appear in implicit arguments (e.g.,
  `Nat.add`, `Array.size`). However, these definitions must not be *eagerly* reduced (instances
  become huge terms), and discrimination trees do not index them. This makes `.instances` safe for
  speculative checks involving implicit arguments without the performance cost of `.default`.

- **`default`**: Also unfolds `[semireducible]` definitions (anything not `[irreducible]`).
  Used for type checking user input where we want to try hard.

- **`all`**: Also unfolds `[irreducible]` definitions. Rarely used.

## Implicit arguments and transparency

When proof automation (e.g., `simp`, `rw`) applies a lemma, explicit arguments are checked at the
caller's transparency (typically `.reducible`). But implicit arguments are often "invisible" to the
user — if a lemma fails to apply because of an implicit argument mismatch, the user is confused.
Historically, Lean bumped transparency to `.default` for implicit arguments, but this eventually
became a performance bottleneck in Mathlib. The option `backward.isDefEq.respectTransparency`
(default: `true`) disables this bump. Instead, instance-implicit arguments (`[..]`) are checked at
`.instances`, and other implicit arguments are checked at the caller's transparency.

See also: `ReducibilityStatus`, `backward.isDefEq.respectTransparency`,
`backward.whnf.reducibleClassField`.
-/
inductive TransparencyMode where
  /-- Unfolds all constants, even those tagged as `@[irreducible]`. -/
  | all
  /-- Unfolds all constants except those tagged as `@[irreducible]`. Used for type checking
  user-written terms where we expect the input to be correct and want to try hard. -/
  | default
  /-- Unfolds only constants tagged with the `@[reducible]` attribute. Used for speculative
  `isDefEq` in proof automation (`simp`, `rw`, type class resolution) where most checks fail
  and we must not try too hard. -/
  | reducible
  /-- Unfolds reducible constants and constants tagged with `@[implicit_reducible]`.
  Used for checking implicit arguments during proof automation, and for unfolding
  class projections applied to instances. Instance diamonds (e.g., `Add Nat` from a direct instance
  vs from `Semiring`) are definitionally equal but structurally different, so `isDefEq` must unfold
  them. Also handles definitions used in types of implicit arguments (e.g., `Nat.add`, `Array.size`). -/
  | instances
  /-- Do not unfold anything. -/
  | none
  deriving Inhabited, BEq

/-- Which structure types should eta be used with? -/
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
  When `true` (default: `true`), performs zeta reduction of `let` and `have` expressions.
  That is, `let x := v; e[x]` reduces to `e[v]`.
  If `zetaHave` is `false` then `have` expressions are not zeta reduced.
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
  When `true` (default: `false`), unfolds applications of functions defined by pattern matching, when one of the patterns applies.
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
  That is, given a local context containing `x : t := e`, then the free variable `x` reduces to `e`.
  Otherwise, `x` must be provided as a `simp` argument.
  -/
  zetaDelta         : Bool := false
  /--
  When `index` (default : `true`) is `false`, `simp` will only use the root symbol
  to find candidate `simp` theorems. It approximates Lean 3 `simp` behavior.
  -/
  index             : Bool := true
  /--
  When `true` (default : `true`), then `simp` will remove unused `let` and `have` expressions:
  `let x := v; e` simplifies to `e` when `x` does not occur in `e`.
  -/
  zetaUnused : Bool := true
  /--
  When `false` (default: `true`), then disables zeta reduction of `have` expressions.
  If `zeta` is `false`, then this option has no effect.
  Unused `have`s are still removed if `zeta` or `zetaUnused` are true.
  -/
  zetaHave : Bool := true
  /--
  If `locals` is `true`, `dsimp` will unfold all definitions from the current file.
  For local theorems, use `+suggestions` instead.
  -/
  locals : Bool := false
  /--
  If `instances` is `true`, `dsimp` will visit instance arguments.
  If option `backward.dsimp.instances` is `true`, it overrides this field.
  -/
  instances : Bool := false
  deriving Inhabited, BEq

end DSimp

namespace Simp

@[inline]
def defaultMaxSteps := 100000

/--
The configuration for `simp`.
Passed to `simp` using, for example, the `simp +contextual` or `simp (maxSteps := 100000)` syntax.

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
  When true (default: `true`) then the simplifier caches the result of simplifying each sub-expression, if possible.
  -/
  memoize           : Bool := true
  /--
  When `singlePass` is `true` (default: `false`), the simplifier runs through a single round of simplification,
  which consists of running pre-methods, recursing using congruence lemmas, and then running post-methods.
  Otherwise, when it is `false`, it iteratively applies this simplification procedure.
  -/
  singlePass        : Bool := false
  /--
  When `true` (default: `true`), performs zeta reduction of `let` and `have` expressions.
  That is, `let x := v; e[x]` reduces to `e[v]`.
  If `zetaHave` is `false` then `have` expressions are not zeta reduced.
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
  When `true` (default: `false`), unfolds applications of functions defined by pattern matching, when one of the patterns applies.
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
  That is, given a local context containing `x : t := e`, then the free variable `x` reduces to `e`.
  Otherwise, `x` must be provided as a `simp` argument.
  -/
  zetaDelta         : Bool := false
  /--
  When `index` (default : `true`) is `false`, `simp` will only use the root symbol
  to find candidate `simp` theorems. It approximates Lean 3 `simp` behavior.
  -/
  index             : Bool := true
  /--
  If `implicitDefEqProofs := true`, `simp` does not create proof terms when the
  input and output terms are definitionally equal.
  -/
  implicitDefEqProofs : Bool := true
  /--
  When `true` (default : `true`), then `simp` removes unused `let` and `have` expressions:
  `let x := v; e` simplifies to `e` when `x` does not occur in `e`.
  This option takes precedence over `zeta` and `zetaHave`.
  -/
  zetaUnused : Bool := true
  /--
  When `true` (default : `true`), then `simp` catches runtime exceptions and
  converts them into `simp` exceptions.
  -/
  catchRuntime : Bool := true
  /--
  When `false` (default: `true`), then disables zeta reduction of `have` expressions.
  If `zeta` is `false`, then this option has no effect.
  Unused `have`s are still removed if `zeta` or `zetaUnused` are true.
  -/
  zetaHave : Bool := true
  /--
  When `true` (default : `true`), then `simp` will attempt to transform `let`s into `have`s
  if they are non-dependent. This only applies when `zeta := false`.
  -/
  letToHave : Bool := true
  /--
  When `true` (default: `true`), `simp` tries to realize constant `f.congr_simp`
  when constructing an auxiliary congruence proof for `f`.
  This option exists because the termination prover uses `simp` and `withoutModifyingEnv`
  while constructing the termination proof. Thus, any constant realized by `simp`
  is deleted.
  -/
  congrConsts : Bool := true
  /--
  When `true` (default: `true`), the bitvector simprocs use `BitVec.ofNat` for representing
  bitvector literals.
  -/
  bitVecOfNat : Bool := true
  /--
  When `true` (default: `true`), the `^` simprocs generate an warning it the exponents are too big.
  -/
  warnExponents : Bool := true
  /--
  If `suggestions` is `true`, `simp?` will invoke the currently configured library suggestion engine on the current goal,
  and attempt to use the resulting suggestions as parameters to the `simp` tactic.
  -/
  suggestions : Bool := false
  /--
  Maximum number of library suggestions to use. If `none`, uses the default limit.
  Only relevant when `suggestions` is `true`.
  -/
  maxSuggestions : Option Nat := none
  /--
  If `locals` is `true`, `simp` will unfold all definitions from the current file.
  For local theorems, use `+suggestions` instead.
  -/
  locals : Bool := false
  /--
  If `instances` is `true`, `simp` will visit instance arguments.
  If option `backward.dsimp.instances` is `true`, it overrides this field.
  -/
  instances : Bool := false
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
  zetaUnused        := false
  letToHave         := false
}

structure NormCastConfig extends Simp.Config where
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false

end Simp

/-- Configuration for which occurrences that match an expression should be rewritten. -/
inductive Occurrences where
  /-- All occurrences should be rewritten. -/
  | all
  /-- A list of indices for which occurrences should be rewritten. -/
  | pos (idxs : List Nat)
  /-- A list of indices for which occurrences should not be rewritten. -/
  | neg (idxs : List Nat)
  deriving Inhabited, BEq

instance : Coe (List Nat) Occurrences := ⟨.pos⟩

/--
Configuration for the `extract_lets` tactic.
-/
structure ExtractLetsConfig where
  /-- If true (default: false), extract lets from subterms that are proofs.
  Top-level lets are always extracted. -/
  proofs : Bool := false
  /-- If true (default: true), extract lets from subterms that are types.
  Top-level lets are always extracted. -/
  types : Bool := true
  /-- If true (default: false), extract lets from subterms that are implicit arguments. -/
  implicits : Bool := false
  /-- If false (default: true), extracts only top-level lets, otherwise allows descending into subterms.
  When false, `proofs` and `types` are ignored, and lets appearing in the types or values of the
  top-level lets are not themselves extracted. -/
  descend : Bool := true
  /-- If true (default: true), descend into forall/lambda/let bodies when extracting. Only relevant when `descend` is true. -/
  underBinder : Bool := true
  /-- If true (default: false), eliminate unused lets rather than extract them. -/
  usedOnly : Bool := false
  /-- If true (default: true), reuse local declarations that have syntactically equal values.
  Note that even when false, the caching strategy for `extract_lets` may result in fewer extracted let bindings than expected. -/
  merge : Bool := true
  /-- When merging is enabled, if true (default: true), make use of pre-existing local definitions in the local context. -/
  useContext : Bool := true
  /-- If true (default: false), then once `givenNames` is exhausted, stop extracting lets. Otherwise continue extracting lets. -/
  onlyGivenNames : Bool := false
  /-- If true (default: false), then when no name is provided for a 'let' expression, the name is used as-is without making it be inaccessible.
  The name still might be inaccessible if the binder name was. -/
  preserveBinderNames : Bool := false
  /-- If true (default: false), lift non-extractable `let`s as far out as possible. -/
  lift : Bool := false

/--
Configuration for the `lift_lets` tactic.
-/
structure LiftLetsConfig extends ExtractLetsConfig where
  lift := true
  preserveBinderNames := true

end Lean.Meta
