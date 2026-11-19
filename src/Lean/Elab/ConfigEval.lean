/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Elab.ConfigEval.Types
public import Lean.Elab.ConfigEval.Basic
public import Lean.Elab.ConfigEval.Commands
public import Lean.Elab.ConfigEval.DeriveEvalTerm
public import Lean.Elab.ConfigEval.DeriveEvalExpr
public import Lean.Elab.ConfigEval.DeriveEvalConfigItem
public import Lean.Elab.ConfigEval.Instances
public import Lean.Elab.ConfigEval.MetaInstances
public import Lean.Elab.ConfigEval.Extra

/-!
# Configuration evaluation

This module provides a system for constructing efficient elaborators for
evaluating configuration syntaxes.

Users should import this module to ensure they have all elaborators and
instances in scope.

The main interfaces are the `declare_core_config_elab`, `declare_term_config_elab`,
`declare_config_elab` and `declare_command_config_elab` commands. These are
macros that construct configuration elaborators from lower-level components.
Metaprogram authors may choose to directly interface with the lower-level components instead.

These commands handle the common cases where
1. your configuration type is a `structure` with no parameters, indices, or universes
  (only `Type` is supported);
2. default values are self-contained and not dependent on other fields; and
3. all fields have types that are composed from `Option`, `List`, `Array`, `String`,
  and inductive types in `Type` with no parameters or indices, whose
  constructor fields are similarly composed.

The macros synthesize a self-contained configuration elaboration procedure, analyzing
the `EvalTerm` and `EvalExpr` instances that are currently available or automatically
derivable. These are the components of the system:

- `EvalTerm` instances provide `Term → TermElabM α` functions for evaluation of raw syntax;
  these handle the common cases where an option value is a identifier, application, or other
  simple expression. They are responsible for adding TermInfo when info is enabled, to support
  hovers. One can invoke derivation of a `EvalTerm T` instance with the
  `ensure_eval_term_instance T` command (after `open scoped Lean.Elab.ConfigEval`).
- `EvalExpr` instances provide `Expr → TermElabM α` functions for evaluation of elaborated
  expressions; these handle cases where an option value may require reduction to evaluate.
  Similarly, one can invoke derivation of an `EvalExpr T` instance with the
  `ensure_eval_expr_instance T` command. If needed, there's also
  `derive_eval_expr_instance_using_meta_eval T` for creating a `Meta.evalExpr'`-based evaluator.
- Functions like `ConfigEval.evalExprWithElab` compose `EvalTerm` and `EvalExpr` instances
  into a single procedure that first attempts `EvalTerm`, and, if that fails, applies the
  standard term elaborator and then attempts `EvalExpr`. This way term elaboration can be
  skipped in all but uncommon cases.
- Configuration item interpretation is through `ConfigEval.foldConfigM`, which is a
  procedure with a lax specification for what counts as a configuration item. The idea is:
  - Null nodes are lists of configurations
  - One-argument nodes wrapping null nodes are considered to be wrappers like `optConfig` or `configItem`
  - Two-argument nodes of the form `("+"<|>"-") (atom<|>ident)` are considered to be
    boolean options
  - Five-argument nodes of the form `"(" (atom<|>ident) ":=" syntax ")"` are considered
    to be general configuration items. (It only checks for the presence of `(` and that
    there are two-to-five arguments.)
  - Bare atoms are considered to be positive boolean options
- Configuration evaluation then uses `EvalConfigItem.set` on each item produced by the
  fold, for an `EvalConfigItem` structure defined for the given configuration type.
  The `def_eval_config_item` command can be used to derive this structure. It
  analyzes which `EvalTerm` and `EvalExpr` instances exist and derives missing ones,
  then builds an efficient procedure to process configuration items and apply evaluators.
- Lastly, there are the `declare_core_config_elab`, `declare_term_config_elab`,
  `declare_config_elab`, and `declare_command_config_elab` macros for conveniently
  running the `def_eval_config_item` command and constructing a self-contained
  elaboration function.

The derivation procedures analyze which `EvalTerm`/`EvalExpr` instances already exist
and only derive the "leaf" instances that are necessary to construct `EvalTerm` and
`EvalExpr` instances. The derived instances are made `private local` — since
configuration elaborators are meant to be self-contained, we decided not to let
the additional instances be a side effect of the macros, except in the current section.
The instances can be added globally by manually using the `ensure_*` commands.

## Notes for core Lean

Builtin elaborators should put their configuration types in, for example,
`Init.MetaTypes` or `Init.Meta.Defs` so that hovers can function when
nothing is imported.

Due to the flexibility of `ConfigEval.foldConfigM`, changing the syntax
definitions for custom configurations doesn't generally lead to bootstrapping
issues. Custom configuration options with a non-`Term` values are fine with the caveat
that their use ought to be avoided in the prelude, to avoid bootstrapping issues when their
syntax changes or the custom configuration elaborator changes.

-/
