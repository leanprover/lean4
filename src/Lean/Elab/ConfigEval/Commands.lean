/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Init.Notation

/-!
# Syntax definitions for commands

Elaborators and macros for these notations are defined in `ConfigEval.Builtins`.
-/

public section

namespace Lean.Elab.ConfigEval

/--
`ensure_eval_term_instance t` ensures there is a `ConfigItem.EvalTerm t` instance by
deriving one or more instances if it needs to.
-/
scoped syntax (name := ensureEvalTermInstance) (visibility)? attrKind "ensure_eval_term_instance " term : command

/--
`ensure_eval_expr_instance t` ensures there is a `ConfigItem.EvalExpr t` instance by
deriving one or more instances if it needs to.
-/
scoped syntax (name := ensureEvalExprInstance) (visibility)? attrKind "ensure_eval_expr_instance " term : command

/--
`ensure_eval_term_expr_instances t` is a macro for running both `ensure_eval_term_instance t`
and `ensure_eval_expr_instance t`, which ensurs there are `ConfigItem.EvalTerm t` and
`ConfigItem.EvalExpr t` instances by deriving one or more instances if it needs to.
-/
scoped syntax (name := ensureEvalTermExprInstances) (visibility)? attrKind "ensure_eval_term_expr_instances " term : command

/--
`derive_eval_expr_instance_using_meta_eval type` defines a `ConfigItem.EvalExpr type` instance
using `Meta.evalExpr'` to evaluate expressions. This sort of item evaluator is a reasonable
backup strategy for infrequently used configuration options, if term- or expression-based
evaluation does not work and the cost of compilation is acceptible.

This should be avoided in core Lean due to the difficulties it creates for bootstrapping.
-/
scoped syntax (name := deriveEvalExprUsingMeta) (visibility)? attrKind "derive_eval_expr_instance_using_meta_eval " term : command

/-- `omit f1, f2, f3` disables generating setters for fields `f1`, `f2`, and `f3`
of the structure. -/
syntax configEntryOmit := &"omit " ident,+,?
syntax configEntryHandlerKeyPrefix := ident (noWs "." noWs "*")?
syntax configEntryHandlerKeyWildcard := "*"
/--
- `key` matches a specific key
- `key.*` matches any keys for which `key` is a proper prefix
- `*` matches all keys
-/
syntax configEntryHandlerKey := configEntryHandlerKeyPrefix <|> configEntryHandlerKeyWildcard
/--
`option key := fun cfg item => ...` adds a configuration option named `key` with the given
expression as its handler. The handler is only called when the key is an exact match.
The provided value is in `item.value`. Such a handler implies `omit key`.

`option key.* := fun cfg item => ...` adds configuration options with `key` as a proper prefix.
The most-specific `*` handler is called if no handlers for exact matches apply.
-/
syntax configEntryHandler := &"option " configEntryHandlerKey " := " term
syntax configEntry := ppGroup(configEntryOmit <|> configEntryHandler)
syntax configEntries := " where" sepByIndentSemicolon(configEntry)

/--
`def_eval_config_item f binders* for struct` defines a `ConfigEval.EvalConfigItem struct` structure named `f`
parameterized by the given binders. This structure contains a setter for updating a configuration
object of type `struct`.

The command will transitively derive any necessary `ConfigEval.EvalTerm`/`ConfigEval.EvalExpr`
instances to support evaluation of configuration options for structure fields.
The syntax supports `public`/`private` modifiers. It also supports `scoped`/`local`, which apply
to any derived instances.

The `EvalConfigItem struct` structure can be customized with a `where` clause.
The possible items of the `where` clause are:
- `omit f1, f2, f3` disables generating setters for fields `f1`, `f2`, and `f3` of `struct`
- `option key := fun cfg item => ...` adds a configuration option named `key` with the given
expression as its handler. The handler is only called when the key is an exact match.
The provided value is in `item.value`. Such a handler implies `omit key`.
- `option key* := fun cfg item => ...` adds configuration options with `key` as a proper prefix.
The most-specific `*` handler is called if no handlers for exact matches apply.
-/
syntax (name := defEvalConfigItemCmd) (docComment)? (visibility)? attrKind
  "def_eval_config_item " ident (bracketedBinder)* " for " ident (configEntries)? : command

/--
`declare_core_config_elab f struct binders* [where ...]` defines a configuration elaborator
```lean
f binders* (cfg : Syntax) (init : struct := {}) (logExceptions : Bool := false) : CoreM struct
```
that evaluates the `cfg` configuration items to update `init`.
Acceptable configuration syntax is documented in `Lean.Elab.ConfigEval.foldConfigM`,
which includes anything that looks like `Lean.Parser.Term.optConfig`, possibly wrapped
in null nodes.

The command will transitively derive any necessary `ConfigEval.EvalTerm`/`ConfigEval.EvalExpr`
instances to support evaluation of configuration options for structure fields.
These instances will be `private local`.

See `ConfigEval.defEvalConfigItemCmd` for further documentation.

See also `declare_term_config_elab`, `declare_config_elab`, and `declare_command_config_elab`.
-/
syntax (name := declareCoreConfigElab) (docComment)? (visibility)?
  "declare_core_config_elab" ident ident (bracketedBinder)* (configEntries)? : command

/--
`declare_term_config_elab f struct binders* [where ...]` defines a configuration elaborator
```lean
f binders* (cfg : Syntax) (init : struct := {}) (logExceptions : Bool := true) : TermElabM struct
```
that evaluates the `cfg` configuration items to update `init`.
Acceptable configuration syntax is documented in `Lean.Elab.ConfigEval.foldConfigM`,
which includes anything that looks like `Lean.Parser.Term.optConfig`, possibly wrapped
in null nodes.

When `logExceptions` is true, it uses the current `errToSorry` state to decide whether or not to
recover by logging errors and skipping invalid options.

The command will transitively derive any necessary `ConfigEval.EvalTerm`/`ConfigEval.EvalExpr`
instances to support evaluation of configuration options for structure fields.
These instances will be `private local`.

See `ConfigEval.defEvalConfigItemCmd` for further documentation.

See also `declare_core_config_elab`, `declare_config_elab`, and `declare_command_config_elab`.
-/
syntax (name := declareTermConfigElab) (docComment)? (visibility)?
  "declare_term_config_elab" ident ident (bracketedBinder)* (configEntries)? : command

/--
`declare_config_elab f struct binders* [where ...]` defines a configuration elaborator
```lean
f binders* (cfg : Syntax) (init : struct := {}) (logExceptions : Bool := true) : TacticM struct
```
that evaluates the `cfg` configuration items to update `init`.
Acceptable configuration syntax is documented in `Lean.Elab.ConfigEval.foldConfigM`,
which includes anything that looks like `Lean.Parser.Term.optConfig`, possibly wrapped
in null nodes.

When `logExceptions` is true, it uses the current `recover` state to decide whether or not to
recover by logging errors and skipping invalid options.

The command will transitively derive any necessary `ConfigEval.EvalTerm`/`ConfigEval.EvalExpr`
instances to support evaluation of configuration options for structure fields.
These instances will be `private local`.

See `ConfigEval.defEvalConfigItemCmd` for further documentation.

See also `declare_core_config_elab`, `declare_term_config_elab`, and `declare_command_config_elab`.
-/
syntax (name := declareTacticConfig) (docComment)? (visibility)?
  "declare_config_elab" ident ident (bracketedBinder)* (configEntries)? : command

/--
`declare_core_config_elab f struct binders* [where ...]` defines a configuration elaborator
```lean
f binders* (cfg : Syntax) (init : struct := {}) (logExceptions : Bool := true) : CommandElabM struct
```
that evaluates the `cfg` configuration items to update `init`.
Acceptable configuration syntax is documented in `Lean.Elab.ConfigEval.foldConfigM`,
which includes anything that looks like `Lean.Parser.Term.optConfig`, possibly wrapped
in null nodes.

The command will transitively derive any necessary `ConfigEval.EvalTerm`/`ConfigEval.EvalExpr`
instances to support evaluation of configuration options for structure fields.
These instances will be `private local`.

See `ConfigEval.defEvalConfigItemCmd` for further documentation.

See also `declare_core_config_elab`, `declare_term_config_elab`, and `declare_config_elab`.
-/
syntax (name := declareCommandConfig) (docComment)? (visibility)?
  "declare_command_config_elab" ident ident (bracketedBinder)* (configEntries)? : command

end Lean.Elab.ConfigEval
