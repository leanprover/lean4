# Lean Profiler

Profile Lean programs with demangled names using
[samply](https://github.com/mstange/samply) and
[Firefox Profiler](https://profiler.firefox.com).

## Quick start

```bash
# Build, record, symbolicate, demangle, and serve in one command
lake profile myexe [args...]

# See all options
lake help profile
```

Requirements: `samply` (`cargo install samply`), `curl`, `gzip`.

## Reading demangled names

The demangler transforms low-level C symbol names into readable Lean names
and annotates them with compact modifiers.

### Basic names

| Raw symbol | Demangled |
|---|---|
| `l_Lean_Meta_Sym_main` | `Lean.Meta.Sym.main` |
| `lp_std_List_map` | `List.map (std)` |
| `_init_l_Foo_bar` | `[init] Foo.bar` |
| `initialize_Init_Data` | `[module_init] Init.Data` |
| `_lean_main` | `[lean] main` |

### Modifier flags `[...]`

Compiler-generated suffixes are folded into a bracket annotation after the
name. These indicate *how* the function was derived from the original source
definition.

| Flag | Meaning | Compiler suffix |
|---|---|---|
| `arity`&darr; | Reduced-arity specialization | `_redArg` |
| `boxed` | Boxed calling-convention wrapper | `_boxed` |
| `impl` | Implementation detail | `_impl` |
| &lambda; | Lambda-lifted closure | `_lam_N`, `_lambda_N`, `_elam_N` |
| `jp` | Join point | `_jp_N` |
| `closed` | Extracted closed subterm | `_closed_N` |
| `private` | Private (module-scoped) definition | `_private.Module.0.` prefix |

Examples:

```
Lean.Meta.Simp.simpLambda [boxed, λ]     -- boxed wrapper of a lambda-lifted closure
Lean.Meta.foo [arity↓, private]           -- reduced-arity version of a private def
```

Multiple flags are comma-separated. Order reflects how they were collected
(innermost suffix first).

### Specializations `spec at ...`

When the compiler specializes a function at a particular call site, the
demangled name shows `spec at <context>` after the base name and its flags.
The context names the function whose body triggered the specialization, and
may carry its own modifier flags:

```
<base-name> [<base-flags>] spec at <context>[<context-flags>]
```

Examples:

```
-- foo specialized at call site in bar
Lean.Meta.foo spec at Lean.Meta.bar

-- foo (with a lambda closure) specialized at bar (with reduced arity and a lambda)
Lean.Meta.foo [λ] spec at Lean.Meta.bar[λ, arity↓]

-- chained specialization: foo specialized at bar, then at baz
Lean.Meta.foo spec at Lean.Meta.bar spec at Lean.Meta.baz[arity↓]
```

Context flags use the same symbols as base flags. When a context has no
flags, the brackets are omitted.

### Other annotations

| Pattern | Meaning |
|---|---|
| `<apply/N>` | Lean runtime apply function (N arguments) |
| `.cold.N` suffix | LLVM cold-path clone (infrequently executed) |
| `(pkg)` suffix | Function from package `pkg` |

## Standalone demangler

`script/profiler/lean_demangle_cli.lean` is a `c++filt`-like filter for Lean
symbol names. It reads mangled names from stdin and writes demangled names to
stdout:

```bash
echo "l_Lean_Meta_Sym_main" | lean --run script/profiler/lean_demangle_cli.lean
# Lean.Meta.Sym.main
```

## How it works

The demangler (`src/Lean/Compiler/NameDemangling.lean`) reverses the encoding
used by `Name.mangle` / `Name.mangleAux` which turns hierarchical Lean names
into valid C identifiers:

- `_` separates name components (`Lean.Meta` -> `Lean_Meta`)
- `__` encodes a literal underscore in a component name
- `_xHH`, `_uHHHH`, `_UHHHHHHHH` encode special characters
- `_N_` encodes numeric name components
- `_00` is a disambiguation prefix for ambiguous patterns

After demangling, a postprocessing pass folds compiler-generated suffixes
into human-readable annotations (see [Reading demangled names](#reading-demangled-names)).
