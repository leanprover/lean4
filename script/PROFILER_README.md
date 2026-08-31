# Lean Profiler

Profile Lean programs with demangled names using
[samply](https://github.com/mstange/samply) and
[Firefox Profiler](https://profiler.firefox.com).

Python 3, no external dependencies.

## Quick start

```bash
# One command: record, symbolicate, demangle, and open in Firefox Profiler
script/lean_profile.sh ./my_lean_binary [args...]

# See all options
script/lean_profile.sh --help
```

Requirements: `samply` (`cargo install samply`), `python3`.

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

## Tools

### `script/lean_profile.sh` -- Full profiling pipeline

Records a profile, symbolicates it via samply's API, demangles Lean names,
and opens the result in Firefox Profiler. This is the recommended workflow.

```bash
script/lean_profile.sh ./build/release/stage1/bin/lean src/Lean/Elab/Term.lean
```

Environment variables:

| Variable | Default | Description |
|---|---|---|
| `SAMPLY_RATE` | 1000 | Sampling rate in Hz |
| `SAMPLY_PORT` | 3756 | Port for samply symbolication server |
| `SERVE_PORT` | 3757 | Port for serving the demangled profile |
| `PROFILE_KEEP` | 0 | Set to 1 to keep the temp directory |

### `script/profiler/lean_demangle.py` -- Name demangler

Demangles individual symbol names. Works as a stdin filter (like `c++filt`)
or with arguments.

```bash
echo "l_Lean_Meta_Sym_main" | python3 script/profiler/lean_demangle.py
# Lean.Meta.Sym.main

python3 script/profiler/lean_demangle.py --raw l_foo___redArg
# foo._redArg  (exact name, no postprocessing)
```

As a Python module:

```python
from lean_demangle import demangle_lean_name, demangle_lean_name_raw

demangle_lean_name("l_foo___redArg")       # "foo [arity↓]"
demangle_lean_name_raw("l_foo___redArg")   # "foo._redArg"
```

### `script/profiler/symbolicate_profile.py` -- Profile symbolicator

Calls samply's symbolication API to resolve raw addresses into symbol names,
then demangles them. Used internally by `lean_profile.sh`.

### `script/profiler/serve_profile.py` -- Profile server

Serves a profile JSON file to Firefox Profiler without re-symbolication
(which would overwrite demangled names). Used internally by `lean_profile.sh`.

### `script/profiler/lean_demangle_profile.py` -- Standalone profile rewriter

Demangles names in an already-symbolicated profile file (if you have one
from another source).

```bash
python3 script/profiler/lean_demangle_profile.py profile.json.gz -o demangled.json.gz
```

## Tests

```bash
cd script/profiler && python3 -m unittest test_demangle -v
```

## How it works

The demangler is a faithful port of Lean 4's `Name.demangleAux` from
`src/Lean/Compiler/NameMangling.lean`. It reverses the encoding used by
`Name.mangle` / `Name.mangleAux` which turns hierarchical Lean names into
valid C identifiers:

- `_` separates name components (`Lean.Meta` -> `Lean_Meta`)
- `__` encodes a literal underscore in a component name
- `_xHH`, `_uHHHH`, `_UHHHHHHHH` encode special characters
- `_N_` encodes numeric name components
- `_00` is a disambiguation prefix for ambiguous patterns

After demangling, a postprocessing pass folds compiler-generated suffixes
into human-readable annotations (see [Reading demangled names](#reading-demangled-names)).
