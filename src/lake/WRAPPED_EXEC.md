# `LAKE_WRAPPED_EXEC` — wrapped execution hook for Lake

This branch adds an optional hook that lets Lake route per-`lean`
subprocess invocations through an external executable ("the wrapper")
instead of invoking them directly via `rawProc`. The wrapper is opaque
to Lake: it can sandbox the call, look up a result in a
content-addressable cache, record an audit trail, dispatch to a worker
pool over the network, or simply exec the command itself — Lake
doesn't care which.

The patch is two commits:

1. **`refactor: extract pure argv helpers in Build/Actions`** — splits
   `Lake/Build/Actions.lean`'s subprocess-driving functions into pure
   argv-construction helpers (`mkLeanModuleArgs`, `mkCcCompileArgs`,
   `renderRspContents`) and the surrounding IO. No behaviour change to
   `compileLeanModule` / `compileO` / `mkArgs`; the new helpers are
   simply available for tooling that wants to reproduce Lake's exact
   invocations without running them.

2. **`feat(lake): add LAKE_WRAPPED_EXEC hook for wrapping lean execution`**
   — the actual hook. Introduces `Lake/Build/WrappedExec.lean` (manifest
   type + dispatch helper), wires it into the lean-module build path,
   adds a transitive olean closure walker used to populate the
   manifest's `inputs` list, and re-exports the new module from
   `Lake/Build.lean`.

When `$LAKE_WRAPPED_EXEC` is unset, the patched Lake is
byte-for-byte identical in behaviour to upstream — the hook is purely
additive on the existing direct-execution path.

## Motivation

A handful of useful capabilities all want the same shape of hook from
Lake: a way to substitute or augment the per-module subprocess
invocation, given enough information to satisfy it externally.
Examples:

- **Sandboxed execution.** Wrap each `lean` call in a per-job isolated
  filesystem view (landlock, bwrap, sandbox-exec, etc.) using the
  manifest's declared inputs/outputs as the allow-list.
- **Tracing / auditing.** Record argv/env/inputs/outputs per job for
  reproducibility analysis or build provenance.
- **Cache farm integration.** Look up a pre-built result in
  content-addressable storage, only invoking `lean` on a cache miss.
- **Distributed compilation** for large libraries (Mathlib is
  ~8k modules and 90+ minutes single-machine compute on Apple Silicon).

All of these want the same primitive: an interception point per
subprocess invocation where the wrapper sees what Lake was about to
run and the dependencies it needs to satisfy. This patch provides
exactly that, with no opinions about what's on the other side of it.

## Contract

### The env var

```
LAKE_WRAPPED_EXEC=<path-to-executable>
```

When set, Lake routes selected subprocess invocations through the
named binary. When unset, Lake spawns `lean` itself, exactly as
upstream. **This is the only externally visible switch.**

### The manifest

For each routed invocation, Lake writes a JSON manifest to
`$TMPDIR/lake-wrapped-<pid>-<monoNano>-<safe-jobid>.json` and execs
the wrapper with the manifest path as `argv[1]`:

```json
{
  "job_id":          "mathlib_Mathlib.Data.Finset.Basic",
  "cmd":             "/path/to/lean",
  "args":            ["Mathlib/Data/Finset/Basic.lean", "-o", "...", ...],
  "env":             { "LEAN_PATH": "...", ... },
  "cwd":             "/workspace",
  "inputs":          ["Mathlib/.../Basic.lean", ".../Setup.json", ".../Dep.olean", ...],
  "outputs":         [".../Basic.olean", ".../Basic.ilean", ".../Basic.c", ...],
  "workspace":       "/workspace",
  "lake_home":       "/workspace/.lake",
  "toolchain":       "/root/.elan/.../bin",
  "toolchain_root":  "/root/.elan/..."
}
```

Field semantics:

| field             | what it carries                                                                |
|-------------------|--------------------------------------------------------------------------------|
| `cmd / args / env / cwd` | exactly what Lake would have passed to its internal `rawProc`           |
| `inputs`          | every file that must exist on disk before `cmd` runs (source, setup, oleans)   |
| `outputs`         | every file Lake expects to find on disk after `cmd` returns successfully       |
| `workspace`       | the workspace root Lake sees (`Workspace.root.dir`)                            |
| `lake_home`       | the `.lake` directory Lake sees                                                |
| `toolchain`       | path to the `lean` binary's parent dir                                         |
| `toolchain_root`  | toolchain `sysroot` (parent of `toolchain`)                                    |

`workspace / lake_home / toolchain / toolchain_root` are exposed so a
wrapper that runs the command somewhere with a different filesystem
layout (a sandbox root, a worker container, etc.) can rewrite the
manifest's paths into its own view.

### The wrapper return shape

The wrapper MUST return:

- **exit code**: 0 on successful `lean` run, non-zero on `lean` failure.
- **stdout**: `lean`'s stdout, byte-for-byte (Lake parses JSON-encoded
  diagnostics out of this stream).
- **stderr**: `lean`'s stderr, byte-for-byte (Lake surfaces this
  verbatim).

Whatever wrapper implementation produces those three things is
indistinguishable from a direct `lean` invocation from Lake's perspective.

### What Lake guarantees in return

- **Manifest cleanup**. After the wrapper exits (any exit code), Lake
  attempts `IO.FS.removeFile manifestPath catch _ => pure ()`. The
  wrapper MUST NOT delete the manifest itself.
- **Local fallback**. If `$LAKE_WRAPPED_EXEC` is unset OR the call site
  passes `lakeRoots = none`, the dispatcher falls through to plain
  `rawProc`. Lets call sites be hooked one at a time.
- **Input closure computed ahead of time**. `collectLeanInputClosure`
  walks Lake's dependency graph once per job; the wrapper doesn't need
  to do any graph walking on its own.
- **Setup file is an input, not an output**. Lake writes the per-module
  `setup.json` to disk before invoking the wrapper; it's listed in
  `inputs` but explicitly excluded from `outputs`. The wrapper must respect
  this — translating it per-worker if needed, but never shipping it
  back as a build artifact.
- **Stable manifest filename pattern**: `lake-wrapped-<pid>-<monoNano>-<safe-jobid>.json`
  in `$TMPDIR`. Unique across concurrent Lake processes.

## What's currently hooked

Today the hook is wired only at `compileLeanModule` (the per-module
`lean` invocation). The dispatcher (`Lake.WrappedExec.runRawProcOrWrapped`)
itself is generic and could be threaded through any other subprocess
call site — `compileO`, `compileSharedLib`, `compileExe`, etc. — by
computing inputs/outputs for that proc kind and passing
`lakeRoots := some ...`. Each is an additive change that doesn't
disturb call sites left as `lakeRoots := none`.

## What stays Lake's responsibility

- **Build scheduling**. Lake decides which jobs run when. The wrapper
  sees jobs one at a time, in whatever order Lake's scheduler dispatches
  them.
- **Cache hits, hash sidecars, incremental rebuilds**. Because the hook
  intercepts below Lake's job layer, all of Lake's normal caching
  semantics apply unchanged. A no-op rebuild dispatches zero wrapper
  calls; the first build dispatches one per missed lean job.
- **Diagnostic parsing**. Lake reads JSON-encoded diagnostics from the
  wrapper's stdout the same way it reads them from `lean`'s.
- **Manifest lifecycle** (see above).

## What's deliberately *not* part of this patch

- **No orchestration or wrapping logic in Lake.** The wrapper binary
  is opaque; what it does between receiving the manifest and exiting
  is its concern.
- **No assumptions about what the wrapper does.** Sandbox, cache
  lookup, dispatch, plain exec — Lake makes no distinction.
- **No protocol assumptions.** The manifest is JSON-on-disk; the
  wrapper is an exec'd binary. The hook is silent about HTTP, gRPC,
  RDMA, shared memory, or any other transport.

## Example consumers

Anything that accepts `<wrapper> <manifest.json>` and returns
`exit + stdout + stderr` qualifies.

### Trivial passthrough

```sh
#!/usr/bin/env bash
# wrapper-passthrough: read manifest, exec exactly what Lake would have run.
set -e
m="$1"
cmd=$(jq -r '.cmd' "$m")
mapfile -t args < <(jq -r '.args[]' "$m")
mapfile -t env_kvs < <(jq -r '.env | to_entries[] | "\(.key)=\(.value)"' "$m")
cwd=$(jq -r '.cwd // ""' "$m")
[[ -n "$cwd" ]] && cd "$cwd"
exec env "${env_kvs[@]}" "$cmd" "${args[@]}"
```

Useful sanity check: builds with `LAKE_WRAPPED_EXEC=./wrapper-passthrough`
should be byte-for-byte identical to plain `lake build`. Verifies that
the hook itself introduces no behavioural changes.

### Sandboxing — execution under an isolation primitive

The manifest lists every file `lean` should be allowed to read
(`inputs`) and write (`outputs`). Combined with `cmd`/`args`/`env`/`cwd`,
that's exactly enough to construct a sandbox view. A landlock-style
sandbox wrapper looks like:

```sh
#!/usr/bin/env bash
# wrapper-sandbox: run lean under landlock, allowing only the manifest's
# declared input/output paths plus the toolchain dir.
set -e
m="$1"
cmd=$(jq -r '.cmd' "$m")
mapfile -t args < <(jq -r '.args[]' "$m")
mapfile -t env_kvs < <(jq -r '.env | to_entries[] | "\(.key)=\(.value)"' "$m")
mapfile -t read_paths < <(jq -r '.inputs[]' "$m")
mapfile -t write_paths < <(jq -r '.outputs[]' "$m")
toolchain=$(jq -r '.toolchain_root' "$m")

# Hand the read/write sets to your isolation tool of choice
# (landlock-sandboxer, bwrap, firejail, sandbox-exec on macOS, …).
# Conceptually:
exec landlock-sandboxer \
    --ro $(printf -- "--ro %q " "${read_paths[@]}" "$toolchain") \
    --rw $(printf -- "--rw %q " "${write_paths[@]}") \
    -- env "${env_kvs[@]}" "$cmd" "${args[@]}"
```

A sandbox wrapper like this lets `lake build` run in a per-job isolated
view of the filesystem without changing anything in Lake itself. The
hook is exactly the surface needed: Lake declares its dependencies,
the wrapper enforces them at OS level.

### Distributed orchestration

A reference distributed consumer is a Go orchestrator (coordinator +
worker pool + per-job wrapper) that ships inputs to workers over
gRPC + HTTP/2 cleartext, runs `lean` on the assigned worker, and
reflects outputs back to Lake's filesystem. The same `inputs` /
`outputs` lists that make sandboxing possible also drive what the
orchestrator transfers — same data, different consumer.

### Composing wrappers

Wrappers compose by chaining: the wrapper Lake invokes can do its own
work and then exec a downstream wrapper, since the downstream's
interface is the same `<binary> <manifest.json>` shape. Two natural
composition patterns:

**Outer-sandbox + inner-dispatch.** An outer wrapper applies a
sandbox using the manifest's declared inputs/outputs, then exec's
the inner wrapper which does the actual dispatch (to a worker pool,
a cache lookup, whatever). Useful when the outer policy should
hold regardless of where the work eventually runs:

```sh
#!/usr/bin/env bash
# wrapper-sandbox-then-dispatch: enforce sandbox before delegating.
set -e
m="$1"
mapfile -t read_paths  < <(jq -r '.inputs[]'  "$m")
mapfile -t write_paths < <(jq -r '.outputs[]' "$m")
exec landlock-sandboxer \
    --ro $(printf -- "--ro %q " "${read_paths[@]}") \
    --rw $(printf -- "--rw %q " "${write_paths[@]}") \
    -- /path/to/wrapper-dispatch "$m"
```

**Outer-dispatch + inner-sandbox at the consumer.** A dispatching
wrapper ships the manifest somewhere (different process, different
container, different host); on the receiving side, the actual `lean`
invocation is itself wrapped in a sandbox, using the same
`inputs`/`outputs`-based isolation as the standalone sandbox wrapper
above — it just runs after the work has been materialized in
whichever environment received the dispatch.

Either is a small change relative to the non-composed configurations:
the sandbox wrapper treats the dispatching wrapper as "the command
to run after isolating", or the dispatched-to environment treats the
sandbox as "the wrapper to apply before `exec lean`". Neither
requires any further changes to Lake.

## Limitations / non-goals (today)

- Only `compileLeanModule` is hooked. C compilation (`compileO`),
  linking (`compileSharedLib`, `compileExe`), archive (`compileStaticLib`)
  are not hooked yet — they continue to run via `rawProc`. (They
  could be hooked the same way; not in this patch.)
- The transitive olean closure used to populate `inputs` is a strict
  superset of `setup.importArts` (the exported-imports view). Lean's
  olean loader follows non-exported references at LEAN_PATH lookup
  time; in an unwrapped build Lake's build dir is fully populated so
  the difference is invisible, but for wrapped-exec we must declare
  the broader set in `inputs`. The walker is straightforward but not
  minimal — it lists everything `lean`'s loader might reach, not only
  what it actually opens during a specific compile.
- For each module-style import the walker contributes `.olean`, `.ir`,
  `.olean.server`, and `.olean.private`. Per `Lean/Setup.lean`'s
  `ImportArtifacts.oleanParts`, batch compilation skips `.olean.server`
  unless `.olean.private` is also present, and `.olean.private` is
  populated only for `importAll` imports. A future tightening could
  drop the server/private contributions for non-`importAll` imports
  in batch builds (rough estimate: ~30–40% fewer files in the
  manifest), at the cost of teaching the walker about `lean`'s
  batch-vs-server modes — which is the kind of coupling we've
  deliberately kept out of the contract so far.
