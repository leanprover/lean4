# `LAKE_REMOTE_EXEC` — remote execution hook for Lake

This branch adds an optional hook that lets Lake route per-`lean`
subprocess invocations through an external executable ("the stub")
instead of running them locally. The stub is opaque to Lake: it can do
nothing (running `lean` itself), dispatch to a worker pool over the
network, hand off to a sandbox runner, ship the work to a CAS-backed
build farm, or anything else.

The patch is two commits:

1. **`refactor: extract pure argv helpers in Build/Actions`** — splits
   `Lake/Build/Actions.lean`'s subprocess-driving functions into pure
   argv-construction helpers (`mkLeanModuleArgs`, `mkCcCompileArgs`,
   `renderRspContents`) and the surrounding IO. No behaviour change to
   `compileLeanModule` / `compileO` / `mkArgs`; the new helpers are
   simply available for tooling that wants to reproduce Lake's exact
   invocations without running them.

2. **`feat(lake): add LAKE_REMOTE_EXEC hook for distributed lean execution`**
   — the actual hook. Introduces `Lake/Build/RemoteExec.lean` (manifest
   type + dispatch helper), wires it into the lean-module build path,
   adds a transitive olean closure walker used to populate the
   manifest's `inputs` list, and re-exports the new module from
   `Lake/Build.lean`.

When `$LAKE_REMOTE_EXEC` is unset, the patched Lake is
byte-for-byte identical in behaviour to upstream — the hook is purely
additive on the existing local-build path.

## Motivation

Lake's build scheduler is excellent at parallelism within a single
host. Several distributed-build use-cases want to lift that parallelism
across hosts:

- **Distributed compilation** for large libraries (Mathlib is
  ~8k modules and 90+ minutes single-machine compute on Apple Silicon).
- **Sandboxed execution**, e.g. routing every `lean` through a
  process-isolating wrapper for reproducibility checks.
- **Cache farm integration** (Bazel-RBE-shaped backends, content-
  addressable storage queues, etc.).

All of these want the same thing from Lake: "let me intercept the
per-module `lean` invocation, given enough information to materialize
it on a remote node." This patch provides exactly that interception
point, with no opinions about what's on the other side of it.

## Contract

### The env var

```
LAKE_REMOTE_EXEC=<path-to-executable>
```

When set, Lake routes selected subprocess invocations through the
named binary. When unset, Lake spawns `lean` itself, exactly as
upstream. **This is the only externally visible switch.**

### The manifest

For each routed invocation, Lake writes a JSON manifest to
`$TMPDIR/lake-remote-<pid>-<monoNano>-<safe-jobid>.json` and execs
the stub with the manifest path as `argv[1]`:

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
| `workspace`       | head-side workspace root (`Workspace.root.dir`)                                |
| `lake_home`       | head-side `.lake` directory                                                    |
| `toolchain`       | path to the `lean` binary's parent dir                                         |
| `toolchain_root`  | toolchain `sysroot` (parent of `toolchain`)                                    |

`workspace / lake_home / toolchain / toolchain_root` are exposed so the
stub can rewrite head-side paths to wherever it materializes them on
the remote node.

### The stub return shape

The stub MUST return:

- **exit code**: 0 on successful `lean` run, non-zero on `lean` failure.
- **stdout**: `lean`'s stdout, byte-for-byte (Lake parses JSON-encoded
  diagnostics out of this stream).
- **stderr**: `lean`'s stderr, byte-for-byte (Lake surfaces this
  verbatim).

Whatever stub implementation produces those three things is
indistinguishable from local `lean` from Lake's perspective.

### What Lake guarantees in return

- **Manifest cleanup**. After the stub exits (any exit code), Lake
  attempts `IO.FS.removeFile manifestPath catch _ => pure ()`. The
  stub MUST NOT delete the manifest itself.
- **Local fallback**. If `$LAKE_REMOTE_EXEC` is unset OR the call site
  passes `lakeRoots = none`, the dispatcher falls through to plain
  `rawProc`. Lets call sites be hooked one at a time.
- **Input closure computed ahead of time**. `collectLeanInputClosure`
  walks Lake's dependency graph once per job; the stub doesn't need
  to do any graph walking on its own.
- **Setup file is an input, not an output**. Lake writes the per-module
  `setup.json` to disk before invoking the stub; it's listed in
  `inputs` but explicitly excluded from `outputs`. The stub must respect
  this — translating it per-worker if needed, but never shipping it
  back as a build artifact.
- **Stable manifest filename pattern**: `lake-remote-<pid>-<monoNano>-<safe-jobid>.json`
  in `$TMPDIR`. Unique across concurrent Lake processes.

## What's currently hooked

Today the hook is wired only at `compileLeanModule` (the per-module
`lean` invocation). The dispatcher (`Lake.RemoteExec.runRawProcOrStub`)
itself is generic and could be threaded through any other subprocess
call site — `compileO`, `compileSharedLib`, `compileExe`, etc. — by
computing inputs/outputs for that proc kind and passing
`lakeRoots := some ...`. Each is an additive change that doesn't
disturb call sites left as `lakeRoots := none`.

## What stays Lake's responsibility

- **Build scheduling**. Lake decides which jobs run when. The stub
  sees jobs one at a time, in whatever order Lake's scheduler dispatches
  them.
- **Cache hits, hash sidecars, incremental rebuilds**. Because the hook
  intercepts below Lake's job layer, all of Lake's normal caching
  semantics apply unchanged. A no-op rebuild dispatches zero stub
  calls; the first build dispatches one per missed lean job.
- **Diagnostic parsing**. Lake reads JSON-encoded diagnostics from the
  stub's stdout the same way it reads them from `lean`'s.
- **Manifest lifecycle** (see above).

## What's deliberately *not* part of this patch

- **No coordinator or worker logic in Lake.** The stub binary is opaque.
- **No orchestration of multiple stubs.** Lake invokes the stub once per
  lean job; whatever queueing / scheduling / load-balancing happens
  beyond that is the stub's concern.
- **No protocol assumptions.** The manifest is JSON-on-disk; the stub
  is an exec'd binary. The hook is silent about HTTP, gRPC, RDMA,
  shared memory, or any other transport.

## Example consumers

Anything that accepts `<stub> <manifest.json>` and returns
`exit + stdout + stderr` qualifies.

### Trivial passthrough

```sh
#!/usr/bin/env bash
# stub-passthrough: read manifest, exec exactly what Lake would have run.
set -e
m="$1"
cmd=$(jq -r '.cmd' "$m")
mapfile -t args < <(jq -r '.args[]' "$m")
mapfile -t env_kvs < <(jq -r '.env | to_entries[] | "\(.key)=\(.value)"' "$m")
cwd=$(jq -r '.cwd // ""' "$m")
[[ -n "$cwd" ]] && cd "$cwd"
exec env "${env_kvs[@]}" "$cmd" "${args[@]}"
```

Useful sanity check: builds with `LAKE_REMOTE_EXEC=./stub-passthrough`
should be byte-for-byte identical to plain `lake build`. Verifies that
the hook itself introduces no behavioural changes.

### Sandboxing — local execution under an isolation primitive

The manifest lists every file `lean` should be allowed to read
(`inputs`) and write (`outputs`). Combined with `cmd`/`args`/`env`/`cwd`,
that's exactly enough to construct a sandbox view. A landlock-style
sandbox stub looks like:

```sh
#!/usr/bin/env bash
# stub-sandbox: run lean under landlock, allowing only the manifest's
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

A sandbox stub like this lets `lake build` run in a per-job isolated
view of the filesystem without changing anything in Lake itself. The
hook is exactly the surface needed: Lake declares its dependencies,
the stub enforces them at OS level.

### Distributed orchestration

The reference distributed user of this hook is a Go orchestrator
(coordinator + worker pool + per-job stub) that ships inputs to workers
over gRPC + HTTP/2 cleartext, runs `lean` on the assigned worker, and
reflects outputs back to the head's filesystem. See the
`lake-distbuild` project for the implementation. The same `inputs` /
`outputs` lists that make sandboxing possible also drive what the
orchestrator transfers across nodes — same data, different consumer.

### Composing — sandbox + remote together

Stubs compose by chaining: the stub Lake invokes can do its own work
and then delegate to a downstream stub, since the downstream's
interface is the same `<binary> <manifest.json>` shape. Two natural
composition patterns:

**Sandbox-then-remote (head-side wrapping):** the head sandbox stub
wraps each remote dispatch, e.g. to enforce that the orchestrator can
only read declared inputs from the head's filesystem when materializing
a job:

```sh
#!/usr/bin/env bash
# stub-sandbox-then-remote: enforce sandbox on the head while the
# orchestrator does the actual dispatch downstream.
set -e
m="$1"
mapfile -t read_paths  < <(jq -r '.inputs[]'  "$m")
mapfile -t write_paths < <(jq -r '.outputs[]' "$m")
exec landlock-sandboxer \
    --ro $(printf -- "--ro %q " "${read_paths[@]}") \
    --rw $(printf -- "--rw %q " "${write_paths[@]}") \
    -- /path/to/stub-remote "$m"
```

**Sandbox at the worker (downstream wrapping):** the remote
orchestrator ships the manifest to a worker, and on the worker the
job is wrapped in a sandbox before invoking `lean`. The worker's own
job runner, written by the orchestrator's author, applies the same
`inputs`/`outputs`-based isolation as the standalone sandbox stub
above — it just runs after the work has been materialized on the
worker filesystem.

Either is a small, local change relative to a non-composed
configuration: the sandbox stub treats the orchestrator stub as the
"command to run after isolating", or the orchestrator's worker treats
the sandbox as the "wrapper to apply before `exec lean`". Neither
requires any further changes to Lake.

## Limitations / non-goals (today)

- Only `compileLeanModule` is hooked. C compilation (`compileO`),
  linking (`compileSharedLib`, `compileExe`), archive (`compileStaticLib`)
  are not hooked yet — they continue to run locally. (They could be
  hooked the same way; not in this patch.)
- The transitive olean closure used to populate `inputs` is a strict
  superset of `setup.importArts` (the exported-imports view). Lean's
  olean loader follows non-exported references at LEAN_PATH lookup
  time; in a local build Lake's build dir is fully populated so the
  difference is invisible, but for remote-exec we must ship the
  broader set. The walker is straightforward but not minimal — it
  ships everything `lean`'s loader might reach, not only what it
  actually opens during a specific compile.
