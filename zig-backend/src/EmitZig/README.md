# EmitZig shadow-tree package

This directory is the M6 shadow-tree home for the future Lean-to-Zig code generator.
It intentionally lives inside `zig-backend/src/EmitZig/` instead of the outer
Lean repository's `src/` tree. The mission-level rule for M6 is that workers may
read from `/Users/davirian/dev/active/lean4/src/`, especially
`src/Lean/Compiler/LCNF/EmitC.lean`, `EmitUtil.lean`, and `NameMangling.lean`,
but they must not modify those files. By keeping the new backend in a separate
Lake package, the project can prototype code generation structure, CLI behavior,
and smoke-test wiring without breaking the bedrock invariant that the upstream
Lean tree stays untouched until the later promotion milestone.

The package is wired to the already-built stage1 toolchain through its local
`lean-toolchain` file, which pins to the custom elan toolchain name
`lean4-stage1-e09155b6f91642c2e50c3eb476823947200a90d0`. That local alias is
linked to `/Users/davirian/dev/active/lean4/build/release/stage1`, preserving a
direct connection to the exact stage1 build while still allowing plain
`lake build` invocations in this subdirectory. This lets the package import the
real compiler modules directly from the built toolchain rather than copying
source files. For this feature, the important proof point is that a minimal
executable can import `Lean.Compiler.LCNF.EmitC`,
`Lean.Compiler.LCNF.EmitUtil`, `Lean.Compiler.NameMangling`, and the rest of the
Lean toolchain surface exactly as it exists in the stage1 build.

The current stage1 binary reports:

- `Lean (version 4.31.0-pre, arm64-apple-darwin25.4.0, commit e09155b6f91642c2e50c3eb476823947200a90d0, Release)`
- `Lake version 5.0.0-src (Lean version 4.31.0, commit e09155b6f91642c2e50c3eb476823947200a90d0)`

That version-and-commit record is kept here so later M6 and M9 workers can tell
which exact toolchain this shadow package was validated against. If the outer
stage1 toolchain changes, this package should be revalidated rather than silently
assuming compatibility.

## Why a shadow tree now?

The shadow-tree approach gives the mission a low-risk path for building EmitZig
in parallel with runtime work:

1. **No source vendoring.** The package imports upstream compiler modules from the
   toolchain instead of copying Lean compiler code into `zig-backend/`.
2. **No outer-repo edits.** The main Lean repository remains clean outside of the
   already-authorized `.gitignore` change from earlier milestones.
3. **Fast iteration.** Workers can run `lake build`, later `lake test`, and then
   dedicated smoke binaries without rebuilding or promoting the whole compiler.
4. **Clear promotion boundary.** Any code written here is explicitly experimental
   until M9 moves it into the first-class compiler tree.

## M9 promotion plan

M9 is where this package stops being a shadow-tree experiment and becomes part of
the real Lean compiler. The expected promotion steps are:

1. Move the implementation from `zig-backend/src/EmitZig/` into the outer repo as
   `src/Lean/Compiler/LCNF/EmitZig.lean` (or split companion modules nearby if the
   file grows too large).
2. Replace shadow-only entrypoints with stage1-integrated build plumbing so the
   regular Lean toolchain can invoke EmitZig alongside or instead of EmitC.
3. Keep using shared upstream helpers like `EmitUtil` and `NameMangling`, but now
   from their native home in `src/Lean/Compiler/...`.
4. Add the promotion-specific bootstrap work that M6 is explicitly avoiding:
   stage0 regeneration, outer build-system integration, and audited changes to the
   compiler pipeline.
5. Remove or retire the shadow package once the promoted implementation is the
   canonical source of truth.

Until that promotion happens, this directory is the safe staging ground for the
EmitZig CLI, unit tests, smoke harnesses, and differential validation work that
subsequent M6 features will add.
