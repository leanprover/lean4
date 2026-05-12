/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.System.IO
public import Lean.Data.Name

namespace Lean

/--
A compacted region holds multiple Lean objects in a contiguous memory region, which can be
read/written to/from disk. Objects inside the region do not have reference counters and cannot be
freed individually. The contents of `.olean` files are compacted regions.
-/
@[expose] public def CompactedRegion := USize

@[extern "lean_compacted_region_is_memory_mapped"]
public opaque CompactedRegion.isMemoryMapped : CompactedRegion → Bool

/-- Size in bytes. -/
@[extern "lean_compacted_region_size"]
public opaque CompactedRegion.size : CompactedRegion → USize

/--
Frees a compacted region and its contents. No live references to the contents may exist at the
time of invocation.
-/
@[extern "lean_compacted_region_free"]
public unsafe opaque CompactedRegion.free : CompactedRegion → IO Unit

opaque CompactorSpec : NonemptyType.{0}
/--
Holds an opaque compactor handle returned by `CompactedRegion.save`, used to chain subsequent saves
so that objects shared between parts are emitted exactly once.

Not thread-safe: a `Compactor` value must not be used concurrently from multiple threads. The
`CompactedRegion`s passed as `depRegions` when the `Compactor` was first created must outlive the
`Compactor`; if any are freed (via `CompactedRegion.free`) while the `Compactor` is still in use,
subsequent saves will dereference dangling pointers.
-/
public def Compactor := CompactorSpec.type

/--
Saves arbitrary data to a compacted region on disk.

The `α` type parameter is erased at the runtime/extern boundary: the compactor walks the live
object graph rooted at `data` regardless of its Lean type. `α` is purely a hint for the caller to
align save and load sites. Mismatched types between save and load yield undefined behavior on use.

`key` is hashed to derive a deterministic mmap base address; for module saves, pass the module
`Name`. `depRegions` are loaded compacted regions (typically from imports) whose objects should
not be re-serialized. `prev`, when present, likewise allows for reuse of objects from prior saves
in the same session.

If `allowClosures` is `true`, closures in the compacted data are tolerated and the file is written
in the extended `v3` olean format (which may become the default in the future). This is an
EXPERIMENTAL option. The saving and loading process must be using identical executables, including
dependent libraries. When `false`, encountering a closure is an error and the file is written in the
old `v2` format.

Returns a `Compactor` that may be passed as `prev` to subsequent saves. Unsafe because the
returned `Compactor` carries thread-safety and `depRegions` lifetime contracts the type system
cannot enforce; see `Compactor`.
-/
@[extern "lean_compacted_region_save"]
public unsafe opaque CompactedRegion.save {α : Type} (fname : @& System.FilePath) (key : @& Name)
    (data : @& α) (depRegions : @& Array CompactedRegion) (prev : Option Compactor)
    (allowClosures := false) : IO Compactor

/--
Reads a compacted region from disk.

`depRegions` are existing compacted regions whose address ranges are needed for cross-region
pointer fixup. The result is the root object reinterpreted at type `α` paired with the new
`CompactedRegion`. Unsafe because `α` is type-erased at the extern boundary: it is the caller's
responsibility to ensure `α` matches the type the data was saved at; mismatched types yield
undefined behavior on use.
-/
@[extern "lean_compacted_region_read"]
public unsafe opaque CompactedRegion.read {α : Type} (fname : @& System.FilePath)
    (depRegions : @& Array CompactedRegion) : IO (α × CompactedRegion)

end Lean
