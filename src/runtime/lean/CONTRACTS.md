# Native collector contracts

`tests/misc_dir/rc_graph/NativeContracts.lean` proves the finite-word and byte-memory facts below
for the runtime's intrusive deletion worklist. `object.cpp` supplies the memory operations and
terminal effects modeled here.
These are conditional representation proofs, not a verification of C++, its compiler, the
allocator or the scheduler.

## Representation and platform

The byte-memory interpretation used by the proofs requires:

* Eight-bit bytes, 32-bit `int`, four- or eight-byte pointers, and
  `sizeof(size_t) == sizeof(void *)`.
* Little-endian integer representation and an eight-byte `lean_object` header with `m_rc` in
  bytes 0–3, `m_cs_sz` in bytes 4–5, `m_other` in byte 6 and `m_tag` in byte 7. C bitfield layout
  is an ABI obligation; field declarations and pointer width alone do not establish it.
* Allocated object addresses are nonzero and aligned to the pointer size: four bytes on
  32-bit targets, eight on 64-bit targets. Distinct allocations have disjoint storage,
  including their eight-byte headers. Without mimalloc, the four-byte allocation-size prefix
  on 32-bit targets need not preserve eight-byte alignment. Integer/pointer conversions
  preserve the address and the provenance needed for subsequent accesses. Header accesses
  satisfy the compiler's aliasing and object-lifetime rules.
* On 64-bit targets, every pointer stored in the queue has its upper 16 bits **zero**. A
  sign-extended canonical address is insufficient. Disabling HWASAN and MTE does not itself
  establish this address bound for every allocator or operating system.

The 64-bit `set_next` reads two bytes at offset 6 with `memcpy` into a native `uint16_t`, shifts
that number left by 48, ORs in the **unmasked** next pointer, and writes eight bytes. The
little-endian precondition is essential to putting the saved metadata back at offsets 6 and 7.
`get_next` reads the header and clears bytes 6 and 7 of its local word.

`savedHi16_pack64` and `clear_bytes_unpack64` connect those byte offsets to finite-word
packing and unpacking. `unpack_pack64`, `pack64_preserves_metadata` and
`setNext64_header_bytes` prove exact link recovery and preservation of `m_other`/`m_tag` under
the address bound. Checked counterexamples show that dropping the bound can both truncate the
link and overwrite a tag.

On 32-bit targets, the next pointer replaces only the first four bytes. `unpack_pack32`,
`pack32_preserves_metadata` and `load_store32` prove recovery and preservation of bytes 4–7
in the stated byte interpretation. Neither branch preserves the old reference count; the
64-bit branch also overwrites the old `m_cs_sz`.

`pointer_tag32/64` prove that aligned object addresses are not immediates.
`immediate32/64` and `unbox_box32/64` prove the low-bit convention and round-trip boxing when
the input fits in `word_bits - 1` bits. Null is a separate sentinel: `lean_is_scalar(NULL)`
is false. Thunk and reference dispatch ignore null before any header access. Constructor,
closure and array slots must be nonnull; all field scanners ignore immediates.
`lean_dec(NULL)` is not a valid public call.

## Ownership, liveness and frames

A decrement consumes one owned reference. Every heap-valued physical field occurrence owns
one reference, including repeated occurrences of the same target. Counts must agree with those
references and external roots, subject to the documented persistent and sticky-count behavior.
An uncounted C pointer is a borrow, not permission to resurrect a dead object.

Losing the last reference transfers exclusive deletion responsibility. It does not mean the
storage has already been freed, and it need not store a literal zero in `m_rc`.

* Only objects with that exclusive deletion responsibility may have their headers repurposed
  for queue links. They must not already be queued. No other thread or callback may increment,
  decrement, mutate or resurrect them.
* A source object remains allocated, with readable layout metadata and fields, until **all**
  of its physical slots have been scanned. Unscanned fields retain their ownership tokens.
  Enqueuing a child must not reclaim its source or invalidate the source's cursor.
* Before disposing a queued head, the driver reads its saved successor. After disposal it
  uses that saved address, without reading the disposed head again.
* A header write changes only the four- or eight-byte header prefix. It preserves all payload
  bytes and all bytes outside that prefix. Counter writes affect only the target counter.
  This is a frame for the intrinsic memory operations; it is not whole-heap immutability
  across an external callback or scheduler operation.

`store_frame`, `setNext32_payload` and `setNext64_payload` prove the byte-store frame.
`Represents` describes a finite null-terminated list by following stored links, rather than
assuming a list-valued saved tail. `push32/64` derive the new representation from the actual
modeled header store. `push64` uses freshness and eight-byte alignment to establish disjoint
headers through `aligned_headers_disjoint`. `push32` takes disjoint eight-byte header extents
as an explicit allocation premise; four-byte alignment alone would not establish it.
Both use `store_other_header` for the suffix frame. A regression instantiates `push32` with
header addresses four modulo eight. `represents_pop` recovers the represented suffix. These
theorems do not prove allocation or ownership: their native use additionally requires the
live-storage and exclusive-deletion conditions above.
Every newly pushed address must also satisfy the platform bound so it can become a saved link
on a later push.

## Memory primitive preconditions and postconditions

All object arguments below are borrowed addresses. A Unit result is an immediate and creates
no reference to the borrowed object.

| Operation | Preconditions | Postcondition and intrinsic write footprint |
| --- | --- | --- |
| Read counter | Allocated object with a valid, unreclaimed RC header; not a queued header | Returns the 32-bit counter encoding; no writes |
| Write counter | Same storage condition, single-threaded ownership, and a valid new count selected by the counter algorithm | Stores precisely the selected count; only `m_rc` changes |
| Fetch-add counter | Valid shared RC storage, caller owns the token being released, and concurrent-count assumptions below | Atomic acquire-release addition of one; returns the **old** count, whose `-1` value identifies the last-reference transition |
| Write next link | Exclusively dead, allocated and fresh object; supported layout/address encoding; represented suffix disjoint from this header | Saves the suffix address, preserves tag/other and payload; RC storage is no longer an RC |
| Read next link | Allocated queued object whose link was initialized under the packing preconditions | Recovers exactly the saved address; no heap writes |
| Read tag | Allocated header, either ordinary or validly repurposed | Returns `m_tag`; no writes |
| Typed count/begin | Allocated source of the corresponding tag with initialized, valid size metadata | Returns the exact physical slot count or start of its contiguous slot region; no writes |
| Read field | Cursor denotes an initialized physical slot strictly before the region end | Returns that slot's null, immediate or owned heap reference as a borrow; no writes |
| Advance field | Cursor is within the source slot region and may advance to, but not beyond, one-past-end | Advances by `sizeof(lean_object *)`; preserves memory |
| Read thunk closure/value | Allocated thunk, last-reference ownership excludes a concurrent force, and atomic members have valid lifetimes | Default sequentially consistent atomic load of the corresponding member; no writes |

The physical regions are exactly:

* Constructor: `lean_ctor_num_objs` pointer slots beginning at `lean_ctor_obj_cptr`. Scalar
  data following those slots is not scanned.
* Closure: `lean_closure_num_fixed` slots beginning at `lean_closure_arg_cptr`. Arity is not
  the number of stored captures.
* Array: `lean_array_size` slots beginning at `lean_array_cptr`, with size at most capacity.
  Spare capacity is not an owned-reference region.
* Reference: the one `m_value` slot, even when its value is null or immediate.
* Thunk: separately read nullable closure and value members. The closure is released before
  the value is considered; normal pending and evaluated states are different layouts of
  these two members, not a variable-length pointer array.

All allocation sizes, offsets and `count * sizeof(void *)` must fit the address space.
`cursor32/64` prove finite-word cursor arithmetic does not wrap for a bounded region,
including the one-past cursor. Allocation extent, pointer provenance, valid initializations
and the strict read bound remain additional obligations. A numeric bound alone does not
make a dereference valid.

## Destruction, finalizers and scheduler effects

Terminal effects require exclusive deletion responsibility, allocated storage and valid tag
metadata. Their postconditions differ:

| Effect | Required behavior |
| --- | --- |
| Free small object | Release that allocation after scanning; do not consult overwritten `m_cs_sz` for its size. The mimalloc path uses `mi_free`; the other path uses its allocation prefix. |
| Free closure/array/scalar array/string | Release storage with its valid allocation size. Closure sizing uses fixed captures; array and string sizing use capacity; scalar-array element size masks out the linearity bit in `m_other`. |
| Destroy MPZ | Run the constructed MPZ destructor while the object and its resources are live; subsequently release the enclosing small allocation. |
| Finalize external | Invoke its registered finalizer once with live external storage and valid class/data; free the enclosing small allocation only after the callback returns. |
| Deactivate finished task | Release the owned result and reclaim the task, releasing the scheduler lock before recursively decrementing the result. |
| Deactivate unfinished task | Clear the closure and dependent-list heads and mark deleted/canceled under the scheduler lock. With the lock released, reclaim already-deleted dependent entries and release the detached closure. Queue/dependency links or a running worker govern storage reclamation; releasing the closure can reentrantly reclaim this task before deactivation returns. |
| Deactivate promise | Resolve its result task to `Option.none` if still unresolved, release the promise's result-task token, then reclaim the promise. An already resolved value stays resolved. |

Task storage reclamation is therefore distinct from last-reference detection and deactivation.
A theorem that records every terminal effect as an immediate physical free does not cover
unfinished tasks, nor does deactivation guarantee that task storage remains live on return.
For example, releasing a waiting task's closure can drop its dependency's last reference;
that dependency's deactivation can then reclaim the already-deleted task. Post-deactivation
reads require an independent lifetime argument. The deterministic native fixture retains the
unresolved promise that owns the dependency, keeping its dependent-list link live during
inspection. A running worker owns the executing closure after removing it from the task;
deactivation does not reclaim that closure from the worker. A keep-alive task carries an extra
owned scheduler reference, so dropping a user handle need not deactivate it. Unfinished tasks
and promises require an initialized task manager; without one, task disposal requires an
already available result.

Finalizers may allocate, release independent roots, reenter the collector and mutate objects
for which they have the required ownership or synchronization. Promise resolution can run
synchronous task callbacks; task capture release can run external finalizers. These effects
can reach shared retained graph state through independently owned references.

The callback contract requires correct ownership accounting, no access through invalid borrows,
no resurrection of objects whose headers are queued, and normal return if the caller's
termination/postcondition is to hold. The intrinsic frame law applies to bytes outside the
intrinsic operation's write footprint. A frame for a complete callback must additionally
exclude its authorized effects; it cannot assert that all retained payloads remain unchanged
when a callback is allowed to mutate them. Likewise, there is no general no-allocation or
termination guarantee for arbitrary finalizers.

The finite graph refinement uses a fixed graph and modeled terminal effects. Extending it to
arbitrary callbacks, asynchronous task states or allocator side effects requires a separate
effect refinement; the native regression tests below are evidence, not a replacement proof.

## Shared counter histories

`Concurrent.lean` separates guard observations from atomic updates. Pending copies may share
protected source tokens kept in `owners`; `references = owners + drops + skipped`. While copies
are pending, a release may reserve or skip an owner only if another remains. The last-reference
theorem leaves only the releasing token, with no pending copies or remaining owners. Live shared
counts stay negative and above the unshared sticky range, and `Int32` updates do not wrap.

Initial sharing requires an unshared pre-sharing `Int32` encoding that `tracks` the logical
owner count. `markMtRc_spec` preserves freezing of an already-overflowed single-threaded
count even with few remaining owners.

Sticky safety assumes at most 4,094 pending increments of at most `LEAN_RC_INC_MAX` each,
and fewer pending releases than the sticky band's width (`0x10000000`). These are the margins
used by the existing runtime, not enforced limits on the task pool or a theorem for
arbitrarily many operations in flight. The large-increment helper repeatedly applies the
same bounded chunks with a fresh guard.

Native guard observations must admit a history ordering that reserves every delayed enabled
adjustment in pending credits until its atomic update, including each chunk of a huge shared
increment. Publication, ownership transfer, and borrow lifetimes must keep the object and each
protected source live through the operation. A native memory and happens-before argument for
these conditional primitive contracts is still required.

The existing runtime reads `m_rc` as a plain `int` in ordinary builds and through a sequentially
consistent atomic load under TSan; shared RMWs use an atomic view of the same storage. A
standards-conforming C++ justification for the mixed accesses and that view's lifetime/aliasing
remains trusted. Alignment, hardware atomicity, and TSan's different accessor do not establish
that justification for ordinary builds.

Compiler correctness, the C/C++ ABI and pointer conversions, atomic publication/lifetimes,
allocator behavior, scheduler invariants, user finalizers, compilation of the foreign calls
and native linking remain trusted obligations.

## Executable evidence and limits

`NativeContracts.lean` checks both 32- and 64-bit encodings without importing the changing
runtime layout adapter. Its byte memory is a mathematical function; it does not execute C.

`native_contracts.c` executes `lean_dec` and public runtime APIs. It does not call, replace or
copy private queue helpers. An earlier sibling's finalizer observes already queued objects,
checks the actual saved links and metadata bytes, and checks that payloads survive queueing.
Later finalizer traces check traversal of the saved suffix.

The native cases cover null/immediate physical slots, repeated owning slots, size versus
capacity, arity versus fixed captures, linearity metadata, pending/evaluated thunks, retained
payloads with ST and MT counters acquired through real APIs, reentrant allocating finalizers,
finished-task result ownership, surviving promise result tasks, duplicate resolution,
deactivated waiting tasks and synchronous callbacks during promise disposal.

Promise cases require a threaded runtime. They use synchronous dependents of unresolved
promises to make lifetime observations deterministic, without worker races. A successful
native run covers its actual host ABI only; compiling the 32-bit theorems does not execute a
32-bit runtime. These boundary fixtures are not a leak detector, a proof of all destructor
implementations or a performance benchmark.

Existing `rc_sticky` fixtures cover single-threaded overflow; the Lean initializer regression
covers an overflowed encoding with one remaining owner.

`concurrent.c` exercises 128 cases with eight workers across shared roots,
scanner fields, unary children, and borrowed array-field retains. In the borrowed case, one
array field owns a child initially at RC −1; each worker holds an array reference while
retaining that child. It checks retained payloads and exactly-once finalization after all
owners release. Both collectors use the same fixture; passing it is executable evidence
rather than a C++ memory-model proof.
