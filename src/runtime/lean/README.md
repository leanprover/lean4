# Reference-counting deletion in Lean

`Collector.lean` supplies the complete deletion control flow used by
`lean_dec_ref_cold`: counter decisions, queue insertion, field scanning, thunk
dispatch, typed field-layout selection, destructor ordering, and the LIFO
deletion loop. The normal Lean compiler specializes this algorithm to borrowed
machine addresses and emits `../object_gc.inc`. `../object.cpp` supplies typed
memory accesses and individual deallocation, destructor, and scheduler effects.
The public C ABI is unchanged.

Fields are released in increasing address order. An object that loses its last
reference is pushed onto the existing intrusive worklist. For a constructor
with one physical slot, the loop can continue directly into its child without
writing a queue link. Both paths dispose the source after releasing its fields
and before visiting its children; pending siblings keep their LIFO order.
Thunks read their atomic closure and cached value in that order. Task and promise
deactivation and external finalizers retain their native implementations.
This order, and hence the order of finalizers, is not a contract: every schedule
that ownership permits reaches the same result.

## Generation and bootstrapping

After building Lean, regenerate the checked-in fragment from the repository root:

```sh
PATH="$PWD/build/release/stage1/bin:$PATH" \
  build/release/stage1/bin/lean --run script/gen_gc.lean \
  src/runtime/lean/Collector.lean src/runtime/object_gc.inc
```

The generator checks every reachable impure compiler declaration before writing
the output. It allows machine integers, immediate scalar constructors, direct
calls to checked local functions, and an explicit list of native primitives.
It rejects allocated types, heap constructors, boxing, reference-counting
instructions, indirect calls, global initializers, and other foreign calls.
It checks the foreign symbols as well as the Lean declaration names.

The fragment uses the compiler's C emitter, with private linkage for generated
helpers. It contains no module initializer or boxed entry point. A build consumes
the checked-in fragment without needing to run Lean inside its own collector.
`make -C build/release update-stage0` copies that fragment with the native sources;
the collector's Lean source is excluded from the ordinary stdlib
snapshot. The regression test regenerates the fragment and requires an exact
match, so changes to the source or compiler cannot silently leave it stale.

The allocation check covers the generated collector's instructions and calls.
It does not prohibit an external finalizer or task scheduler operation from
allocating or recursively calling the collector.

## Proofs

`tests/misc_dir/rc_graph/Graph.lean` represents every root and every field
occurrence by a separate ownership token. Repeated pointers therefore account
for separate references. Its validity predicate relates the encoded counter
to the number of remaining tokens through `tests/elab/rc_model.lean`.
Persistent and sticky counts may keep an object after its ideal count reaches
zero; its outgoing references remain owned.

The model distinguishes losing the last reference from reclaiming storage.
An absent counter marks exclusive deletion responsibility; the object is
reclaimed only after its fields have been scanned. This is a logical state,
not a claim that the native intrusive header contains a literal zero.

The total `drain` function decreases the sum of owned tokens and queued objects.
`Schedule.lean` permits any interleaving of releasing an owned field of an object
that has lost its last reference and reclaiming a queued object whose fields are
released. `schedule_independent` proves that every such schedule, run until no
step applies, ends with the same ownership and counters and reclaims the same
objects; `drain` is one such schedule. `Released` states what releasing a root
does, whatever the schedule:

* counters match the remaining references, and every live object keeps its fields;
* exactly the objects that lost their last reference are reclaimed, each once;
* exactly the released root and the fields of reclaimed objects are released;
* objects reachable from another remaining root stay live with their payloads;
* nothing remains queued, so releases compose (`Released.quiescent`).

`Refinement.lean` interprets the same `Adapter`-parameterized implementation that
the native wrapper calls. It proves the counter decision for every `Int32`,
queue insertion, direct single-child continuation, ordered thunk reads, ordinary
field scanning, and the complete root release equal to the finite ownership collector.
`collect_released` transfers `Released` and schedule independence to the shared
collector.
The interpreter records
each link write and reads the saved tail when constructing a queued list, so
omitting the write or returning the old head breaks `release_refines`.
`entry_refines` establishes termination and exact agreement with `drain` under
the finite heap interpretation, including the shared `partial_fixpoint` loop.

The layout contract counts physical slots, including null and immediate values,
and requires that count to fit in `USize`. Removing ignored slots must leave
exactly the graph's owned field occurrences in order; repeated references retain
distinct occurrence tokens. Thunk slots enumerate those tokens in closure/value
order. `native_entry_uses_shared` checks the exported wrapper and its complete
primitive binding against the shared entry point; bypassing that entry or
swapping a thunk primitive breaks the equality.

`Dispatch.lean` checks classification of all 256 byte tags against an independent
tag table, then proves the selected field operations and destructor order for
arbitrary primitives. `native_dispatch_uses_shared` checks the native bindings.
Native static assertions bind the Lean tag table to the C constants.

`Concurrent.lean` separates shared-counter guards from atomic updates. Pending
copies may share a protected source owner token, including a borrowed field;
releases preserve a source owner until those copies finish. Initial sharing uses
the pre-sharing `Int32` encoding and `markMtRc_spec`, preserving prior overflow
freezing even with few remaining owners. The history invariant proves exclusive
ownership with no pending copies at the last-reference event and bounds delayed
adjustments so the counter cannot wrap into the unshared range. Sticky safety
assumes at most 4,094 pending increments, each at most `LEAN_RC_INC_MAX`, and fewer
pending releases than the sticky band's width. These are assumptions rather than
enforced limits.

`ConcurrentRefinement.lean` interprets the production release with separate
values for its first read, fresh sticky check, and atomic old count.
`history_last_exclusive` relates its deletion decision to permitted histories.
Native guard observations must admit a history ordering that reserves every
delayed enabled adjustment in pending credits, including each huge shared
increment chunk. Publication, borrow lifetimes, and the existing C++ mixed access
contracts remain conditional trusted obligations; see [`CONTRACTS.md`](CONTRACTS.md).

The graph proofs assume a valid heap whose edges and payloads are immutable during
the deletion cascade. C pointer layout, intrusive-link encoding and memory
accesses, native destructors, foreign primitive contracts, compiler correctness,
concurrent mutation, scheduling, and arbitrary finalizer behavior remain outside
the graph proof.

[`CONTRACTS.md`](CONTRACTS.md) states the native primitive preconditions, effects,
and remaining trust obligations. `NativeContracts.lean` checks a byte-addressed
model of the saved links and frame conditions, including the little-endian and
pointer-width assumptions. Those theorems do not verify the C++ implementation;
`native_contracts.c` separately exercises the actual runtime boundary.

The scalar lemmas and counter refinement use `bv_decide`, whose native proof
checker evaluation introduces the usual compiler-trust dependencies. The graph
proofs inherit those dependencies through `rc_model`; they do not add axioms
asserting collector correctness.

## Validation

Run the collector validation gate and sticky-counter regression:

```sh
tests/with_stage1_test_env.sh tests/misc_dir/rc_graph/run_test.sh
tests/with_stage1_test_env.sh tests/misc_dir/rc_sticky/run_test.sh
```

The gate checks proofs and executable examples, exact regeneration, and rejection
of allocating or unapproved code without replacing the output. `candidate.c`
executes the freshly generated fragment over checked primitives before the runtime
switch. Both graph harnesses compare 4,096 seeded cases with their shared
independent counted-edge model; the candidate also exercises all 256 tags and 24
deterministic interleavings across root release, scanning, and unary continuation.

[`refinement_audit.py`](../../../tests/misc_dir/rc_graph/refinement_audit.py) contains
the executable mutation case table. Each well-typed mutant must fail its named
theorem, pass the allocation audit, and trigger a seeded candidate assertion.

The native graph harness checks exact finalizer traces and surviving counts after
every root release, with ST/serial-MT unary continuation, pending siblings,
reentrant finalizers, and a 100,000-object chain. It can also run against the
incumbent runtime for comparison. See the [native contract evidence](CONTRACTS.md#executable-evidence-and-limits)
for boundary fixtures and their memory, foreign-effect, and concurrency limits.
`concurrent.c` runs 128 cases with eight workers across shared roots, scanner
fields, unary children, and borrowed array-field retains, checking retained
payloads and exactly-once finalization. It runs unchanged against the incumbent
and migrated runtimes.

`tests/misc_dir/rc_graph/bench.c` times deletion separately from allocation for
constructor chains and arrays of leaves, immediate scalars, and shared objects.
Build a binary against each runtime and compare repeated, alternating runs on
the same idle CPU:

```sh
build/release/stage1/bin/leanc -O3 -DNDEBUG -o /tmp/rc-gc-bench \
  tests/misc_dir/rc_graph/bench.c
/tmp/rc-gc-bench
```

Run the complete test suite after building the replacement:

```sh
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
  make -C build/release -j "$(nproc)" test
```
