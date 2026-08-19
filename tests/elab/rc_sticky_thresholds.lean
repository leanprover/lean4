import Std.Tactic.BVDecide

/-!
# Reference-count sticky thresholds

When a reference count over- or underflows it lands in a deeply negative "sticky" range and stays
there: never freed, never adjusted again. This file models what the C functions that implement that
decide, and proves the safety properties they exist to provide.

## What is modelled, and what is not

`incRefN` and `decRef` are pure functions of the count, mirroring the branch structure of their C
counterparts. They constrain what each function *decides*.

An increment only ever leaves a count behind, so `incRefN` yields an `Int32`. A drop can also free
the object, so `decRef` yields `Option Int32`: the count left behind, or `none` if it was freed.
One value rather than a count plus a "was it freed" flag, so the two outcomes cannot disagree.

They say nothing about concurrency: the thread-shared paths really run `atomic_fetch_sub` and
`atomic_fetch_add`, and no interleaving of those is modelled here.
-/

/-- `#define LEAN_RC_STICKY      (INT_MIN + 0x10000000)` -/
abbrev LEAN_RC_STICKY : Int32 := Int32.minValue + 0x10000000

/-- `#define LEAN_RC_STICKY_DROP (INT_MIN + 0x20000000)` -/
abbrev LEAN_RC_STICKY_DROP : Int32 := Int32.minValue + 0x20000000

/-- `#define LEAN_RC_INC_MAX ((size_t)(LEAN_RC_STICKY - INT_MIN) + 1)` -/
abbrev LEAN_RC_INC_MAX : USize := (LEAN_RC_STICKY - Int32.minValue).toUInt32.toUSize + 1

/-- `lean_is_st`. -/
abbrev isSt (rc : Int32) : Bool := rc > 0

/-- `lean_is_mt`. Note this holds of stuck counts too; they are also negative. -/
abbrev isMt (rc : Int32) : Bool := rc < 0

/-- `lean_is_persistent`. -/
abbrev isPersistent (rc : Int32) : Bool := rc == 0

/-- Stuck in the sticky range: never adjusted or freed again. -/
abbrev isStuck (rc : Int32) : Bool := rc ≤ LEAN_RC_STICKY

/-- A thread-shared count that is not stuck, so one that still tracks references. -/
abbrev isUnstuckMt (rc : Int32) : Bool := isMt rc && !isStuck rc

/--
The references a count stands for: `rc` when single-threaded, `-rc` when thread-shared, since a
thread-shared count is stored negated. Widened, because `-Int32.minValue` does not fit in `Int32`.
-/
abbrev refCount (rc : Int32) : Int64 := if isSt rc then rc.toInt64 else -rc.toInt64

/--
The count `lean_inc_ref_huge_n` leaves behind, mirroring its branch structure:
```c
    if (lean_is_st(o)) {
        int rc = lean_internal_get_rc(o);
        if (n > (size_t)(INT_MAX - rc)) lean_internal_set_rc(o, LEAN_RC_STICKY);
        else                            lean_internal_set_rc(o, rc + (int)n);
    } else if ((unsigned)lean_internal_get_rc(o) > (unsigned)LEAN_RC_STICKY) {
        std::atomic_store_explicit(lean_get_rc_mt_addr(o), LEAN_RC_STICKY,
                                   std::memory_order_relaxed);
    }
```
-/
abbrev incRefHugeN (rc : Int32) (n : USize) : Int32 :=
  if isSt rc then
    if n > (Int32.maxValue - rc).toUInt32.toUSize then LEAN_RC_STICKY
    else rc + n.toUInt32.toInt32
  else if rc.toUInt32 > LEAN_RC_STICKY.toUInt32 then LEAN_RC_STICKY
  else rc

/--
The count `lean_inc_ref_n(o, n)` leaves behind, mirroring its branch structure:
```c
    if (LEAN_UNLIKELY(n > LEAN_RC_INC_MAX)) { lean_inc_ref_huge_n(o, n); return; }
    if (LEAN_LIKELY(lean_is_st(o))) {
        lean_internal_add_rc(o, n);
    } else if ((unsigned)lean_internal_get_rc(o) > (unsigned)LEAN_RC_STICKY) {
        std::atomic_fetch_sub_explicit(lean_get_rc_mt_addr(o), n, std::memory_order_relaxed);
    }
```
-/
abbrev incRefN (rc : Int32) (n : USize) : Int32 :=
  if n > LEAN_RC_INC_MAX then incRefHugeN rc n
  else if isSt rc then rc + n.toUInt32.toInt32
  else if rc.toUInt32 > LEAN_RC_STICKY.toUInt32 then rc - n.toUInt32.toInt32
  else rc

/--
A single-threaded count stays single-threaded or gets stuck, never overflowing into MT; persistent
and stuck counts are untouched; and an unstuck thread-shared count stays unstuck or gets stuck,
never wrapping into the single-threaded range.
-/
theorem incRefN_spec (rc : Int32) (n : USize) :
    let rc' := incRefN rc n
    let ni := n.toUInt64.toInt64
    if isSt rc then
      (isSt rc' && refCount rc' == refCount rc + ni) || isStuck rc'
    else if isPersistent rc || isStuck rc then
      rc' == rc
    else
      isUnstuckMt rc && ((isUnstuckMt rc' && refCount rc' == refCount rc + ni) || isStuck rc') := by
  intros
  cases System.Platform.numBits_eq <;> split <;> bv_decide

/-- Drops have stopped: at or below the drop threshold. Implied by `isStuck`, but wider. -/
abbrev isDropStopped (rc : Int32) : Bool := rc ≤ LEAN_RC_STICKY_DROP

/--
`lean_dec_ref_cold`, as the count it leaves behind or `none` if the object was freed:
```c
    if (lean_internal_get_rc(o) != 1) {
        if (LEAN_UNLIKELY(lean_internal_get_rc(o) <= LEAN_RC_STICKY_DROP)) return;
        if (std::atomic_fetch_add_explicit(lean_get_rc_mt_addr(o), 1,
                                          std::memory_order_acq_rel) != -1) return;
    }
    <free>
```
Note: `atomic_fetch_add` returns the count *before* the adjustment, so `!= -1` means this was not
the last reference; that is why the thread-shared arm frees exactly on `rc == -1`.
-/
abbrev decRefCold (rc : Int32) : Option Int32 :=
  if rc == 1 then none
  else if isDropStopped rc then some rc
  else if rc == -1 then none
  else some (rc + 1)

/--
`lean_dec_ref`, the inline entry point, which handles the common cases itself and delegates the
rest:
```c
    if (LEAN_LIKELY(lean_internal_get_rc(o) > 1)) {
        lean_internal_sub_rc(o, 1);
    } else if (lean_internal_get_rc(o) != 0) {
        lean_dec_ref_cold(o);
    }
```
`none` is "the object was freed"; `some rc'` is the count it left behind.
-/
abbrev decRef (rc : Int32) : Option Int32 :=
  if rc > 1 then some (rc - 1)
  else if rc != 0 then decRefCold rc
  else some rc

/-- What `lean_dec_ref` does to every count, split by class. -/
theorem decRef_spec (rc : Int32) :
    let rc' := decRef rc
    if rc > 1 then
      rc' == some (rc - 1)
    else if rc == 1 || rc == -1 then
      rc' == none
    else if rc == 0 || isDropStopped rc then
      rc' == some rc
    else
      rc' == some (rc + 1) := by
  grind

/--
Drops stop at a strictly less negative threshold than increments. Since a thread-shared increment
is a `fetch_sub`, a count inside the band can only descend, so it converges into the sticky range
rather than climbing back out. That convergence argument is about interleavings and so is outside
this model; this records only the ordering it rests on.
-/
theorem drop_threshold_above_inc_threshold : LEAN_RC_STICKY < LEAN_RC_STICKY_DROP := by
  decide
