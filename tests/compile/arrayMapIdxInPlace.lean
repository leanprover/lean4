/-
`Array.mapFinIdx` and `Array.mapIdx` should map in place, exactly like
`Array.map`: when the input array is uniquely owned, each element slot is handed
to the mapping function exclusively (refcount 1), so the function may mutate it
without copying.

We observe this with `dbgTraceIfShared msg x`, which prints `msg` to stderr
exactly when `x` has refcount > 1 at that point. The mapping function here does
an in-place `Array.modify` on each row. If the row is borrowed from the input
array (the old, push-based reference behaviour) it is shared, the modify copies
the whole row, and a trace is printed. With the in-place implementation no trace
is printed, matching `Array.map`.

This is a regression test for the `@[implemented_by]` on `Array.mapFinIdxM`:
before that change, the `mapFinIdx`/`mapIdx` lines below each printed one
`row shared` trace per row.
-/
set_option compiler.extract_closed false

@[noinline] def build (r c : Nat) : Array (Array Nat) :=
  (Array.range r).map (fun _ => Array.range c)

@[noinline] def sumHeads (m : Array (Array Nat)) : Nat :=
  m.foldl (fun s row => s + row[0]!) 0

@[noinline] def viaMap (n : Nat) : Nat :=
  sumHeads <| (build n n).map (fun row =>
    (dbgTraceIfShared "map: row shared" row).modify 0 (· + 1))

@[noinline] def viaMapFinIdx (n : Nat) : Nat :=
  sumHeads <| (build n n).mapFinIdx (fun _ row _ =>
    (dbgTraceIfShared "mapFinIdx: row shared" row).modify 0 (· + 1))

@[noinline] def viaMapIdx (n : Nat) : Nat :=
  sumHeads <| (build n n).mapIdx (fun _ row =>
    (dbgTraceIfShared "mapIdx: row shared" row).modify 0 (· + 1))

def main : IO UInt32 := do
  IO.println s!"map       {viaMap 3}"
  IO.println s!"mapFinIdx {viaMapFinIdx 3}"
  IO.println s!"mapIdx    {viaMapIdx 3}"
  return 0
