/-!
Regression test for `ByteArray.copySlice` with heap-allocated (bignum) `Nat` arguments.

The runtime `lean_byte_array_copy_slice` takes `srcOff`/`destOff`/`len` as borrowed `Nat`s and
reads them with a saturating conversion. This checks that out-of-range bignum offsets and lengths
agree with the reference semantics on every path (early return, append-at-end, length clamping)
rather than aborting, and covers the leak once fixed by decrementing owned arguments there.
-/

/-- The pure meaning of `copySlice`, matching the body of `ByteArray.copySlice`. -/
def refCopySlice (src : ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) : ByteArray :=
  ⟨dest.data.extract 0 destOff ++ src.data.extract srcOff (srcOff + len) ++
    dest.data.extract (destOff + min len (src.data.size - srcOff)) dest.data.size⟩

def check (name : String) (src : ByteArray) (srcOff : Nat) (dest : ByteArray)
    (destOff len : Nat) : IO Unit := do
  let got := (src.copySlice srcOff dest destOff len).data
  let expected := (refCopySlice src srcOff dest destOff len).data
  if got == expected then IO.println s!"ok: {name}"
  else IO.println s!"FAIL {name}: got {got} expected {expected}"

def main (args : List String) : IO Unit := do
  -- Build the bignum offset from the argument count so it is a genuine heap `Nat`,
  -- not a compile-time persistent constant. Defaults to `2^64` with no arguments.
  let huge := 2 ^ 64 + args.length
  let src := ByteArray.mk #[10, 11, 12, 13]
  let dest := ByteArray.mk #[1, 2, 3]
  check "normal" src 1 dest 1 2
  check "append" src 0 dest 3 4
  check "srcOff-past-end" src 9 dest 0 2
  check "srcOff-bignum" src huge dest 0 2
  check "destOff-bignum" src 0 dest huge 2
  check "len-bignum" src 1 dest 1 huge
  check "all-bignum" src huge dest huge huge
