def Nat.Up (ub a i : Nat) := i < a ∧ i < ub

theorem Nat.Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.lt_succ_self _, h⟩

/-- A terminal byte slice, a suffix of a byte array. -/
structure ByteSliceT := (arr : ByteArray) (off : Nat)

namespace ByteSliceT

/-- The number of elements in the byte slice. -/
@[inline] def size (self : ByteSliceT) : Nat := self.arr.size - self.off

/-- Index into a byte slice. The `getOp` function allows the use of the `buf[i]` notation. -/
@[inline] def getOp (self : ByteSliceT) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)

end ByteSliceT

/-- Convert a byte array into a terminal slice. -/
def ByteArray.toSliceT (arr : ByteArray) : ByteSliceT := ⟨arr, 0⟩

/-- A byte slice, given by a backing byte array, and an offset and length. -/
structure ByteSlice := (arr : ByteArray) (off len : Nat)

namespace ByteSlice

/-- Convert a byte slice into an array, by copying the data if necessary. -/
def toArray : ByteSlice → ByteArray
| ⟨arr, off, len⟩ => arr.extract off len

/-- Index into a byte slice. The `getOp` function allows the use of the `buf[i]` notation. -/
@[inline] def getOp (self : ByteSlice) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)


/-- The inner loop of the `forIn` implementation for byte slices. -/
def forIn.loop [Monad m] (f : UInt8 → β → m (ForInStep β))
  (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β :=
  if h : i < _end then do
    match ← f (arr.get! i) b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => have := Nat.Up.next h; loop f arr off _end (i+1) b
  else pure b
termination_by _end - i

attribute [simp] ByteSlice.forIn.loop
#check @ByteSlice.forIn.loop._eq_1
