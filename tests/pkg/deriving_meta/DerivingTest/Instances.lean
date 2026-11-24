module
public import DerivingTest.Handlers

/-!
Handwritten "base case" instances for the type classes defined in `DerivingTest.Handlers`
-/

public section

instance : ToData Nat where
  convert := .nat

instance : ToData Int where
  convert := .int

instance : ToData String where
  convert := .string

instance : ToData UInt8 where
  convert x := .nat x.toNat

instance : ToData UInt16 where
  convert x := .nat x.toNat

instance : ToData UInt32 where
  convert x := .nat x.toNat

instance : ToData UInt64 where
  convert x := .nat x.toNat

instance : ToData USize where
  convert x := .nat x.toNat

instance : ToData (Fin n) where
  convert x := .nat x.val

instance [ToData α] : ToData (Array α) where
  convert x := .array <| x.map ToData.convert

@[instance_reducible, expose, inline]
def FirstDiff.atomic [DecidableEq α] : FirstDiff α where
  firstDiff a b := if a = b then none else some .differentValue

attribute [local instance] FirstDiff.atomic in
instance [DecidableEq α] : LawfulFirstDiff α where
  of_firstDiff_eq_none a b := by
    intro h
    replace h := ite_eq_left_iff.mp h
    by_cases heq : a = b
    · exact heq
    · specialize h heq
      contradiction

instance : FirstDiff Nat := FirstDiff.atomic
instance : FirstDiff Int := FirstDiff.atomic
instance : FirstDiff String := FirstDiff.atomic
instance : FirstDiff UInt8 := FirstDiff.atomic
instance : FirstDiff UInt16 := FirstDiff.atomic
instance : FirstDiff UInt32 := FirstDiff.atomic
instance : FirstDiff UInt64 := FirstDiff.atomic
instance : FirstDiff USize := FirstDiff.atomic
instance : FirstDiff (Fin n) := FirstDiff.atomic

protected def Array.firstDiff [FirstDiff α] (a b : Array α) : Option DiffPath :=
  if h : a.size = b.size then
    go 0 h
  else
    some (.field `size .differentValue)
where
  go (i : Nat) (h : a.size = b.size) : Option DiffPath :=
    if _ : i < a.size then
      match firstDiff a[i] b[i] with
      | none => go (i + 1) h
      | some diff => some (.atIdx i diff)
    else
      none

instance [FirstDiff α] : FirstDiff (Array α) where
  firstDiff := Array.firstDiff

deriving instance GenRandom for Nat, Int

instance : GenRandom (Fin n) where
  random := do
    if h : n = 0 then
      throw (.userError "Failed to generate random number in `Fin 0`")
    else
      have : NeZero n := ⟨h⟩
      return Fin.ofNat n (← IO.rand 0 (n - 1))

deriving instance GenRandom for BitVec, UInt8, UInt16, UInt32, UInt64, USize

instance [GenRandom α] : GenRandom (Array α) where
  random := do
    let len ← GenRandom.random Nat
    Array.ofFnM fun _ : Fin len => GenRandom.random α

instance : GenRandom Char where
  random := return Char.ofOrdinal (← GenRandom.random _)

instance : GenRandom String where
  random := return String.ofList (← GenRandom.random (Array Char)).toList

deriving instance GenRandom for ByteArray
