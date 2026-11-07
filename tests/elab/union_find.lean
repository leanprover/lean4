module
import Lean.Data.UnionFind

/-!
This is a generic unit test for Lean.UnionFind
-/


def test : IO Unit := do
  let uf := Lean.UnionFind.emptyWithCapacity 32
  let (uf, eqcSpecial1) := uf.push
  let (uf, eqc0) := uf.push
  let (uf, eqc1) := uf.push
  let (uf, eqc2) := uf.push
  let (uf, eqc3) := uf.push
  let (uf, eqc4) := uf.push
  let (uf, eqc5) := uf.push
  let (uf, eqc6) := uf.push
  let (uf, eqc7) := uf.push
  let (uf, eqc8) := uf.push
  let (uf, eqc9) := uf.push
  let (uf, eqcSpecial2) := uf.push
  let uf := uf.union! eqc1 eqc3
  let uf := uf.union! eqc2 eqc4
  let uf := uf.union! eqc3 eqc5
  let uf := uf.union! eqc8 eqc6
  let uf := uf.union! eqc9 eqc7
  let uf := uf.union! eqc4 eqc6
  let uf := uf.union! eqc7 eqc5
  let uf := uf.union! eqc0 eqc6

  let arr := #[eqc0, eqc1, eqc2, eqc3, eqc4, eqc5, eqc6, eqc7, eqc8, eqc9]
  let mut uf := uf
  for i in 0...arr.size do
    for j in (i + 2)...arr.size do
      if i %2 == j %2 then
        assert! uf.root! arr[i]! == uf.root! arr[j]!
        let (uf', eq) := uf.checkEquiv! arr[i]! arr[j]!
        uf := uf'
        assert! eq
        assert! uf.root! arr[i]! == uf.root! arr[j]!
      else
        assert! uf.root! arr[i]! != uf.root! arr[j]!
        let (uf', eq) := uf.checkEquiv! arr[i]! arr[j]!
        uf := uf'
        assert! !eq
        assert! uf.root! arr[i]! != uf.root! arr[j]!

  let szEven := uf.iterClass eqc6 |>.toArray |>.size
  assert! szEven == 5
  let szOdd := uf.iterClass eqc7 |>.toArray |>.size
  assert! szOdd == 5
  let sz1 := uf.iterClass eqcSpecial1 |>.toArray |>.size
  assert! sz1 == 1
  let sz2 := uf.iterClass eqcSpecial2 |>.toArray |>.size
  assert! sz2 == 1

  IO.println "Everything okay!"

/-- info: Everything okay! -/
#guard_msgs in
#eval test
