import Init.System.IO
import Init.Data.BitVec


open BitVec

      set_option diagnostics true


def test : IO Unit := do
  let w := 5
  for xx in [0 : 2^w] do
    let x := BitVec.ofNat w xx
    let bbpop : BitVec w := x.popCountParSum
    let bvpop : BitVec w := x.popCount
    -- IO.print f!"\nNaive popCount returned {pop}, bitblaster circuit returned{bbpop}, bvPop returned {bvpop}"
    if bbpop.toNat ≠ bvpop.toNat then IO.print f!"\nFAIL"

    IO.println ""

#eval! test


-- x.popCountAuxRec (setWidth (w + 1) (extractLsb' 0 1 x)) 1

-- (setWidth (w) x).popCountAuxRec (setWidth (w) (extractLsb' 0 1 (setWidth (w) x))) 1 + (x.extractLsb' w 1).setWidth (w + 1)

def scatter (xs : BitVec (n * w)) : List (BitVec w) :=
  List.map (fun i => xs.extractLsb' (i * w) w) (List.range n)

def sumVecs (xs : List (BitVec w)) : BitVec w :=
  xs.foldl (fun acc x => acc + x) 0#w

/-- zero extend each of the bits `x[i]`, and produce a packed bitvector. -/
def extractAndExtendPopulate (x : BitVec w) : BitVec (w * w) :=
  let res := BitVec.extractAndExtendPopulateAux 0 x 0#0 (by omega) (by intros; omega)
  res

-- setWidth (w + 1 + 1) (sumVecs (setWidth (w + 1) x).extractAndExtendPopulate.scatter) +
--     setWidth (w + 1 + 1) (extractLsb' (w + 1) 1 x) =
--   sumVecs x.extractAndExtendPopulate.scatter

def test1 : IO Unit := do
  let w := 5
  let wlt := 4
  for xx in [0 : 2^w] do
    let x := BitVec.ofNat w xx
    let lhs := setWidth w (sumVecs (scatter (extractAndExtendPopulate (setWidth wlt x)))) +
        setWidth w (extractLsb' wlt 1 x)
    let rhs := sumVecs (scatter (extractAndExtendPopulate x))
    if lhs ≠ rhs then IO.print f!"\nFAIL with x = {x}, where pop1 = {lhs.toNat} and pop2 = {rhs.toNat}"

    IO.println ""

#eval! test1
