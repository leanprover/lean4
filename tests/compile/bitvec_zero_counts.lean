module
import Init.Data.BitVec.Lemmas

/-! Kernel and runtime regression tests for efficient BitVec leading/trailing-zero counting. -/

set_option exponentiation.threshold 8192

example : ((1#8192) <<< 8191).clz = 0 := rfl
example : ((1#8192) <<< 8191).ctz = 8191 := rfl
example : ((1#8192) <<< 4096).clz = 4095 := rfl
example : (1#8192).clz = 8191#8192 := rfl
example : (3#8192).ctz = 0#8192 := rfl
example : (0#8192).ctz = 8192#8192 := rfl
example : (0#0).clz = 0#0 := rfl
example : (0#0).ctz = 0#0 := rfl
example (x : BitVec w) : x.clz.toNat =
    if x = 0 then w else w - (x.toNat.log2 + 1) := BitVec.toNat_clz x

private def check (w n : Nat) : IO Unit := do
  let x := BitVec.ofNat w n
  let mut leading := 0
  let mut trailing := 0
  for i in [:w] do
    if leading == i && !x.getLsbD (w - 1 - i) then leading := leading + 1
    if trailing == i && !x.getLsbD i then trailing := trailing + 1
  unless x.clz.toNat == leading && x.ctz.toNat == trailing do
    throw <| IO.userError s!"zero counts: width={w}, value={n}"

public def main : IO Unit := do
  for w in [:9] do
    for n in [:1 <<< w] do check w n
  for w in [31, 32, 33, 63, 64, 65, 127, 128, 129, 1024, 8192] do
    check w 0
    check w 1
    check w ((1 <<< w) - 1)
    for k in [0, 1, w / 2, w - 1] do
      check w (1 <<< k)
      check w (3 <<< k)
