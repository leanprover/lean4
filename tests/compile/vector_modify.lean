module

import Init.Data.Vector.Lemmas

/-! Test vector modification across module boundaries, including kernel reduction,
out-of-bounds indices, shared inputs, and nested updates in compiled code. -/

example : (#v[1, 2, 3].modify 0 (· + 10)) = #v[11, 2, 3] := rfl
example : (#v[1, 2, 3].modify 2 (· * 10)) = #v[1, 2, 30] := rfl
example : (#v[1, 2, 3].modify 3 (· + 10)) = #v[1, 2, 3] := rfl
example : (#v[] : Vector Nat 0).modify 0 (· + 1) = #v[] := rfl

example (xs : Vector Nat n) (i : Nat) (f : Nat → Nat) :
    (xs.modify i f).toArray = xs.toArray.modify i f := by simp

example (xs : Vector Nat n) (i : Nat) (f : Nat → Nat) :
    (xs.modify i f).toList = xs.toList.modify i f := by simp

example (xs : Vector Nat n) (i : Nat) (f : Nat → Nat) (h : n ≤ i) :
    xs.modify i f = xs := by simp [Vector.modify_eq_of_size_le h]

def modifyRows (n m : Nat) : Vector (Vector Nat m) n := Id.run do
  let mut rows := (Vector.ofFn fun i : Fin n => (Vector.replicate m i.val).markLinear).markLinear
  for i in [0:n] do
    rows := rows.modify i fun row => row.modify 0 (· + 10)
  return rows

public def main : IO Unit := do
  for n in [0:8] do
    let xs := Vector.ofFn (n := n) fun i => i.val + 1
    for i in [0:10] do
      let ys := xs.modify i (· * 3)
      unless ys.toList == xs.toList.modify i (· * 3) do
        throw <| IO.userError s!"incorrect modification at {i} in {xs.toList}"
      unless xs.toList == List.range' 1 n do
        throw <| IO.userError "modification changed a shared input"
  let rows := #v[#v[1, 2], #v[3, 4]]
  unless rows.modify 1 (·.modify 0 (· + 10)) == #v[#v[1, 2], #v[13, 4]] do
    throw <| IO.userError "incorrect nested modification"
  unless (#v[1, 2, 3].modify 3 fun _ => panic! "out-of-bounds callback") == #v[1, 2, 3] do
    throw <| IO.userError "incorrect out-of-bounds modification"
  unless modifyRows 3 2 == #v[#v[10, 0], #v[11, 1], #v[12, 2]] do
    throw <| IO.userError "incorrect in-place row modification"
