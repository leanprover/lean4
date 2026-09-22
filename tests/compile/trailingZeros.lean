module
import Init.Data.Dyadic.Basic

/-! Regression tests for arbitrary-precision trailing-zero counting (#15264). -/

example : Nat.trailingZeros 0 = 0 := by decide
example : Nat.trailingZeros 1 = 0 := rfl
example : Nat.trailingZeros 17 = 0 := rfl
example : Nat.trailingZeros 24 = 3 := by decide
example : Int.trailingZeros 0 = 0 := rfl
example : Int.trailingZeros (-1) = 0 := rfl
example : Int.trailingZeros (-24) = 3 := by decide
example : Int.trailingZeros (-48) = Int.trailingZeros (-24) + 1 := by
  rw [Int.trailingZeros_def]
  decide
example : Nat.trailingZeros (3 <<< 500) = 500 := rfl
example : Nat.trailingZeros (1 <<< 64) = 64 := rfl
example : Nat.trailingZeros (1 <<< 128) = 128 := rfl
example : Nat.trailingZeros ((1 <<< 64) + 8) = 3 := rfl
example : Int.trailingZeros (-(3 <<< 500)) = 500 := rfl
example : Nat.trailingZeros (3 <<< 8192) = 8192 := rfl
example : Int.trailingZeros (-(3 <<< 8192)) = 8192 := rfl
example : Nat.trailingZeros ((1 <<< 65536) + 1) = 0 := rfl
example : Nat.trailingZeros (((1 <<< 65536) + 1) <<< 8193) = 8193 := rfl
example : [63, 64, 65, 127, 128, 129].map (fun k => Nat.trailingZeros (3 <<< k)) =
    [63, 64, 65, 127, 128, 129] := rfl
example (i : Int) : i.trailingZeros = i.natAbs.trailingZeros :=
  Int.trailingZeros_eq_natAbs i

example : ¬ (16 : Int) ∣ 24 := Int.two_pow_trailingZeros_add_one_not_dvd (by decide)
example : ¬ (16 : Int) ∣ -24 := Int.two_pow_trailingZeros_add_one_not_dvd (by decide)
example : ¬ (2 : Int) ∣ 7 := Int.two_pow_trailingZeros_add_one_not_dvd (by decide)

def check (odd k : Nat) : IO Unit := do
  let n := odd <<< k
  unless n.trailingZeros == k do
    throw <| IO.userError s!"Nat: odd={odd}, shift={k}"
  for i in [(n : Int), -(n : Int)] do
    unless i.trailingZeros == k do
      throw <| IO.userError s!"Int: shift={k}"
    match Dyadic.ofIntWithPrec i 17 with
    | .zero => throw <| IO.userError "unexpected zero"
    | .ofOdd coefficient prec _ =>
      unless coefficient == (if i < 0 then -(odd : Int) else (odd : Int)) &&
          prec == 17 - (k : Int) do
        throw <| IO.userError s!"Dyadic: shift={k}"

public def main : IO Unit := do
  unless (0 : Nat).trailingZeros == 0 && (0 : Int).trailingZeros == 0 do
    throw <| IO.userError "zero"
  for odd in [:128] do
    for k in [:10] do
      check (2 * odd + 1) k
  for odd in [1, 3, 17, (1 <<< 31) + 1, (1 <<< 64) + 1, (1 <<< 1024) + 1] do
    for k in [0, 1, 2, 30, 31, 32, 33, 62, 63, 64, 65, 127, 128, 129, 1024, 65536] do
      check odd k
