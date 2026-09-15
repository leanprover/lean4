module

/-!
Tests bignum result allocation from compiled and interpreted callers. Retain inputs and multiple
results across later allocations, exercise shared operands, cancellation, signed division, and
conversion across scalar/bignum boundaries, and round-trip decimal representations.
-/

private def values (seed : Nat) : Array Nat :=
  #[0, 1, 2, 3, 2 ^ 30 - 1, 2 ^ 30, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 31 + 1,
    2 ^ 32 - 1, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64, 2 ^ 128 + 1,
    2 ^ 256 - 1, 2 ^ 1024 + 3].map (· + seed)

public def main (args : List String) : IO Unit := do
  let inputs := values args.length
  for a in inputs do
    unless a.repr.toNat? = some a do
      throw <| IO.userError "Nat decimal round-trip failed"
    for b in inputs do
      let x : Int := a
      let y : Int := b
      for s in #[x, -x] do
        for t in #[y, -y] do
          let results := #[s + t, s - t, s * t, -s, s + s, s - s, s * s]
          -- Later allocations must not invalidate either retained inputs or results.
          let copies := results.map fun r => r + (2 ^ 2048 : Int)
          for r in results do
            unless r.repr.toInt? = some r do
              throw <| IO.userError "Int decimal round-trip failed"
          unless copies.map (· - (2 ^ 2048 : Int)) = results &&
              results[0]! - t = s && results[1]! + t = s &&
              results[2]! = t * s && results[3]! = -s &&
              results[4]! = s * 2 && results[5]! = 0 && results[6]! = s * s &&
              s.natAbs = a && t.natAbs = b do
            throw <| IO.userError "retained Int arithmetic failed"
          unless s.ediv t * t + s.emod t = s && s.tdiv t * t + s.tmod t = s do
            throw <| IO.userError "signed division failed"
      let q := a / b
      let r := a % b
      let product := a * b
      unless q * b + r = a && product = b * a &&
          (if b = 0 then product = 0 else product / b = a) &&
          (a - b) + min a b = a && (a ^ 3) = a * a * a &&
          (a &&& b) + (a ||| b) = a + b do
        throw <| IO.userError "retained Nat arithmetic failed"
