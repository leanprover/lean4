/-! Benchmarks evaluating a `Nat` literal between `2^32` and `2^63` in a loop (#16007). -/

def main : List String → IO Unit
| [n] => do
  let mut acc := 0
  for i in 0...n.toNat! do
    acc := (acc + i * 4294967296) % 1000000007
  IO.println acc
| _ => throw <| .userError "give upper bound"
