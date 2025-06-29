def computeFuel (mass : Nat) : Nat :=
  let rec go acc cur :=
    let n := cur / 3 - 2
    if n = 0 then acc + cur else go (acc + cur) n
  termination_by cur
  go 0 mass - mass

def computeFuel' (mass : Nat) : Nat :=
  let rec go acc cur :=
    letI n := cur / 3 - 2
    if n = 0 then acc + cur else go (acc + cur) n
  termination_by cur
  go 0 mass - mass
