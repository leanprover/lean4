import Std.Data.Iterators

/- definitions -/

def sum₁ (xs : Array Nat) : Nat :=
  xs.iter.fold (init := 0) (· + ·)

def sum₂ (xs : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for x in xs do
    sum := sum + x
  return sum

def isolatedMap (xs : Array Nat) : Nat :=
  xs.iter.map (· * 2) |>.fold (init := 0) (· + ·)

def isolatedFilterMap (xs : Array Nat) : Nat :=
  xs.iter.filterMap (fun x => Option.guard (· % 2 = 0) (3 * x)) |>.fold (init := 0) (· + ·)

def isolatedTake (xs : Array Nat) (n : Nat) : Nat :=
  xs.iter.take n |>.fold (init := 0) (· + ·)

def isolatedDrop (xs : Array Nat) (n : Nat) : Nat :=
  xs.iter.drop n |>.fold (init := 0) (· + ·)

def isolatedTakeWhile (xs : Array Nat) : Nat :=
  xs.iter.takeWhile (· < 100000) |>.fold (init := 0) (· + ·)

def isolatedDropWhile (xs : Array Nat) : Nat :=
  xs.iter.dropWhile (· < 100000) |>.fold (init := 0) (· + ·)

def isolatedZip (xs : Array Nat) (ys : Array Nat) : Nat :=
  xs.iter.zip ys.iter |>.fold (init := 0) (fun | acc, (a, b) => acc + a * b)

def isolatedSteppedRange (n : Nat) : Nat :=
  (*...n).iter.stepSize 2 |>.fold (init := 0) (· + ·)

section Primes

def numDivisors (n : Nat) := (1...=n).iter
  |>.filter (n % · = 0)
  |>.size

def isPrime (n : Nat) := numDivisors n == 2

def primes (n : Nat) := (*...* : Std.PRange _ Nat).iter.take n
  |>.filter isPrime
  |>.toList

end Primes

def printEveryNth (xs : List Nat) (n : Nat) : IO Unit := do
  for x in xs, i in (*...* : Std.PRange _ Nat) do
    if i % n = 0 then
      IO.println s!"xs[{i}] = {x}"

def printEveryNthSliceBased (xs : Array Nat) (n : Nat) : IO Unit := do
  for x in xs[*...*], i in (*...* : Std.PRange _ Nat) do
    if i % n = 0 then
      IO.println s!"xs[{i}] = {x}"

def longChainOfCombinators (xs : Array Nat) : Nat :=
  xs.iter.zip (2...* : Std.PRange _ Nat).iter
    |>.filter (fun | (_, i) => i % 2 = 0)
    |>.attachWith (fun _ => True) (fun _ _ => .intro)
    |>.map (fun x => x.1.2)
    |>.drop 1
    |>.take 10000000
    |>.takeWhile (fun x => x < 5000000)
    |>.fold (init := 0) (· + ·)

/- evaluations -/

def xs : Array Nat := (*...100000).iter.toArray

def l : List Nat := (*...100000).iter.toList

#eval! sum₁ xs

#eval! sum₂ xs

#eval! isolatedMap xs

#eval! isolatedFilterMap xs

#eval! isolatedTake xs 1000000

#eval! isolatedDrop xs 100000

#eval! isolatedTakeWhile xs

#eval! isolatedDropWhile xs

#eval! isolatedZip xs xs

#eval! isolatedSteppedRange 1000000

#eval! longChainOfCombinators xs

#eval! (*...1000000).iter.fold (init := 0) (· + ·)

#eval! primes 3000

#eval! printEveryNth l 10000

#eval! printEveryNthSliceBased xs 10000
