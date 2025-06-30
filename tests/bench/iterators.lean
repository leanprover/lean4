import Std.Data.Iterators

/- definitions -/

def sum₁ (xs : Array Nat) : Nat :=
  xs.iter.fold (init := 0) (· + ·)

def sum₂ (xs : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for x in xs do
    sum := sum + x
  return sum

def numDivisors (n : Nat) := (1...=n).iter
  |>.filter (n % · = 0)
  |>.size

def isPrime (n : Nat) := numDivisors n == 2

def primes (n : Nat) := (*...* : Std.PRange _ Nat).iter.take n
  |>.filter isPrime
  |>.toList

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

def xs : Array Nat := (*...1000000).iter.toArray

def l : List Nat := (*...1000000).iter.toList

#eval sum₁ xs

#eval sum₂ xs

#eval longChainOfCombinators xs

#eval (*...1000000).iter.fold (init := 0) (· + ·)

#eval primes 3000

#eval printEveryNth l 10000

#eval printEveryNthSliceBased xs 10000
