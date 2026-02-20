import Std.Data.Iterators

/-
This benchmark measures the performance of iterators. The file starts with various function
declarations. The functions are then called from `main`.

The benchmark is run in three settings.

* The runtime of the compiled program is measured in `iterators (compiled)`.
* The time taken to interpret the script, including running `main`, is measured in
  `iterators (interpreted)`.
* The time taken to interpret the script, without running `main`, is measured in
  `interators (elab)`.
-/

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
  |>.count

def isPrime (n : Nat) := numDivisors n == 2

def primes (n : Nat) := (*...* : Std.Rii Nat).iter.take n
  |>.filter isPrime
  |>.toList

end Primes

def printEveryNth (xs : List Nat) (n : Nat) : IO Unit := do
  for x in xs, i in (*...* : Std.Rii Nat) do
    if i % n = 0 then
      IO.println s!"xs[{i}] = {x}"

def printEveryNthSliceBased (xs : Array Nat) (n : Nat) : IO Unit := do
  for x in xs[*...*], i in (*...* : Std.Rii Nat) do
    if i % n = 0 then
      IO.println s!"xs[{i}] = {x}"

def longChainOfCombinators (xs : Array Nat) : Nat :=
  xs.iter.zip (2...*).iter
    |>.filter (fun | (_, i) => i % 2 = 0)
    |>.attachWith (fun _ => True) (fun _ _ => .intro)
    |>.map (fun x => x.1.2)
    |>.drop 1
    |>.take 10000000
    |>.takeWhile (fun x => x < 5000000)
    |>.fold (init := 0) (· + ·)

def xs : Array Nat := (*...100000).iter.toArray

def l : List Nat := (*...100000).iter.toList

/- evaluations -/

@[noinline]
def run' (f : Unit → α) : IO α := do
  return f ()

notation "run " t => (fun _ => ()) <$> run' fun _ => t

def main : IO Unit := do
  run sum₁ xs
  run sum₂ xs
  run isolatedMap xs
  run isolatedFilterMap xs
  run isolatedTake xs 1000000
  run isolatedDrop xs 1000000
  run isolatedTakeWhile xs
  run isolatedDropWhile xs
  run isolatedZip xs xs
  run isolatedSteppedRange 1000000
  run longChainOfCombinators xs
  run (*...1000000).iter.fold (init := 0) (· + ·)
  run primes 3000
  printEveryNth l 10000
  printEveryNthSliceBased xs 10000
