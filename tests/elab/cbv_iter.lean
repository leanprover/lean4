import Std

/-! ### Basic producer tests -/

example : [1, 2, 3].iter.toList = [1, 2, 3] := by cbv
example : [1, 2, 3].iter.toArray = #[1, 2, 3] := by cbv
example : ([] : List Nat).iter.toList = [] := by cbv
example : ([] : List Nat).iter.toArray = #[] := by cbv

/-! ### Map tests -/

example : ([1, 2, 3].iter.map (· + 1)).toList = [2, 3, 4] := by cbv
example : ([1, 2, 3].iter.map (· + 1)).toArray = #[2, 3, 4] := by cbv
example : ([1, 2, 3].iter.map (· * 2)).toList = [2, 4, 6] := by cbv
example : (([] : List Nat).iter.map (· + 1)).toList = [] := by cbv

/-! ### Filter tests -/

example : ([1, 2, 3, 4].iter.filter (· % 2 == 0)).toList = [2, 4] := by cbv
example : ([1, 2, 3, 4].iter.filter (· % 2 == 0)).toArray = #[2, 4] := by cbv

/-! ### FilterMap tests -/

example : ([1, 2, 3, 4].iter.filterMap (fun x => if x % 2 == 0 then some (x * 10) else none)).toList
    = [20, 40] := by cbv

/-! ### Fold tests -/

example : [1, 2, 3].iter.fold (· + ·) 0 = 6 := by cbv
example : [1, 2, 3, 4].iter.fold (· * ·) 1 = 24 := by cbv
example : ([] : List Nat).iter.fold (· + ·) 0 = 0 := by cbv

/-! ### Composed combinator tests -/

example : ([1, 2, 3, 4].iter.filter (· % 2 == 0) |>.map (· * 10)).toList = [20, 40] := by cbv
example : ([1, 2, 3].iter.map (· + 1) |>.filter (· % 2 == 0)).toList = [2, 4] := by cbv
example : ([1, 2, 3].iter.map (· * 2) |>.map (· + 1)).toList = [3, 5, 7] := by cbv

/-! ### String operations using iterators internally -/

example : "abc".contains 'b' = true := by cbv
example : "abc".contains 'd' = false := by cbv
example : "hello".contains (· == 'l') = true := by cbv
example : String.toNat? "192" = some 192 := by cbv
example : String.toNat? "0" = some 0 := by cbv
example : String.toNat? "" = none := by cbv
example : "hello".foldl (fun n _ => n + 1) 0 = 5 := by cbv

-- Tests requiring `String.contains_string_eq` (not yet available):
def filterBySubstring (strings : Array String) (substring : String) : Array String :=
  strings.filter (·.contains substring)

example : filterBySubstring #[] "john" = #[] := by cbv
example : filterBySubstring #["xxx", "asd", "xxy", "john doe", "xxxAAA", "xxx"] "xxx" = #["xxx", "xxxAAA", "xxx"] := by cbv
example : filterBySubstring #["xxx", "asd", "aaaxxy", "john doe", "xxxAAA", "xxx"] "xx" = #["xxx", "aaaxxy", "xxxAAA", "xxx"] := by cbv
example : filterBySubstring #["grunt", "trumpet", "prune", "gruesome"] "run" = #["grunt", "prune"] := by cbv


def allPrefixes (string : String) : Array String.Slice :=
  if string = "" then
    #[]
  else
    ((string.positions.drop 1).map (string.sliceTo ·.1) |>.toArray).push string

example : allPrefixes "" = #[] := by cbv
example : allPrefixes "asdfgh" == #["a".toSlice, "as", "asd", "asdf", "asdfg", "asdfgh"] := by cbv
example : allPrefixes "WWW" == #["W".toSlice, "WW", "WWW"] := by cbv

def sumSquares (xs : List Rat) : Int :=
  xs.map (·.ceil ^ (2 : Nat)) |>.sum

/-! ### Rational arithmetic tests -/

example : sumSquares [1, 2, 3] = 14 := by cbv
example : sumSquares [1.0, 2, 3] = 14 := by cbv
example : sumSquares [1, 3, 5, 7] = 84 := by cbv
example : sumSquares [1.4, 4.2, 0] = 29 := by cbv
example : sumSquares [-2.4, 1, 1] = 6 := by cbv
example : sumSquares [100, 1, 15, 2] = 10230 := by cbv
example : sumSquares [10000, 10000] = 200000000 := by cbv
example : sumSquares [-1.4, 4.6, 6.3] = 75 := by cbv
example : sumSquares [-1.4, 17.9, 18.9, 19.9] = 1086 := by cbv
example : sumSquares [0] = 0 := by cbv
example : sumSquares [-1] = 1 := by cbv
example : sumSquares [-1, 1, 0] = 2 := by cbv

/-! ### String case swapping and reversal tests -/

def reverseString (s : String) : String :=
  s.revChars.fold (init := "") fun sofar c => sofar.push c

def swapCase (c : Char) : Char :=
  if c.isUpper then
    c.toLower
  else if c.isLower then
    c.toUpper
  else
    c

def solve (s : String) : String :=
  if s.contains Char.isAlpha then
    s.map swapCase
  else
    reverseString s

example : solve "AsDf" = "aSdF" := by cbv
example : solve "1234" = "4321" := by cbv
example : solve "ab" = "AB" := by cbv
example : solve "#a@C" = "#A@c" := by cbv
example : solve "#AsdfW^45" = "#aSDFw^45" := by cbv
example : solve "#6@2" = "2@6#" := by cbv
example : solve "#$a^D" = "#$A^d" := by cbv
example : solve "#ccc" = "#CCC" := by cbv


/-! ### Subarray iteration tests -/

def isSorted (xs : Array Nat) : Bool := Id.run do
  if h : xs.size > 0 then
    let mut last := xs[0]
    let mut repeated := false
    for x in xs[1...*] do
      match compare last x with
      | .lt =>
        last := x
        repeated := false
      | .eq =>
        if repeated then
          return false
        else
          repeated := true
      | .gt =>
        return false
  return true

example : isSorted #[5] = true := by cbv
example : isSorted #[1, 2, 3, 4, 5] = true := by cbv
example : isSorted #[1, 3, 2, 4, 5] = false := by cbv
example : isSorted #[1, 2, 3, 4, 5, 6] = true := by cbv
example : isSorted #[1, 2, 3, 4, 5, 6, 7] = true := by cbv
example : isSorted #[1, 3, 2, 4, 5, 6, 7] = false := by cbv
example : isSorted #[] = true := by cbv
example : isSorted #[1] = true := by cbv
example : isSorted #[3, 2, 1] = false := by cbv
example : isSorted #[1, 2, 2, 2, 3, 4] = false := by cbv
example : isSorted #[1, 2, 3, 3, 3, 4] = false := by cbv
example : isSorted #[1, 2, 2, 3, 3, 4] = true := by cbv
example : isSorted #[1, 2, 3, 4] = true := by cbv

/-! ### Inclusive range iteration tests -/

def f (n : Nat) : List Nat := Id.run do
  let mut ret : List Nat := []
  for i in 1...=n do
    if i % 2 = 0 then
      let mut x := 1
      for j in 1...=i do x := x * j
      ret := x :: ret
    else
      let mut x := 0
      for j in 1...=i do x := x + j
      ret := x :: ret
  return ret.reverse

example : f 5 = [1, 2, 6, 24, 15] := by cbv
example : f 7 = [1, 2, 6, 24, 15, 720, 28] := by cbv
example : f 1 = [1] := by cbv
example : f 3 = [1, 2, 6] := by cbv


def hasCloseElements (xs : Array Rat) (threshold : Rat) : Bool := Id.run do
  let sorted := xs.mergeSort
  for h : i in *...(sorted.size - 1) do
    if (sorted[i + 1] - sorted[i]).abs < threshold then
      return true
  return false

example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.3 = true := by cbv
example : hasCloseElements #[1.0, 2.0, 3.9, 4.0, 5.0, 2.2] 0.05 = false := by cbv
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.95 = true := by cbv
example : hasCloseElements #[1.0, 2.0, 5.9, 4.0, 5.0] 0.8 = false := by cbv
example : hasCloseElements #[1.0, 2.0, 3.0, 4.0, 5.0, 2.0] 0.1 = true := by cbv
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 1.0 = true := by cbv
example : hasCloseElements #[1.1, 2.2, 3.1, 4.1, 5.1] 0.5 = false := by cbv

/-! ### Array.iter producer tests -/

example : #[1, 2, 3].iter.toList = [1, 2, 3] := by cbv
example : #[1, 2, 3].iter.toArray = #[1, 2, 3] := by cbv
example : (#[] : Array Nat).iter.toList = [] := by cbv
example : (#[1, 2, 3].iter.map (· + 10)).toList = [11, 12, 13] := by cbv
example : (#[1, 2, 3, 4].iter.filter (· % 2 == 0)).toArray = #[2, 4] := by cbv

/-! ### FlatMap tests -/

example : ([1, 2, 3].iter.flatMap (fun n => List.replicate n n |>.iter)).toList
    = [1, 2, 2, 3, 3, 3] := by cbv
example : ([1, 2].iter.flatMap (fun n => [n, n * 10].iter)).toList
    = [1, 10, 2, 20] := by cbv
example : (([] : List Nat).iter.flatMap (fun n => [n].iter)).toList = [] := by cbv

/-! ### TakeWhile tests -/

example : ([1, 2, 3, 4, 5].iter.takeWhile (· < 4)).toList = [1, 2, 3] := by cbv
example : ([1, 2, 3, 4, 5].iter.takeWhile (· < 1)).toList = [] := by cbv
example : ([1, 2, 3].iter.takeWhile (· < 10)).toList = [1, 2, 3] := by cbv

/-! ### DropWhile tests -/

example : ([1, 2, 3, 4, 5].iter.dropWhile (· < 4)).toList = [4, 5] := by cbv
example : ([1, 2, 3, 4, 5].iter.dropWhile (· < 1)).toList = [1, 2, 3, 4, 5] := by cbv
example : ([1, 2, 3].iter.dropWhile (· < 10)).toList = [] := by cbv

/-! ### Zip tests -/

example : ([1, 2, 3].iter.zip [10, 20, 30].iter).toList = [(1, 10), (2, 20), (3, 30)] := by cbv
example : ([1, 2].iter.zip [10, 20, 30].iter).toList = [(1, 10), (2, 20)] := by cbv
example : ([1, 2, 3].iter.zip ([] : List Nat).iter).toList = [] := by cbv

/-! ### Composed new combinator tests -/

def dotProduct (xs ys : List Int) : Int :=
  (xs.iter.zip ys.iter |>.map (fun (a, b) => a * b) |>.fold (· + ·) 0)

example : dotProduct [1, 2, 3] [4, 5, 6] = 32 := by cbv
example : dotProduct [1, 0, -1] [1, 1, 1] = 0 := by cbv
example : dotProduct [] [] = 0 := by cbv

def runLengthEncode (xs : List Nat) : List (Nat × Nat) := Id.run do
  let mut result : List (Nat × Nat) := []
  let mut current := 0
  let mut count := 0
  for x in xs do
    if count == 0 then
      current := x
      count := 1
    else if x == current then
      count := count + 1
    else
      result := (current, count) :: result
      current := x
      count := 1
  if count > 0 then
    result := (current, count) :: result
  return result.reverse

example : runLengthEncode [1, 1, 2, 3, 3, 3, 2, 2] = [(1, 2), (2, 1), (3, 3), (2, 2)] := by cbv
example : runLengthEncode [] = [] := by cbv
example : runLengthEncode [5] = [(5, 1)] := by cbv

/-! ### Range iteration tests for all interval types -/

-- Rco (closed-open): a...b
def sumRco (a b : Nat) : Nat := Id.run do
  let mut s := 0
  for i in a...b do s := s + i
  return s

example : sumRco 0 5 = 10 := by cbv
example : sumRco 1 4 = 6 := by cbv
example : sumRco 3 3 = 0 := by cbv
example : sumRco 0 0 = 0 := by cbv
example : sumRco 0 1 = 0 := by cbv

-- Rcc (closed-closed): a...=b (already tested via `f`, adding direct tests)
def sumRcc (a b : Nat) : Nat := Id.run do
  let mut s := 0
  for i in a...=b do s := s + i
  return s

example : sumRcc 0 4 = 10 := by cbv
example : sumRcc 1 3 = 6 := by cbv
example : sumRcc 3 3 = 3 := by cbv
example : sumRcc 5 3 = 0 := by cbv

-- Rio (inclusive-open): *...b (already tested via hasCloseElements, adding direct tests)
def sumRio (b : Nat) : Nat := Id.run do
  let mut s := 0
  for i in *...b do s := s + i
  return s

example : sumRio 5 = 10 := by cbv
example : sumRio 1 = 0 := by cbv
example : sumRio 0 = 0 := by cbv

-- Ric (inclusive-closed): *...=b
def sumRic (b : Nat) : Nat := Id.run do
  let mut s := 0
  for i in *...=b do s := s + i
  return s

example : sumRic 4 = 10 := by cbv
example : sumRic 0 = 0 := by cbv
example : sumRic 1 = 1 := by cbv

-- Roc (open-closed): a<...=b
def sumRoc (a b : Nat) : Nat := Id.run do
  let mut s := 0
  for i in a<...=b do s := s + i
  return s

example : sumRoc 0 4 = 10 := by cbv
example : sumRoc 0 1 = 1 := by cbv
example : sumRoc 3 3 = 0 := by cbv
example : sumRoc 1 5 = 14 := by cbv

-- Roo (open-open): a<...b
def sumRoo (a b : Nat) : Nat := Id.run do
  let mut s := 0
  for i in a<...b do s := s + i
  return s

example : sumRoo 0 5 = 10 := by cbv
example : sumRoo 0 1 = 0 := by cbv
example : sumRoo 3 3 = 0 := by cbv
example : sumRoo 1 5 = 9 := by cbv

-- Rco (closed-open): a...b
example : (1...3).iter.toList = [1, 2] := by cbv
example : (1...3).iter.toArray = #[1, 2] := by cbv
example : (0...5).iter.toList = [0, 1, 2, 3, 4] := by cbv
example : (3...3).iter.toList = [] := by cbv

-- Rcc (closed-closed): a...=b
example : (1...=3).iter.toList = [1, 2, 3] := by cbv
example : (1...=3).iter.toArray = #[1, 2, 3] := by cbv
example : (0...=4).iter.toList = [0, 1, 2, 3, 4] := by cbv
example : (3...=3).iter.toList = [3] := by cbv
example : (5...=3).iter.toList = [] := by cbv

-- Rio (inclusive-open): *...b
example : ((*...5 : Std.Rio Nat)).iter.toList = [0, 1, 2, 3, 4] := by cbv
example : ((*...0 : Std.Rio Nat)).iter.toList = [] := by cbv

-- Ric (inclusive-closed): *...=b
example : ((*...=4 : Std.Ric Nat)).iter.toList = [0, 1, 2, 3, 4] := by cbv
example : ((*...=0 : Std.Ric Nat)).iter.toList = [0] := by cbv

-- Roc (open-closed): a<...=b
example : (1<...=4).iter.toList = [2, 3, 4] := by cbv
example : (1<...=4).iter.toArray = #[2, 3, 4] := by cbv
example : (3<...=3).iter.toList = [] := by cbv
example : (0<...=5).iter.toList = [1, 2, 3, 4, 5] := by cbv

-- Roo (open-open): a<...b
example : (1<...5).iter.toList = [2, 3, 4] := by cbv
example : (1<...5).iter.toArray = #[2, 3, 4] := by cbv
example : (3<...3).iter.toList = [] := by cbv
example : (0<...5).iter.toList = [1, 2, 3, 4] := by cbv
