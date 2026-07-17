import Std.Internal.Do
import Std.Tactic.Do

/-!
Benchmark for `vcgen`/`grind` over the Verina verification corpus. Each program is
discharged with `vcgen … with finish`; supporting lemmas and the manual
verification-condition steps are `sorry`'d, so the elaboration cost measured here is
the `vcgen` decomposition and `grind` search itself. Each fixture lives in its own
namespace with `@[local grind]` lemmas.
-/

open Std.Internal.Do Lean.Order
set_option mvcgen.warning false
set_option warn.sorry false
set_option maxHeartbeats 1000000

namespace E_containsConsecutiveNumbers

@[local grind] def HasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

def containsConsecutiveNumbers (a : Array Int) : Id Bool := do
  if a.size < 2 then
    return false
  else
    let mut i : Nat := 0
    let mut found : Bool := false
    while i + 1 < a.size ∧ found = false do
      if a[i]! + 1 = a[i + 1]! then
        found := true
      else
        i := i + 1
    return found

theorem containsConsecutiveNumbers_spec (a : Array Int) :
    (containsConsecutiveNumbers a).run = true ↔ HasConsecutivePair a := by
  generalize h : (containsConsecutiveNumbers a).run = r
  apply Id.of_wp_run_eq h
  vcgen [containsConsecutiveNumbers] invariants
  | inv1 => fun r => match r with
    | .inl ⟨i, found⟩ => i + 1 ≤ a.size ∧
        (found = false → ∀ j : Nat, j < i → a[j]! + 1 ≠ a[j + 1]!) ∧
        (found = true → HasConsecutivePair a)
    | .inr ⟨i, found⟩ => (i + 1 ≥ a.size ∨ found = true) ∧
        (found = false → ∀ j : Nat, j < i → a[j]! + 1 ≠ a[j + 1]!) ∧
        (found = true → HasConsecutivePair a)
  | inv2 => fun ⟨i, found⟩ => (a.size + 1 - i) * 2 + (if found = false then 1 else 0)
  with finish

end E_containsConsecutiveNumbers

namespace E_countSumDivisibleBy

def digitSum (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + digitSum (n / 10)

@[local grind] def divisesDigitSum (d k : Nat) : Bool := decide (d ∣ digitSum k)

def countSumDivisibleBy (n : Nat) (d : Nat) : Id Nat := do
  let mut count := 0
  let mut k := 0
  while k < n do
    let sum := digitSum k
    if sum % d = 0 then
      count := count + 1
    k := k + 1
  return count

theorem countSumDivisibleBy_spec (n d : Nat) (_hd : d > 0) :
    (countSumDivisibleBy n d).run = ((List.range n).countP (divisesDigitSum d)) := by
  generalize h : (countSumDivisibleBy n d).run = r
  apply Id.of_wp_run_eq h
  vcgen [countSumDivisibleBy] invariants
  | inv1 => fun r => match r with
    | .inl ⟨count, k⟩ => k ≤ n ∧
        count = ((List.range k).countP (divisesDigitSum d))
    | .inr ⟨count, k⟩ => k = n ∧
        count = ((List.range k).countP (divisesDigitSum d))
  | inv2 => fun ⟨count, k⟩ => n + 1 - k
  with finish [List.range_succ, Nat.dvd_iff_mod_eq_zero, divisesDigitSum]

end E_countSumDivisibleBy

namespace E_cubeElements

@[local grind] def intCube (x : Int) : Int := x * x * x

def cubeElements (a : Array Int) : Id (Array Int) := do
  let mut result := Array.replicate a.size (0 : Int)
  let mut i : Nat := 0
  while i < a.size do
    let x := a[i]!
    result := result.set! i (intCube x)
    i := i + 1
  return result

theorem cubeElements_spec (a : Array Int) :
    (cubeElements a).run.size = a.size ∧
    (∀ (i : Nat), i < a.size → (cubeElements a).run[i]! = intCube (a[i]!)) := by
  generalize h : (cubeElements a).run = r
  apply Id.of_wp_run_eq h
  vcgen [cubeElements] invariants
  | inv1 => fun r => match r with
    | .inl ⟨result, i⟩ => i ≤ a.size ∧ result.size = a.size ∧
        ∀ k, k < i → result[k]! = intCube (a[k]!)
    | .inr ⟨result, i⟩ => i = a.size ∧ result.size = a.size ∧
        ∀ k, k < i → result[k]! = intCube (a[k]!)
  | inv2 => fun ⟨result, i⟩ => a.size + 1 - i
  with finish

end E_cubeElements

namespace E_cubeSurfaceArea

def cubeSurfaceArea (size : Nat) : Id Nat := do
  let area := 6 * (size ^ 2)
  return area

theorem cubeSurfaceArea_spec (size : Nat) :
    (cubeSurfaceArea size).run = 6 * (size ^ 2) := by
  generalize h : (cubeSurfaceArea size).run = r
  apply Id.of_wp_run_eq h
  vcgen [cubeSurfaceArea]
  with finish

end E_cubeSurfaceArea

namespace E_differenceMinMax

@[local grind] def InArray (a : Array Int) (v : Int) : Prop := ∃ (i : Nat), i < a.size ∧ a[i]! = v
@[local grind] def IsMinOfArray (a : Array Int) (mn : Int) : Prop := InArray a mn ∧ (∀ (i : Nat), i < a.size → mn ≤ a[i]!)
@[local grind] def IsMaxOfArray (a : Array Int) (mx : Int) : Prop := InArray a mx ∧ (∀ (i : Nat), i < a.size → a[i]! ≤ mx)
def differenceMinMax (a : Array Int) : Id Int := do
  let mut mn := a[0]!
  let mut mx := a[0]!
  let mut i : Nat := 1
  while i < a.size do
    let v := a[i]!
    if v < mn then mn := v else pure ()
    if v > mx then mx := v else pure ()
    i := i + 1
  return (mx - mn)
theorem differenceMinMax_spec (a : Array Int) (hne : a.size ≠ 0) :
    ∃ (mn : Int) (mx : Int), IsMinOfArray a mn ∧ IsMaxOfArray a mx ∧ (differenceMinMax a).run = mx - mn := by
  generalize h : (differenceMinMax a).run = r
  apply Id.of_wp_run_eq h
  vcgen [differenceMinMax] invariants
  | inv1 => fun r => match r with
    | .inl ⟨mn, mx, i⟩ => 1 ≤ i ∧ i ≤ a.size ∧
        (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
    | .inr ⟨mn, mx, i⟩ => i = a.size ∧
        (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
  | inv2 => fun ⟨_mn, _mx, i⟩ => a.size - i
  with (try finish)
  case vc2 => sorry

end E_differenceMinMax

namespace E_elementWiseModulo

@[local grind] def allNonzero (b : Array Int) : Prop :=
  ∀ (i : Nat), i < b.size → b[i]! ≠ 0

def elementWiseModulo (a : Array Int) (b : Array Int) : Id (Array Int) := do
  let mut result := Array.replicate a.size (0 : Int)
  let mut i : Nat := 0
  while i < a.size do
    result := result.set! i (a[i]! % b[i]!)
    i := i + 1
  return result

theorem elementWiseModulo_spec (a b : Array Int)
    (hsize : a.size = b.size) (_hnz : allNonzero b) :
    (elementWiseModulo a b).run.size = a.size ∧
    (∀ (i : Nat), i < a.size → (elementWiseModulo a b).run[i]! = a[i]! % b[i]!) := by
  generalize h : (elementWiseModulo a b).run = r
  apply Id.of_wp_run_eq h
  vcgen [elementWiseModulo] invariants
  | inv1 => fun r => match r with
    | .inl ⟨result, i⟩ => i ≤ a.size ∧ result.size = a.size ∧
        ∀ k, k < i → result[k]! = a[k]! % b[k]!
    | .inr ⟨result, i⟩ => i = a.size ∧ result.size = a.size ∧
        ∀ k, k < i → result[k]! = a[k]! % b[k]!
  | inv2 => fun ⟨result, i⟩ => a.size + 1 - i
  with finish

end E_elementWiseModulo

namespace E_findSmallest

def findSmallest (s : Array Nat) : Id (Option Nat) := do
  if s.size = 0 then
    return none
  else
    let mut minIndex := 0
    for i in [1:s.size] do
      if s[i]! < s[minIndex]! then
        minIndex := i
    return some s[minIndex]!

theorem findSmallest_spec (s : Array Nat) :
    (match (findSmallest s).run with
     | none => s.size = 0
     | some min =>
        s.size > 0 ∧
        (∃ i, i < s.size ∧ s[i]! = min) ∧
        (∀ j, j < s.size → min ≤ s[j]!)) := by
  generalize h : (findSmallest s).run = r
  apply Id.of_wp_run_eq h
  vcgen [findSmallest] invariants
  | inv1 => fun xs minIndex => minIndex < s.size ∧ s[minIndex]! ≤ s[0]! ∧
      ∀ j, j ∈ xs.prefix → s[minIndex]! ≤ s[j]!
  with finish

end E_findSmallest

namespace E_hasOppositeSign

def hasOppositeSign (a : Int) (b : Int) : Id Bool := do
  if a > 0 ∧ b < 0 then
    return true
  else if a < 0 ∧ b > 0 then
    return true
  else
    return false

theorem hasOppositeSign_spec (a : Int) (b : Int) :
    (hasOppositeSign a b).run = true ↔ ((a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)) := by
  generalize h : (hasOppositeSign a b).run = r
  apply Id.of_wp_run_eq h
  vcgen [hasOppositeSign]
  with finish

end E_hasOppositeSign

namespace E_isDivisibleBy11

def isDivisibleBy11 (n : Int) : Id Bool := do
  let remainder := n % 11
  if remainder = 0 then
    return true
  else
    return false

theorem isDivisibleBy11_spec (n : Int) :
    (isDivisibleBy11 n).run = true ↔ (11 : Int) ∣ n := by
  generalize h : (isDivisibleBy11 n).run = r
  apply Id.of_wp_run_eq h
  vcgen [isDivisibleBy11]
  with finish

end E_isDivisibleBy11

namespace E_isEven

@[local grind] def IntIsEven (n : Int) : Prop := n % 2 = 0

def isEven (n : Int) : Id Bool := do
  if n % 2 = 0 then return true else return false

theorem isEven_spec (n : Int) : (isEven n).run = true ↔ IntIsEven n := by
  generalize h : (isEven n).run = r
  apply Id.of_wp_run_eq h
  vcgen [isEven, IntIsEven]
  with finish

end E_isEven

namespace E_isGreater

def isGreater (n : Int) (a : Array Int) : Id Bool := do
  let mut ok := true
  for i in [0:a.size] do
    if a[i]! < n then
      ok := ok
    else
      ok := false
  return ok

theorem isGreater_spec (n : Int) (a : Array Int) (_h : a.size > 0) :
    (isGreater n a).run = true ↔ (∀ i : Nat, i < a.size → a[i]! < n) := by
  generalize h : (isGreater n a).run = r
  apply Id.of_wp_run_eq h
  vcgen [isGreater] invariants
  | inv1 => fun xs ok => ok = true ↔ (∀ j : Nat, j ∈ xs.prefix → a[j]! < n)
  with finish

end E_isGreater

namespace E_isPrime

@[local grind] private theorem mem_range_toList_iff (n d : Nat) :
    d ∈ [2:n].toList ↔ (2 ≤ d ∧ d < n) := by grind

private theorem mem_self_append_singleton {α} (l : List α) (x : α) : x ∈ l ++ [x] := by
  simp
private theorem mem_append_left' {α} (x : α) (l₁ l₂ : List α) (h : x ∈ l₁) :
    x ∈ l₁ ++ l₂ := by simp [h]
local grind_pattern mem_self_append_singleton => l ++ [x]
local grind_pattern mem_append_left' => x ∈ l₁, l₁ ++ l₂

private theorem not_imp_extract {P Q : Prop} (h : ¬(P → Q)) : P ∧ ¬Q :=
  ⟨Classical.byContradiction fun hp => h fun p => absurd p hp,
   fun q => h fun _ => q⟩

def isPrime (n : Nat) : Id Bool := do
  let mut composite : Bool := false
  for k in [2:n] do
    if n % k = 0 then
      composite := true
  if composite = true then
    return false
  else
    return true

theorem isPrime_spec (n : Nat) (_h : 2 ≤ n) :
    (isPrime n).run = true ↔ ¬ ∃ k : Nat, 1 < k ∧ k < n ∧ n % k = 0 := by
  generalize h : (isPrime n).run = r
  apply Id.of_wp_run_eq h
  vcgen [isPrime] invariants
  | inv1 => fun xs composite => composite = false ↔ (∀ d : Nat, d ∈ xs.prefix → n % d ≠ 0)
  with (try finish)
  case vc2 => sorry
  case vc3 => sorry

end E_isPrime

namespace E_kthElement

def kthElement (arr : Array Int) (k : Nat) : Id Int := do
  return arr[k - 1]!

theorem kthElement_spec (arr : Array Int) (k : Nat)
    (_h1 : arr.size ≥ 1) (_h2 : 1 ≤ k) (_h3 : k ≤ arr.size) :
    (kthElement arr k).run = arr[k - 1]! := by
  generalize h : (kthElement arr k).run = r
  apply Id.of_wp_run_eq h
  vcgen [kthElement]
  with finish

end E_kthElement

namespace E_lastDigit

def lastDigit (n : Nat) : Id Nat := do
  let d := n % 10
  return d

theorem lastDigit_spec (n : Nat) :
    (lastDigit n).run = n % 10 ∧ (lastDigit n).run < 10 := by
  generalize h : (lastDigit n).run = r
  apply Id.of_wp_run_eq h
  vcgen [lastDigit]
  with finish

end E_lastDigit

namespace E_minOfThree

def minOfThree (a b c : Int) : Id Int := do
  let mut m := a
  if b ≤ m then
    m := b
  else
    pure ()
  if c ≤ m then
    m := c
  else
    pure ()
  return m

theorem minOfThree_spec (a b c : Int) :
    (minOfThree a b c).run ≤ a ∧ (minOfThree a b c).run ≤ b ∧
      (minOfThree a b c).run ≤ c ∧
      ((minOfThree a b c).run = a ∨ (minOfThree a b c).run = b ∨
        (minOfThree a b c).run = c) := by
  generalize h : (minOfThree a b c).run = r
  apply Id.of_wp_run_eq h
  vcgen [minOfThree]
  with finish

end E_minOfThree

namespace E_multiply

def multiply (a b : Int) : Id Int := do
  let prod := a * b
  return prod

theorem multiply_spec (a b : Int) : (multiply a b).run = a * b := by
  generalize h : (multiply a b).run = r
  apply Id.of_wp_run_eq h
  vcgen [multiply]
  with finish

end E_multiply

namespace E_myMin

def myMin (a b : Int) : Id Int := do
  if a ≤ b then
    return a
  else
    return b

theorem myMin_spec (a b : Int) :
    (myMin a b).run ≤ a ∧ (myMin a b).run ≤ b ∧
      ((myMin a b).run = a ∨ (myMin a b).run = b) := by
  generalize h : (myMin a b).run = r
  apply Id.of_wp_run_eq h
  vcgen [myMin]
  with finish

end E_myMin

namespace E_removeElement

def removeElement (s : Array Int) (k : Nat) : Id (Array Int) := do
  let mut result := Array.replicate (s.size - 1) (0 : Int)
  let mut i : Nat := 0
  while i < result.size do
    if i < k then
      result := result.set! i (s[i]!)
    else
      result := result.set! i (s[i + 1]!)
    i := i + 1
  return result

theorem removeElement_spec (s : Array Int) (k : Nat) (hk : k < s.size) :
    (removeElement s k).run.size + 1 = s.size ∧
    (∀ (i : Nat), i < (removeElement s k).run.size →
      (if i < k then (removeElement s k).run[i]! = s[i]!
       else (removeElement s k).run[i]! = s[i + 1]!)) := by
  generalize h : (removeElement s k).run = r
  apply Id.of_wp_run_eq h
  vcgen [removeElement] invariants
  | inv1 => fun r => match r with
    | .inl ⟨result, i⟩ => i ≤ result.size ∧ result.size + 1 = s.size ∧
        ∀ (j : Nat), j < i →
          (if j < k then result[j]! = s[j]! else result[j]! = s[j + 1]!)
    | .inr ⟨result, i⟩ => i = result.size ∧ result.size + 1 = s.size ∧
        ∀ (j : Nat), j < result.size →
          (if j < k then result[j]! = s[j]! else result[j]! = s[j + 1]!)
  | inv2 => fun ⟨result, i⟩ => result.size - i
  with finish

end E_removeElement

namespace E_sumAndAverage

@[local grind]
def gaussSumNat (n : Nat) : Nat := n * (n + 1) / 2

def sumAndAverage (n : Nat) : Id (Int × Float) := do
  let sumNat : Nat := gaussSumNat n
  let sumInt : Int := Int.ofNat sumNat
  if n = 0 then
    return (sumInt, 0.0)
  else
    let avg : Float := (Float.ofInt sumInt) / (Float.ofNat n)
    return (sumInt, avg)

theorem sumAndAverage_spec (n : Nat) :
    (sumAndAverage n).run.1 = Int.ofNat (gaussSumNat n) ∧
    (n = 0 → (sumAndAverage n).run.2 = 0.0) ∧
    (n > 0 → (sumAndAverage n).run.2 =
      (Float.ofInt (sumAndAverage n).run.1) / (Float.ofNat n)) := by
  generalize h : (sumAndAverage n).run = r
  apply Id.of_wp_run_eq h
  vcgen [sumAndAverage]
  with finish

end E_sumAndAverage

namespace E_sumOfSquaresOfFirstNOddNumbers

def oddSquaresClosedFormNumerator (n : Nat) : Nat := n * (2 * n - 1) * (2 * n + 1)

def sumOfSquaresOfFirstNOddNumbers (n : Nat) : Id Nat := do
  let num := oddSquaresClosedFormNumerator n
  return num / 3

theorem sumOfSquaresOfFirstNOddNumbers_spec (n : Nat) :
    (sumOfSquaresOfFirstNOddNumbers n).run = oddSquaresClosedFormNumerator n / 3 := by
  generalize h : (sumOfSquaresOfFirstNOddNumbers n).run = r
  apply Id.of_wp_run_eq h
  vcgen [sumOfSquaresOfFirstNOddNumbers]
  with finish

end E_sumOfSquaresOfFirstNOddNumbers

namespace E_swapFirstAndLast

@[local grind]
def lastIdx (a : Array Int) : Nat := a.size - 1

def swapFirstAndLast (a : Array Int) : Id (Array Int) := do
  let n := a.size
  let last := n - 1
  let mut result := a
  if n = 1 then
    return result
  else
    let firstVal := a[0]!
    let lastVal := a[last]!
    result := result.set! 0 lastVal
    result := result.set! last firstVal
    return result

theorem swapFirstAndLast_spec (a : Array Int) (h : 0 < a.size) :
    (swapFirstAndLast a).run.size = a.size ∧
    (∀ (i : Nat), i < a.size →
      ((swapFirstAndLast a).run[i]! =
        if i = 0 then a[lastIdx a]!
        else if i = lastIdx a then a[0]!
        else a[i]!)) := by
  generalize hr : (swapFirstAndLast a).run = r
  apply Id.of_wp_run_eq hr
  vcgen [swapFirstAndLast]
  with finish

end E_swapFirstAndLast

namespace P_findEvenNumbers

@[local grind]
def isEvenInt (x : Int) : Bool :=
  x % 2 = 0

@[local grind]
def Array.Sublist (arr : Array Int) (sub : Array Int) : Prop :=
  ∃ indices : Array Nat,
    indices.size = sub.size ∧
    (∀ i, i < indices.size → indices[i]! < arr.size) ∧
    (∀ i, i < indices.size → sub[i]! = arr[indices[i]!]!) ∧
    (∀ i j, i < j → j < indices.size → indices[i]! < indices[j]!)

@[local grind =]
theorem count_extract_succ [DecidableEq α] [Inhabited α] {a : α} {xs : Array α} {n : Nat}
    (h : n < xs.size) :
    (xs.extract 0 (n + 1)).count a =
      if xs[n]! = a then (xs.extract 0 n).count a + 1 else (xs.extract 0 n).count a := sorry
@[local grind]
theorem Array.extract_size_self {xs : Array α} : xs.extract 0 xs.size = xs := sorry

@[local grind →]
theorem range_split_index {n : Nat} {pref suff : List Nat} {c : Nat}
    (h : [:n].toList = pref ++ c :: suff) : c = pref.length := sorry

@[local grind =]
theorem getElem!_push {α} [Inhabited α] (xs : Array α) (x : α) (i : Nat) :
    (xs.push x)[i]! = if i < xs.size then xs[i]! else if i = xs.size then x else default := sorry
def findEvenNumbers (arr : Array Int) : Id (Array Int) := do
  let mut result : Array Int := #[]
  let mut indices : Array Nat := #[]
  for i in [0:arr.size] do
    let x := arr[i]!
    if isEvenInt x = true then
      result := result.push x
      indices := indices.push i
  return result

theorem findEvenNumbers_spec (arr : Array Int) :
    (Array.Sublist arr (findEvenNumbers arr).run) ∧
    (∀ x, x ∈ (findEvenNumbers arr).run → isEvenInt x = true) ∧
    (∀ x, isEvenInt x = true → (findEvenNumbers arr).run.count x = arr.count x) ∧
    (∀ x, isEvenInt x = false → (findEvenNumbers arr).run.count x = 0) := by
  generalize h : (findEvenNumbers arr).run = r
  apply Id.of_wp_run_eq h
  vcgen [findEvenNumbers] invariants
  | inv1 => fun xs ⟨result, indices⟩ => xs.prefix.length ≤ arr.size ∧
      (∀ x, x ∈ result → isEvenInt x = true) ∧
      (∀ x, isEvenInt x = false → result.count x = 0) ∧
      (∀ x, isEvenInt x = true → result.count x = (arr.extract 0 xs.prefix.length).count x) ∧
      indices.size = result.size ∧
      (∀ k, k < indices.size → indices[k]! < xs.prefix.length) ∧
      (∀ k, k < indices.size → indices[k]! < arr.size) ∧
      (∀ k, k < indices.size → result[k]! = arr[indices[k]!]!) ∧
      (∀ k j, k < j → j < indices.size → indices[k]! < indices[j]!)
  case vc3 => sorry
  case vc4 => sorry
  all_goals grind [Array.count_push, getElem!_push, count_extract_succ, Array.extract_size_self, -Array.extract_eq_pop, -Nat.min_def]

end P_findEvenNumbers

namespace P_findMajorityElement

@[local grind]
def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

@[local grind]
def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x

attribute [grind] List.take_succ_eq_append_getElem

@[local grind →]
theorem range_split_index {m : Nat} {pref suff : List Nat} {c : Nat}
    (h : [:m].toList = pref ++ c :: suff) : c = pref.length := sorry
attribute [grind] List.take_length

@[local grind →]
theorem mem_getElem! (lst : List Int) (w : Int) (hw : w ∈ lst) :
    ∃ k, k < lst.length ∧ lst[k]! = w := sorry
def findMajorityElement (lst : List Int) : Id Int := do
  let n := lst.length
  let threshold := n / 2
  let mut found := false
  let mut candidate : Int := -1
  for i in [0:n] do
    let elem := lst[i]!
    let mut count := 0
    for j in [0:n] do
      if lst[j]! = elem then
        count := count + 1
    if count > threshold then
      found := true
      candidate := elem
  if found then
    return candidate
  else
    return -1

theorem findMajorityElement_spec (lst : List Int) :
    (hasMajorityElement lst → ((findMajorityElement lst).run ∈ lst ∧
        isMajorityElement lst (findMajorityElement lst).run)) ∧
    (¬hasMajorityElement lst → (findMajorityElement lst).run = -1) := by
  generalize h : (findMajorityElement lst).run = r
  apply Id.of_wp_run_eq h
  vcgen [findMajorityElement] invariants
  | inv1 => fun xs ⟨found, candidate⟩ => (found = true → candidate ∈ lst ∧ isMajorityElement lst candidate) ∧
      (found = false → ∀ k : Nat, k < xs.prefix.length → ¬isMajorityElement lst lst[k]!)
  | inv2 pref cur suff hsplit b hinv => fun ys count => count = (lst.take ys.prefix.length).count lst[cur]!
  case vc7 => sorry
  case vc8 => sorry
  all_goals grind [List.take_length, List.length_range', List.take_succ_eq_append_getElem, -Array.extract_eq_pop, -Nat.min_def]

end P_findMajorityElement

namespace P_ifPowerOfFour

@[local grind]
def isPowerOfFour (n : Nat) : Prop :=
  ∃ x : Nat, 4 ^ x = n

@[local grind]
theorem isPowerOfFour_div_four {current : Nat} (hc : current % 4 = 0)
    (h : isPowerOfFour current) : isPowerOfFour (current / 4) := sorry

@[local grind]
theorem isPowerOfFour_mul_four {current : Nat} (h : isPowerOfFour current) :
    isPowerOfFour (current * 4) := sorry
@[local grind]
theorem isPowerOfFour_one : isPowerOfFour 1 := sorry

@[local grind]
theorem pow_four_gt_one_iff {e : Nat} : 1 < 4 ^ e ↔ 1 ≤ e := sorry
@[local grind]
theorem pow_four_div_four {e : Nat} (he : 1 ≤ e) : 4 ^ e / 4 = 4 ^ (e - 1) := sorry
@[local grind]
theorem pow_four_mod_four {e : Nat} : 4 ^ e % 4 = 0 ↔ 1 ≤ e := sorry
@[local grind]
theorem pow_four_eq_one {e : Nat} : 4 ^ e = 1 ↔ e = 0 := sorry

theorem isPowerOfFour_iff_div_four {current : Nat} (hc : current % 4 = 0) :
    isPowerOfFour current ↔ isPowerOfFour (current / 4) := sorry
def ifPowerOfFour (n : Nat) : Id Bool := do
  if n = 0 then
    return false
  else
    let mut current := n
    for _ in [0:n] do
      if current > 1 ∧ current % 4 = 0 then
        current := current / 4
    return current = 1

theorem ifPowerOfFour_spec (n : Nat) :
    ((ifPowerOfFour n).run = true ↔ isPowerOfFour n) := by
  generalize h : (ifPowerOfFour n).run = r
  apply Id.of_wp_run_eq h
  vcgen [ifPowerOfFour] invariants
  | inv1 => fun xs current => current > 0 ∧ (isPowerOfFour n ↔ isPowerOfFour current) ∧
      (isPowerOfFour n → ∃ e, current = 4 ^ e ∧ (e = 0 ∨ 4 ^ (e + xs.prefix.length) = n))
  case vc4 => sorry
  all_goals grind [isPowerOfFour_iff_div_four, Nat.lt_pow_self, Nat.pow_succ, -Array.extract_eq_pop, -Nat.min_def]

end P_ifPowerOfFour

namespace P_isSorted

@[local grind]
def AdjacentSorted (a : Array Int) : Prop :=
  ∀ (i : Nat), i + 1 < a.size → a[i]! ≤ a[i + 1]!

@[local grind]
def GloballySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!

@[local grind]
theorem adjacent_implies_global (a : Array Int) (hadj : AdjacentSorted a) :
    GloballySorted a := sorry
def isSorted (a : Array Int) : Id Bool := do
  let mut sorted := true
  for i in [0:a.size] do
    if i + 1 < a.size then
      if a[i]! > a[i + 1]! then
        sorted := false
  return sorted

theorem isSorted_spec (a : Array Int) :
    ((isSorted a).run = true ↔ AdjacentSorted a) ∧
    ((isSorted a).run = true → GloballySorted a) ∧
    ((isSorted a).run = false ↔ ¬ AdjacentSorted a) := by
  generalize h : (isSorted a).run = r
  apply Id.of_wp_run_eq h
  vcgen [isSorted] invariants
  | inv1 => fun xs sorted => (sorted = true → ∀ k : Nat, k ∈ xs.prefix → k + 1 < a.size → a[k]! ≤ a[k + 1]!) ∧
      (sorted = false → ∃ k : Nat, k + 1 < a.size ∧ a[k]! > a[k + 1]!)
  with finish

end P_isSorted

namespace P_isSublist

@[local grind]
def isContiguousSublist (sub : List Int) (main : List Int) : Prop :=
  sub <:+: main

attribute [grind] List.singleton_append List.append_assoc List.take_prefix
  List.IsPrefix.isInfix List.take_left

@[local grind]
theorem infix_drop_one (sub rest : List Int)
    (hinf : sub <:+: rest) (hne : sub ≠ rest.take sub.length) (_hsub : sub ≠ []) :
    sub <:+: rest.drop 1 := sorry
def isSublist (sub : List Int) (main : List Int) : Id Bool := do
  if sub = [] then
    return true
  else
    let mut rest := main
    let mut found := false
    for _ in [0:main.length] do
      if rest ≠ [] ∧ found = false then
        if sub.length ≤ rest.length then
          if sub = rest.take sub.length then
            found := true
          else
            rest := rest.drop 1
        else
          rest := rest.drop 1
    return found

theorem isSublist_spec (sub : List Int) (main : List Int) :
    ((isSublist sub main).run = true ↔ isContiguousSublist sub main) := by
  generalize h : (isSublist sub main).run = r
  apply Id.of_wp_run_eq h
  vcgen [isSublist] invariants
  | inv1 => fun xs ⟨rest, found⟩ => rest <:+: main ∧
      (found = true → sub <:+: main) ∧
      (sub <:+: main → found = true ∨ sub <:+: rest) ∧
      (found = false → rest.length + xs.prefix.length ≤ main.length)
  with finish [List.eq_nil_of_infix_nil, List.length_drop, List.length_range',
    List.length_eq_zero_iff]

end P_isSublist

namespace P_mergeSorted

@[local grind]
def isSorted (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

@[local grind]
theorem isSorted_le (arr : Array Nat) (i : Nat) :
    isSorted arr → i + 1 < arr.size → arr[i]! ≤ arr[i + 1]! := sorry

@[local grind =]
theorem count_extract_succ [DecidableEq α] [Inhabited α] {a : α} {xs : Array α} {n : Nat}
    (h : n < xs.size) :
    (xs.extract 0 (n + 1)).count a =
      if xs[n]! = a then (xs.extract 0 n).count a + 1 else (xs.extract 0 n).count a := sorry
@[local grind]
theorem Array.extract_size_self {xs : Array α} : xs.extract 0 xs.size = xs := sorry

@[local grind →]
theorem range_split_index {n : Nat} {pref suff : List Nat} {c : Nat}
    (h : [:n].toList = pref ++ c :: suff) : c = pref.length := sorry

@[local grind →]
theorem range_split_lt {n : Nat} {pref suff : List Nat} {c : Nat}
    (h : [:n].toList = pref ++ c :: suff) : pref.length < n := sorry
@[local grind =]
theorem getElem!_push_lt {α} [Inhabited α] (xs : Array α) (x : α) {i : Nat} (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := sorry
@[local grind =]
theorem getElem!_push_eq {α} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := sorry

@[local grind]
theorem isSorted_push' (result : Array Nat) (v : Nat)
    (hs : isSorted result)
    (hall : ∀ p, p < result.size → result[p]! ≤ v) :
    isSorted (result.push v) := sorry

@[local grind]
theorem push_all_le (result : Array Nat) (v w : Nat)
    (hall : ∀ p, p < result.size → result[p]! ≤ w) (hvw : v ≤ w) :
    ∀ p, p < (result.push v).size → (result.push v)[p]! ≤ w := sorry
def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Id (Array Nat) := do
  let mut result : Array Nat := #[]
  let mut i : Nat := 0
  let mut j : Nat := 0
  for _ in [0:a1.size + a2.size] do
    if i >= a1.size then
      result := result.push a2[j]!
      j := j + 1
    else
      if j >= a2.size then
        result := result.push a1[i]!
        i := i + 1
      else
        if a1[i]! <= a2[j]! then
          result := result.push a1[i]!
          i := i + 1
        else
          result := result.push a2[j]!
          j := j + 1
  return result

theorem mergeSorted_spec (a1 : Array Nat) (a2 : Array Nat)
    (h1 : isSorted a1) (h2 : isSorted a2) :
    ((mergeSorted a1 a2).run.size = a1.size + a2.size) ∧
    (isSorted (mergeSorted a1 a2).run) ∧
    (∀ v : Nat, (mergeSorted a1 a2).run.count v = a1.count v + a2.count v) := by
  generalize h : (mergeSorted a1 a2).run = r
  apply Id.of_wp_run_eq h
  vcgen [mergeSorted] invariants
  | inv1 => fun xs ⟨result, i, j⟩ => i ≤ a1.size ∧ j ≤ a2.size ∧
      result.size = i + j ∧ result.size = xs.prefix.length ∧
      isSorted result ∧
      (∀ v : Nat, result.count v = (a1.extract 0 i).count v + (a2.extract 0 j).count v) ∧
      (i < a1.size → ∀ p, p < result.size → result[p]! ≤ a1[i]!) ∧
      (j < a2.size → ∀ p, p < result.size → result[p]! ≤ a2[j]!)
  case vc3 => sorry
  case vc4 => sorry
  case vc5 => sorry
  case vc6 => sorry
  all_goals grind [isSorted_le, isSorted_push', push_all_le, count_extract_succ, Array.extract_size_self, Array.count_push, getElem!_push_lt, getElem!_push_eq, -Array.extract_eq_pop, -Nat.min_def]

end P_mergeSorted

namespace I_differenceMinMax

@[local grind] def InArray (a : Array Int) (v : Int) : Prop :=
  ∃ (i : Nat), i < a.size ∧ a[i]! = v

@[local grind] def IsMinOfArray (a : Array Int) (mn : Int) : Prop :=
  InArray a mn ∧ (∀ (i : Nat), i < a.size → mn ≤ a[i]!)

@[local grind] def IsMaxOfArray (a : Array Int) (mx : Int) : Prop :=
  InArray a mx ∧ (∀ (i : Nat), i < a.size → a[i]! ≤ mx)

def differenceMinMax (a : Array Int) : Id Int := do
  let mut mn := a[0]!
  let mut mx := a[0]!
  let mut i : Nat := 1
  while i < a.size do
    let v := a[i]!
    if v < mn then
      mn := v
    else
      pure ()
    if v > mx then
      mx := v
    else
      pure ()
    i := i + 1
  return (mx - mn)

theorem differenceMinMax_spec (a : Array Int) :
    ⦃ a.size ≠ 0 ⦄
    differenceMinMax a
    ⦃ fun r => ∃ (mn : Int) (mx : Int),
      IsMinOfArray a mn ∧ IsMaxOfArray a mx ∧ r = mx - mn ⦄ := by
  vcgen [differenceMinMax] invariants
  | inv1 => fun r => match r with
    | .inl ⟨mn, mx, i⟩ => 1 ≤ i ∧ i ≤ a.size ∧
        (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
    | .inr ⟨mn, mx, i⟩ => i = a.size ∧
        (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
  | inv2 => fun ⟨_mn, _mx, i⟩ => a.size - i
  with (try finish)
  case vc2 => sorry

end I_differenceMinMax

namespace I_findMajorityElement

@[local grind]
def isMajorityElement (lst : List Int) (x : Int) : Prop :=
  lst.count x > lst.length / 2

@[local grind]
def hasMajorityElement (lst : List Int) : Prop :=
  ∃ x, x ∈ lst ∧ isMajorityElement lst x

attribute [grind] List.take_succ_eq_append_getElem

@[local grind →]
theorem range_split_index {m : Nat} {pref suff : List Nat} {c : Nat}
    (h : [:m].toList = pref ++ c :: suff) : c = pref.length := sorry
attribute [grind] List.take_length

@[local grind →]
theorem mem_getElem! (lst : List Int) (w : Int) (hw : w ∈ lst) :
    ∃ k, k < lst.length ∧ lst[k]! = w := sorry
def findMajorityElement (lst : List Int) : Id Int := do
  let n := lst.length
  let threshold := n / 2
  let mut found := false
  let mut candidate : Int := -1
  for i in [0:n] do
    let elem := lst[i]!
    let mut count := 0
    for j in [0:n] do
      if lst[j]! = elem then
        count := count + 1
    if count > threshold then
      found := true
      candidate := elem
  if found then
    return candidate
  else
    return -1

theorem findMajorityElement_spec (lst : List Int) :
    ⦃ True ⦄
    findMajorityElement lst
    ⦃ fun r => (hasMajorityElement lst → r ∈ lst ∧ isMajorityElement lst r) ∧
      (¬hasMajorityElement lst → r = -1) ⦄ := by
  vcgen [findMajorityElement] invariants
  | inv1 => fun xs ⟨found, candidate⟩ => (found = true → candidate ∈ lst ∧ isMajorityElement lst candidate) ∧
      (found = false → ∀ k : Nat, k < xs.prefix.length → ¬isMajorityElement lst lst[k]!)
  | inv2 _ cur _ _ _ _ => fun ys count => count = (lst.take ys.prefix.length).count lst[cur]!
  case vc7 => sorry
  case vc8 => sorry
  all_goals grind [List.take_length, List.length_range', List.take_succ_eq_append_getElem, List.count_append, List.count_singleton, -Array.extract_eq_pop, -Nat.min_def]

end I_findMajorityElement
