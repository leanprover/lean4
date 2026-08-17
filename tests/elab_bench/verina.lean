import Std.WP
import Std.Tactic.Do

/-!
Benchmark for `vcgen`/`grind` over the Verina verification corpus. Each program states its own
contract: the `requires`/`ensures` clauses of the definition give the Hoare triple `f.spec`, and
the `invariant`/`decreasing` clauses of its loops give `vcgen` what it needs to prove that triple.
Supporting lemmas and the verification-condition steps of a `where finally | spec` section are
`sorry`'d, so the elaboration cost measured here is the `vcgen` decomposition and `grind` search
itself. Each fixture lives in its own namespace with `@[local grind]` lemmas.
-/

open Std.WP Lean.Order
set_option mvcgen.warning false
set_option warn.sorry false
set_option maxHeartbeats 1000000

namespace E_containsConsecutiveNumbers

@[local grind] def HasConsecutivePair (a : Array Int) : Prop :=
  ∃ i : Nat, i + 1 < a.size ∧ a[i]! + 1 = a[i + 1]!

def containsConsecutiveNumbers (a : Array Int) : Id Bool
    ensures r => r = true ↔ HasConsecutivePair a := do
  if a.size < 2 then
    return false
  else
    let mut i : Nat := 0
    let mut found : Bool := false
    while i + 1 < a.size ∧ found = false
        invariant exit =>
          (if exit then i + 1 ≥ a.size ∨ found = true else i + 1 ≤ a.size) ∧
          (found = false → ∀ j : Nat, j < i → a[j]! + 1 ≠ a[j + 1]!) ∧
          (found = true → HasConsecutivePair a)
        decreasing (a.size + 1 - i) * 2 + (if found = false then 1 else 0)
      do
      if a[i]! + 1 = a[i + 1]! then
        found := true
      else
        i := i + 1
    return found

end E_containsConsecutiveNumbers

namespace E_countSumDivisibleBy

def digitSum (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + digitSum (n / 10)

@[local grind] def divisesDigitSum (d k : Nat) : Bool := decide (d ∣ digitSum k)

def countSumDivisibleBy (n : Nat) (d : Nat) : Id Nat
    requires d > 0
    ensures r => r = ((List.range n).countP (divisesDigitSum d)) := do
  let mut count := 0
  let mut k := 0
  while k < n
      invariant exit =>
        (if exit then k = n else k ≤ n) ∧
        count = ((List.range k).countP (divisesDigitSum d))
      decreasing n + 1 - k
    do
    let sum := digitSum k
    if sum % d = 0 then
      count := count + 1
    k := k + 1
  return count
where finally
  | spec => all_goals grind [List.range_succ, Nat.dvd_iff_mod_eq_zero, divisesDigitSum]

end E_countSumDivisibleBy

namespace E_cubeElements

@[local grind] def intCube (x : Int) : Int := x * x * x

def cubeElements (a : Array Int) : Id (Array Int)
    ensures r => r.size = a.size ∧ (∀ (i : Nat), i < a.size → r[i]! = intCube (a[i]!)) := do
  let mut result := Array.replicate a.size (0 : Int)
  let mut i : Nat := 0
  while i < a.size
      invariant exit =>
        (if exit then i = a.size else i ≤ a.size) ∧ result.size = a.size ∧
        ∀ k, k < i → result[k]! = intCube (a[k]!)
      decreasing a.size + 1 - i
    do
    let x := a[i]!
    result := result.set! i (intCube x)
    i := i + 1
  return result

end E_cubeElements

namespace E_cubeSurfaceArea

def cubeSurfaceArea (size : Nat) : Id Nat
    ensures r => r = 6 * (size ^ 2) := do
  let area := 6 * (size ^ 2)
  return area

end E_cubeSurfaceArea

namespace E_differenceMinMax

@[local grind] def InArray (a : Array Int) (v : Int) : Prop := ∃ (i : Nat), i < a.size ∧ a[i]! = v
@[local grind] def IsMinOfArray (a : Array Int) (mn : Int) : Prop := InArray a mn ∧ (∀ (i : Nat), i < a.size → mn ≤ a[i]!)
@[local grind] def IsMaxOfArray (a : Array Int) (mx : Int) : Prop := InArray a mx ∧ (∀ (i : Nat), i < a.size → a[i]! ≤ mx)

def differenceMinMax (a : Array Int) : Id Int
    requires a.size ≠ 0
    ensures r => ∃ (mn : Int) (mx : Int),
      IsMinOfArray a mn ∧ IsMaxOfArray a mx ∧ r = mx - mn := do
  let mut mn := a[0]!
  let mut mx := a[0]!
  let mut i : Nat := 1
  while i < a.size
      invariant exit =>
        (if exit then i = a.size else 1 ≤ i ∧ i ≤ a.size) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mn) ∧ (∀ j : Nat, j < i → mn ≤ a[j]!) ∧
        (∃ j : Nat, j < i ∧ a[j]! = mx) ∧ (∀ j : Nat, j < i → a[j]! ≤ mx)
      decreasing a.size - i
    do
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
where finally
  | spec => case vc2 => sorry

end E_differenceMinMax

namespace E_elementWiseModulo

@[local grind] def allNonzero (b : Array Int) : Prop :=
  ∀ (i : Nat), i < b.size → b[i]! ≠ 0

def elementWiseModulo (a : Array Int) (b : Array Int) : Id (Array Int)
    requires a.size = b.size ∧ allNonzero b
    ensures r => r.size = a.size ∧ (∀ (i : Nat), i < a.size → r[i]! = a[i]! % b[i]!) := do
  let mut result := Array.replicate a.size (0 : Int)
  let mut i : Nat := 0
  while i < a.size
      invariant exit =>
        (if exit then i = a.size else i ≤ a.size) ∧ result.size = a.size ∧
        ∀ k, k < i → result[k]! = a[k]! % b[k]!
      decreasing a.size + 1 - i
    do
    result := result.set! i (a[i]! % b[i]!)
    i := i + 1
  return result

end E_elementWiseModulo

namespace E_findSmallest

def findSmallest (s : Array Nat) : Id (Option Nat)
    ensures r => match r with
      | none => s.size = 0
      | some min =>
          s.size > 0 ∧
          (∃ i, i < s.size ∧ s[i]! = min) ∧
          (∀ j, j < s.size → min ≤ s[j]!) := do
  if s.size = 0 then
    return none
  else
    let mut minIndex := 0
    for i in [1:s.size]
        invariant pref _ => minIndex < s.size ∧ s[minIndex]! ≤ s[0]! ∧
          ∀ j, j ∈ pref → s[minIndex]! ≤ s[j]!
      do
      if s[i]! < s[minIndex]! then
        minIndex := i
    return some s[minIndex]!

end E_findSmallest

namespace E_hasOppositeSign

def hasOppositeSign (a : Int) (b : Int) : Id Bool
    ensures r => r = true ↔ ((a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0)) := do
  if a > 0 ∧ b < 0 then
    return true
  else if a < 0 ∧ b > 0 then
    return true
  else
    return false

end E_hasOppositeSign

namespace E_isDivisibleBy11

def isDivisibleBy11 (n : Int) : Id Bool
    ensures r => r = true ↔ (11 : Int) ∣ n := do
  let remainder := n % 11
  if remainder = 0 then
    return true
  else
    return false

end E_isDivisibleBy11

namespace E_isEven

@[local grind] def IntIsEven (n : Int) : Prop := n % 2 = 0

def isEven (n : Int) : Id Bool
    ensures r => r = true ↔ IntIsEven n := do
  if n % 2 = 0 then return true else return false

end E_isEven

namespace E_isGreater

def isGreater (n : Int) (a : Array Int) : Id Bool
    requires a.size > 0
    ensures r => r = true ↔ (∀ i : Nat, i < a.size → a[i]! < n) := do
  let mut ok := true
  for i in [0:a.size]
      invariant pref _ => ok = true ↔ (∀ j : Nat, j ∈ pref → a[j]! < n)
    do
    if a[i]! < n then
      ok := ok
    else
      ok := false
  return ok

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

def isPrime (n : Nat) : Id Bool
    requires 2 ≤ n
    ensures r => r = true ↔ ¬ ∃ k : Nat, 1 < k ∧ k < n ∧ n % k = 0 := do
  let mut composite : Bool := false
  for k in [2:n]
      invariant pref _ => composite = false ↔ (∀ d : Nat, d ∈ pref → n % d ≠ 0)
    do
    if n % k = 0 then
      composite := true
  if composite = true then
    return false
  else
    return true
where finally
  | spec =>
    case vc2 => sorry
    case vc3 => sorry

end E_isPrime

namespace E_kthElement

def kthElement (arr : Array Int) (k : Nat) : Id Int
    requires arr.size ≥ 1 ∧ 1 ≤ k ∧ k ≤ arr.size
    ensures r => r = arr[k - 1]! := do
  return arr[k - 1]!

end E_kthElement

namespace E_lastDigit

def lastDigit (n : Nat) : Id Nat
    ensures r => r = n % 10 ∧ r < 10 := do
  let d := n % 10
  return d

end E_lastDigit

namespace E_minOfThree

def minOfThree (a b c : Int) : Id Int
    ensures r => r ≤ a ∧ r ≤ b ∧ r ≤ c ∧ (r = a ∨ r = b ∨ r = c) := do
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

end E_minOfThree

namespace E_multiply

def multiply (a b : Int) : Id Int
    ensures r => r = a * b := do
  let prod := a * b
  return prod

end E_multiply

namespace E_myMin

def myMin (a b : Int) : Id Int
    ensures r => r ≤ a ∧ r ≤ b ∧ (r = a ∨ r = b) := do
  if a ≤ b then
    return a
  else
    return b

end E_myMin

namespace E_removeElement

def removeElement (s : Array Int) (k : Nat) : Id (Array Int)
    requires k < s.size
    ensures r => r.size + 1 = s.size ∧
      (∀ (i : Nat), i < r.size →
        (if i < k then r[i]! = s[i]! else r[i]! = s[i + 1]!)) := do
  let mut result := Array.replicate (s.size - 1) (0 : Int)
  let mut i : Nat := 0
  while i < result.size
      invariant exit =>
        (if exit then i = result.size else i ≤ result.size) ∧ result.size + 1 = s.size ∧
        ∀ (j : Nat), j < i → (if j < k then result[j]! = s[j]! else result[j]! = s[j + 1]!)
      decreasing result.size - i
    do
    if i < k then
      result := result.set! i (s[i]!)
    else
      result := result.set! i (s[i + 1]!)
    i := i + 1
  return result

end E_removeElement

namespace E_sumAndAverage

@[local grind]
def gaussSumNat (n : Nat) : Nat := n * (n + 1) / 2

def sumAndAverage (n : Nat) : Id (Int × Float)
    ensures r => r.1 = Int.ofNat (gaussSumNat n) ∧
      (n = 0 → r.2 = 0.0) ∧
      (n > 0 → r.2 = (Float.ofInt r.1) / (Float.ofNat n)) := do
  let sumNat : Nat := gaussSumNat n
  let sumInt : Int := Int.ofNat sumNat
  if n = 0 then
    return (sumInt, 0.0)
  else
    let avg : Float := (Float.ofInt sumInt) / (Float.ofNat n)
    return (sumInt, avg)

end E_sumAndAverage

namespace E_sumOfSquaresOfFirstNOddNumbers

def oddSquaresClosedFormNumerator (n : Nat) : Nat := n * (2 * n - 1) * (2 * n + 1)

def sumOfSquaresOfFirstNOddNumbers (n : Nat) : Id Nat
    ensures r => r = oddSquaresClosedFormNumerator n / 3 := do
  let num := oddSquaresClosedFormNumerator n
  return num / 3

end E_sumOfSquaresOfFirstNOddNumbers

namespace E_swapFirstAndLast

@[local grind]
def lastIdx (a : Array Int) : Nat := a.size - 1

def swapFirstAndLast (a : Array Int) : Id (Array Int)
    requires 0 < a.size
    ensures r => r.size = a.size ∧
      (∀ (i : Nat), i < a.size →
        (r[i]! =
          if i = 0 then a[lastIdx a]!
          else if i = lastIdx a then a[0]!
          else a[i]!)) := do
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

end E_swapFirstAndLast

namespace P_findEvenNumbers

@[local grind]
def isEvenInt (x : Int) : Bool :=
  x % 2 = 0

/-- `idx` witnesses that `sub` is a subsequence of `arr`: it lists, in increasing order, the
positions of `arr` that `sub` collects. The loop below maintains this witness, so it is named
rather than left under the existential of `Array.Sublist`. It carries no `grind` attribute: the
conditions it collects are reached through `IsSublistWitness.push`, not by unfolding. -/
def IsSublistWitness (arr : Array Int) (sub : Array Int) (idx : Array Nat) : Prop :=
  idx.size = sub.size ∧
  (∀ i, i < idx.size → idx[i]! < arr.size) ∧
  (∀ i, i < idx.size → sub[i]! = arr[idx[i]!]!) ∧
  (∀ i j, i < j → j < idx.size → idx[i]! < idx[j]!)

/-- The empty witness. -/
@[local grind]
theorem IsSublistWitness.empty (arr : Array Int) : IsSublistWitness arr #[] #[] := sorry

/-- Extending the witness by a position past every position it already holds. -/
@[local grind]
theorem IsSublistWitness.push {arr sub : Array Int} {idx : Array Nat} {k : Nat}
    (h : IsSublistWitness arr sub idx) (hk : k < arr.size)
    (hmax : ∀ i, i < idx.size → idx[i]! < k) :
    IsSublistWitness arr (sub.push arr[k]!) (idx.push k) := sorry

@[local grind]
def Array.Sublist (arr : Array Int) (sub : Array Int) : Prop :=
  ∃ idx, IsSublistWitness arr sub idx

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

def findEvenNumbers (arr : Array Int) : Id (Array Int)
    ensures r => (Array.Sublist arr r) ∧
      (∀ x, x ∈ r → isEvenInt x = true) ∧
      (∀ x, isEvenInt x = true → r.count x = arr.count x) ∧
      (∀ x, isEvenInt x = false → r.count x = 0) := do
  let mut result : Array Int := #[]
  let mut indices : Array Nat := #[]
  for i in [0:arr.size]
      invariant pref _ => pref.length ≤ arr.size ∧
        (∀ x, x ∈ result → isEvenInt x = true) ∧
        (∀ x, isEvenInt x = false → result.count x = 0) ∧
        (∀ x, isEvenInt x = true → result.count x = (arr.extract 0 pref.length).count x) ∧
        IsSublistWitness arr result indices ∧
        (∀ k, k < indices.size → indices[k]! < pref.length)
    do
    let x := arr[i]!
    if isEvenInt x = true then
      result := result.push x
      indices := indices.push i
  return result
where finally
  | spec =>
    case vc3 => sorry
    all_goals grind [Array.count_push, getElem!_push, count_extract_succ,
      Array.extract_size_self, -Array.extract_eq_pop, -Nat.min_def]

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

def findMajorityElement (lst : List Int) : Id Int
    ensures r => (hasMajorityElement lst → r ∈ lst ∧ isMajorityElement lst r) ∧
      (¬hasMajorityElement lst → r = -1) := do
  let n := lst.length
  let threshold := n / 2
  let mut found := false
  let mut candidate : Int := -1
  for i in [0:n]
      invariant ipref _ =>
        (found = true → candidate ∈ lst ∧ isMajorityElement lst candidate) ∧
        (found = false → ∀ k : Nat, k < ipref.length → ¬isMajorityElement lst lst[k]!)
    do
    let elem := lst[i]!
    let mut count := 0
    for j in [0:n]
        invariant jpref _ => count = (lst.take jpref.length).count lst[i]!
      do
      if lst[j]! = elem then
        count := count + 1
    if count > threshold then
      found := true
      candidate := elem
  if found then
    return candidate
  else
    return -1

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

def ifPowerOfFour (n : Nat) : Id Bool
    ensures r => (r = true ↔ isPowerOfFour n) := do
  if n = 0 then
    return false
  else
    let mut current := n
    for _ in [0:n]
        invariant pref _ => current > 0 ∧ (isPowerOfFour n ↔ isPowerOfFour current) ∧
          (isPowerOfFour n → ∃ e, current = 4 ^ e ∧ (e = 0 ∨ 4 ^ (e + pref.length) = n))
      do
      if current > 1 ∧ current % 4 = 0 then
        current := current / 4
    return current = 1
where finally
  | spec =>
    case vc4 => sorry
    all_goals grind [isPowerOfFour_iff_div_four, Nat.lt_pow_self, Nat.pow_succ,
      -Array.extract_eq_pop, -Nat.min_def]

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

def isSorted (a : Array Int) : Id Bool
    ensures r => (r = true ↔ AdjacentSorted a) ∧
      (r = true → GloballySorted a) ∧
      (r = false ↔ ¬ AdjacentSorted a) := do
  let mut sorted := true
  for i in [0:a.size]
      invariant pref _ =>
        (sorted = true → ∀ k : Nat, k ∈ pref → k + 1 < a.size → a[k]! ≤ a[k + 1]!) ∧
        (sorted = false → ∃ k : Nat, k + 1 < a.size ∧ a[k]! > a[k + 1]!)
    do
    if i + 1 < a.size then
      if a[i]! > a[i + 1]! then
        sorted := false
  return sorted

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

def isSublist (sub : List Int) (main : List Int) : Id Bool
    ensures r => (r = true ↔ isContiguousSublist sub main) := do
  if sub = [] then
    return true
  else
    let mut rest := main
    let mut found := false
    for _ in [0:main.length]
        invariant pref _ => rest <:+: main ∧
          (found = true → sub <:+: main) ∧
          (sub <:+: main → found = true ∨ sub <:+: rest) ∧
          (found = false → rest.length + pref.length ≤ main.length)
      do
      if rest ≠ [] ∧ found = false then
        if sub.length ≤ rest.length then
          if sub = rest.take sub.length then
            found := true
          else
            rest := rest.drop 1
        else
          rest := rest.drop 1
    return found
where finally
  | spec =>
    all_goals grind [List.eq_nil_of_infix_nil, List.length_drop, List.length_range',
      List.length_eq_zero_iff]

end P_isSublist

namespace P_mergeSorted

/-- Sortedness carries no `grind` attribute: it is reached through the lemmas below rather than by
unfolding, which would make every pair of array reads a candidate instantiation. -/
def isSorted (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

/-- Every element of `xs` is at most `v`. Named for the same reason as `isSorted`. -/
def AllLE (xs : Array Nat) (v : Nat) : Prop :=
  ∀ p, p < xs.size → xs[p]! ≤ v

@[local grind]
theorem isSorted_empty : isSorted #[] := sorry

@[local grind]
theorem AllLE_empty (v : Nat) : AllLE #[] v := sorry

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
    (hs : isSorted result) (hall : AllLE result v) :
    isSorted (result.push v) := sorry

@[local grind]
theorem push_all_le (result : Array Nat) (v w : Nat)
    (hall : AllLE result w) (hvw : v ≤ w) :
    AllLE (result.push v) w := sorry

def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Id (Array Nat)
    requires isSorted a1 ∧ isSorted a2
    ensures r => (r.size = a1.size + a2.size) ∧
      (isSorted r) ∧
      (∀ v : Nat, r.count v = a1.count v + a2.count v) := do
  let mut result : Array Nat := #[]
  let mut i : Nat := 0
  let mut j : Nat := 0
  for _ in [0:a1.size + a2.size]
      invariant pref _ => i ≤ a1.size ∧ j ≤ a2.size ∧
        result.size = i + j ∧ result.size = pref.length ∧
        isSorted result ∧
        (∀ v : Nat, result.count v = (a1.extract 0 i).count v + (a2.extract 0 j).count v) ∧
        (i < a1.size → AllLE result a1[i]!) ∧
        (j < a2.size → AllLE result a2[j]!)
    do
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
where finally
  | spec =>
    case vc3 => sorry
    case vc4 => sorry
    case vc5 => sorry
    case vc6 => sorry
    all_goals grind [isSorted_le, isSorted_push', push_all_le, count_extract_succ,
      Array.extract_size_self, Array.count_push, getElem!_push_lt, getElem!_push_eq,
      -Array.extract_eq_pop, -Nat.min_def]

end P_mergeSorted
