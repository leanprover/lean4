module

import all Init.Data.String.Pattern.Memcmp

/-!
Checks that the `memcmp`-based runtime implementations of `memcmpStr`, `memcmpStrLt` and
`memcmpStrCompare` agree with their Lean definitions, with the byte-level specifications in
`memcmpStr_eq_true_iff`, `memcmpStrLt_eq_true_iff` and `memcmpStrCompare_eq_compare`, and with an
independent reference implementation, and that `memcmpSlice`, `memcmpSliceLt` and
`memcmpSliceCompare` agree with them on slices that do not start at the beginning of their
underlying strings. The inputs include bytes on both sides of the boundary between `0x7f` and
`0x80`, ranges that start or end in the middle of a UTF-8 character, and long ranges that differ at
word and vector boundaries.
-/

open String.Slice.Pattern.Internal

structure Results where
  eq : Bool
  lt : Bool
  cmp : Ordering
deriving BEq, Repr

abbrev MemcmpFn (α : Type) :=
  (lhs rhs : String) → (lstart rstart : String.Pos.Raw) → (len : Nat) →
    lstart.increaseBy len ≤ lhs.rawEndPos → rstart.increaseBy len ≤ rhs.rawEndPos → α

/-- Calls the functions directly, which compiles to calls into the runtime. -/
@[noinline] def viaRuntime : MemcmpFn Results := fun lhs rhs lstart rstart len h₁ h₂ =>
  { eq := memcmpStr lhs rhs lstart rstart len h₁ h₂
    lt := memcmpStrLt lhs rhs lstart rstart len h₁ h₂
    cmp := memcmpStrCompare lhs rhs lstart rstart len h₁ h₂ }

/-- Goes through closures, which exercises the boxed entry points of the runtime. -/
@[noinline, nospecialize] def viaClosures (eq lt : MemcmpFn Bool) (cmp : MemcmpFn Ordering) :
    MemcmpFn Results := fun lhs rhs lstart rstart len h₁ h₂ =>
  { eq := eq lhs rhs lstart rstart len h₁ h₂
    lt := lt lhs rhs lstart rstart len h₁ h₂
    cmp := cmp lhs rhs lstart rstart len h₁ h₂ }

/-- Runs the loop from the Lean definition of `memcmpStrCompare`. -/
@[noinline] def viaModel : MemcmpFn Results := fun lhs rhs lstart rstart len h₁ h₂ =>
  let cmp := memcmpStrCompare.go lhs rhs lstart rstart len h₁ h₂ 0
  { eq := cmp == .eq
    lt := cmp == .lt
    cmp }

/-- Evaluates the right-hand sides of the correctness theorems in terms of `Array UInt8`. -/
@[noinline] def viaSpec : MemcmpFn Results := fun lhs rhs lstart rstart len _ _ =>
  let a := (lhs.toByteArray.extract lstart.byteIdx (lstart.byteIdx + len)).data
  let b := (rhs.toByteArray.extract rstart.byteIdx (rstart.byteIdx + len)).data
  { eq := a == b
    lt := decide (a < b)
    cmp := compare a b }

/-- A slice with contents `s` that does not start at the beginning of its underlying string. -/
def embed (s : String) : String.Slice :=
  (("x" ++ s ++ "yz").toSlice.drop 1).dropEnd 2

/-- Calls the `Slice` variants on slices of other strings with the same contents. -/
@[noinline] def viaSlices (lhs rhs : String) (lstart rstart : String.Pos.Raw) (len : Nat) :
    Option Results :=
  let ls := embed lhs
  let rs := embed rhs
  if h₁ : lstart.increaseBy len ≤ ls.rawEndPos then
    if h₂ : rstart.increaseBy len ≤ rs.rawEndPos then
      some { eq := memcmpSlice ls rs lstart rstart len h₁ h₂
             lt := memcmpSliceLt ls rs lstart rstart len h₁ h₂
             cmp := memcmpSliceCompare ls rs lstart rstart len h₁ h₂ }
    else
      none
  else
    none

def refCompare : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    if x.toNat < y.toNat then .lt else if y.toNat < x.toNat then .gt else refCompare xs ys

def viaReference (lhs rhs : String) (lstart rstart len : Nat) : Results :=
  let c := refCompare ((lhs.toUTF8.toList.drop lstart).take len)
    ((rhs.toUTF8.toList.drop rstart).take len)
  { eq := c == .eq, lt := c == .lt, cmp := c }

structure Stats where
  lt : Nat := 0
  eq : Nat := 0
  gt : Nat := 0
  failures : Array String := #[]

def fail (msg : String) : StateM Stats Unit :=
  modify fun s => { s with failures := s.failures.push msg }

def check (lhs rhs : String) (lstart rstart len : Nat) : StateM Stats Unit := do
  let args := s!"{lhs.toUTF8} at {lstart} vs {rhs.toUTF8} at {rstart} with length {len}"
  if h₁ : (⟨lstart⟩ : String.Pos.Raw).increaseBy len ≤ lhs.rawEndPos then
    if h₂ : (⟨rstart⟩ : String.Pos.Raw).increaseBy len ≤ rhs.rawEndPos then
      let expected := viaReference lhs rhs lstart rstart len
      let results := [("runtime", viaRuntime), ("closures", viaClosures memcmpStr memcmpStrLt memcmpStrCompare),
        ("model", viaModel), ("spec", viaSpec)]
      for (name, f) in results do
        let r := f lhs rhs ⟨lstart⟩ ⟨rstart⟩ len h₁ h₂
        unless r == expected do
          fail s!"{name} disagrees with reference on {args}:\n{repr r}\nexpected\n{repr expected}"
      match viaSlices lhs rhs ⟨lstart⟩ ⟨rstart⟩ len with
      | some r =>
        unless r == expected do
          fail s!"slices disagree with reference on {args}:\n{repr r}\nexpected\n{repr expected}"
      | none => fail s!"slices out of bounds: {args}"
      match expected.cmp with
      | .lt => modify fun s => { s with lt := s.lt + 1 }
      | .eq => modify fun s => { s with eq := s.eq + 1 }
      | .gt => modify fun s => { s with gt := s.gt + 1 }
      return
  fail s!"out of bounds: {args}"

/-- Checks every in-bounds range of `lhs` against every in-bounds range of `rhs` of the same length. -/
def checkAllRanges (lhs rhs : String) : StateM Stats Unit := do
  for lstart in 0...=lhs.utf8ByteSize do
    for rstart in 0...=rhs.utf8ByteSize do
      for len in 0...=min (lhs.utf8ByteSize - lstart) (rhs.utf8ByteSize - rstart) do
        check lhs rhs lstart rstart len

def report (name : String) (m : StateM Stats Unit) : IO Bool := do
  let (_, s) := Id.run (m.run {})
  IO.println s!"{name}: {s.lt} lt, {s.eq} eq, {s.gt} gt, {s.failures.size} failures"
  for f in s.failures.extract 0 10 do
    IO.println f
  return s.failures.isEmpty

/--
Characters whose encodings contain bytes on both sides of the boundary between `0x7f` and `0x80`,
which a signed comparison gets wrong. `é` and `ÿ` only differ in their second byte.
-/
def alphabet : List Char := ['\x00', 'a', 'b', '\x7f', 'é', 'ÿ', '€']

def allUpTo : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (alphabet.flatMap fun c => (allUpTo n).map (c.toString ++ ·))

def exhaustive : StateM Stats Unit := do
  let xs := allUpTo 2
  for lhs in xs do
    for rhs in xs do
      checkAllRanges lhs rhs

def lengths : List Nat :=
  [1, 4, 8, 16, 17, 32, 33, 64, 65, 128, 129, 257]

/--
Compares `n` copies of `é` (`c3 a9`) with a copy in which the `k`-th character is replaced by
`ÿ` (`c3 bf`), `Ù` (`c3 99`) or `\x7f\x7f` (`7f 7f`), at several pairs of offsets and with several
lengths.
-/
def boundaries : StateM Stats Unit := do
  for n in lengths do
    let base := String.ofList (List.replicate n 'é')
    let positions := [0, 1, 3, 4, 7, 8, 15, 16, 31, 32, n / 2, n - 1].filter (· < n)
    for k in positions do
      for c in ["ÿ", "Ù", "\x7f\x7f"] do
        let modified := String.ofList (List.replicate k 'é') ++ c ++
          String.ofList (List.replicate (n - k - 1) 'é')
        for (lhs, rhs) in [(base, modified), (modified, base)] do
          for (lstart, rstart) in [(0, 0), (1, 1), (2, 2), (0, 2), (2, 0), (8, 8), (3, 5)] do
            let maxLen := min (lhs.utf8ByteSize - lstart) (rhs.utf8ByteSize - rstart)
            for len in [0, 1, 7, 8, 9, 16, 31, 32, 33, 64, maxLen / 2, maxLen - 1, maxLen] do
              if lstart ≤ lhs.utf8ByteSize ∧ rstart ≤ rhs.utf8ByteSize ∧ len ≤ maxLen then
                check lhs rhs lstart rstart len

public def main : IO UInt32 := do
  let mut ok := true
  ok := (← report "exhaustive" exhaustive) && ok
  ok := (← report "boundaries" boundaries) && ok
  return if ok then 0 else 1
