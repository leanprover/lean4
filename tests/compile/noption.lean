module

import Init.Util
import Init.ShareCommon

/-!
Tests the semantics and allocation-free runtime representation of `NOption`, including nested
options, immediate values around the constructor-tag niche, and the immediate-value overflow path.
-/

inductive Color where
  | red
  | green
  | blue
  deriving BEq, Repr

def NOption.map (f : α → β) : NOption α → NOption β
  | .none => .none
  | .some x => .some (f x)

def NOption.getD (x : NOption α) (fallback : α) : α :=
  match x with
  | .none => fallback
  | .some x => x

def check (what : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw <| IO.userError s!"check failed: {what}"

@[noinline] def wrap (x : α) : NOption α := .some x

@[noinline] def unwrap (fallback : α) (x : NOption α) : α := x.getD fallback

unsafe def checkSamePointer (what : String) (x : α) : IO Unit := do
  let wrapped := wrap x
  check what (ptrAddrUnsafe x == ptrAddrUnsafe wrapped)
  let y := unwrap x wrapped
  check s!"{what} after extraction" (ptrAddrUnsafe x == ptrAddrUnsafe y)

def checkNat (n : Nat) : IO Unit := do
  check s!"Nat roundtrip {n}" (unwrap 0 (wrap n) == n)

def checkNested : IO Unit := do
  let values : Array (NOption (NOption Nat)) :=
    #[.none, .some .none, .some (.some 0), .some (.some 244), .some (.some 245)]
  let actual := values.map fun x =>
    match x with
    | .none => 0
    | .some .none => 1
    | .some (.some n) => n + 2
  check "nested options" (actual == #[0, 1, 2, 246, 247])

def checkLargestImmediate : IO Unit := do
  let maxSmallNat : Nat := 2 ^ (System.Platform.numBits - 1) - 1
  check "largest immediate Nat is immediate" (unsafe isScalarObj maxSmallNat)
  let wrapped := wrap maxSmallNat
  check "largest immediate Nat uses escape object" !(unsafe isScalarObj wrapped)
  check "largest immediate Nat roundtrip" (unwrap 0 wrapped == maxSmallNat)
  let bigNat := maxSmallNat + 1
  check "large Nat is a pointer" !(unsafe isScalarObj bigNat)
  unsafe checkSamePointer "NOption.some preserves a large Nat pointer" bigNat
  let wrappedTwice := wrap wrapped
  check "nested escape roundtrip" <| match unwrap .none wrappedTwice with
    | .none => false
    | .some n => n == maxSmallNat
  let shared := ShareCommon.shareCommon' wrappedTwice
  check "shared nested escape roundtrip" <| match unwrap .none shared with
    | .none => false
    | .some n => n == maxSmallNat

def checkOwnership (payload : Array Nat) : IO Unit := do
  let mut x := wrap payload
  for _ in *...1000 do
    x := wrap (unwrap payload x)
  check "ownership roundtrip" (unwrap #[] x == payload)

public unsafe def main : IO Unit := do
  check "none branch" ((.none : NOption Nat).getD 37 == 37)
  check "some branch" (((.some 5 : NOption Nat).map (· + 1)).getD 0 == 6)
  check "enum none is immediate" (isScalarObj (NOption.none : NOption Color))
  check "enum some is immediate" (isScalarObj (NOption.some Color.blue))
  check "shifted Nat is immediate" (isScalarObj (NOption.some 244))
  check "nested none is immediate" (isScalarObj (NOption.some (NOption.none : NOption Nat)))
  check "regular Option.some allocates" !(isScalarObj (Option.some Color.blue))
  for n in #[0, 1, 242, 243, 244, 245, 1000] do
    checkNat n
  checkNested
  checkLargestImmediate
  let payload := #[10, 20, 30, 40]
  checkSamePointer "NOption.some preserves an Array pointer" payload
  let regular := Option.some payload
  check "Option.some changes an Array pointer" (ptrAddrUnsafe payload != ptrAddrUnsafe regular)
  checkOwnership payload
  IO.println "ok"
