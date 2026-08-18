module

import Init.Data.Erased
import Init.Util

/-!
Tests `Erased` and `NSigma`, including the allocation-free runtime representation of `NSigma`.
-/

def check (what : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw <| IO.userError s!"check failed: {what}"

example (a : α) : (Erased.mk a).out = a := by simp
example (a : Erased α) : Erased.mk a.out = a := by simp

def dependent : NSigma (fun n : Nat => Fin (n + 1)) :=
  .mk 3 2

example : dependent.fst = 3 := by simp [dependent]
example : dependent.snd ≍ (2 : Fin 4) := by simp [dependent, NSigma.mk]

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'NSigma.fst', which is 'noncomputable'
-/
#guard_msgs in
def getFirst (x : NSigma (fun _ : Nat => Unit)) : Nat :=
  x.fst

@[noinline] def pack (n : Nat) (xs : Array Nat) : NSigma (fun _ : Nat => Array Nat) :=
  .mk n xs

@[noinline] def unpack (x : NSigma (fun _ : Nat => Array Nat)) : Array Nat :=
  x.snd

unsafe def checkSamePointer (what : String) (x : α) (y : β) : IO Unit :=
  check what (ptrAddrUnsafe x == ptrAddrUnsafe y)

public unsafe def main : IO Unit := do
  let payload := #[10, 20, 30, 40]
  check "Erased is immediate" (isScalarObj (Erased.mk payload))
  let packed := pack 4 payload
  checkSamePointer "NSigma is represented by its second component" payload packed
  checkSamePointer "NSigma.snd adds no indirection" payload (unpack packed)
  IO.println "ok"
