def loop (x : Nat) : Unit := loop (x + 1)
termination_by tailrecursion

/--
info: equations:
theorem loop.eq_1 : ∀ (x : Nat), loop x = loop (x + 1)
-/
#guard_msgs in
#print equations loop

/-- error: unknown constant 'loop.induct' -/
#guard_msgs in
#check loop.induct

def find (P : Nat → Bool) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    find P (x +1)
termination_by tailrecursion

/--
info: equations:
theorem find.eq_1 : ∀ (P : Nat → Bool) (x : Nat), find P x = if P x = true then some x else find P (x + 1)
-/
#guard_msgs in
#print equations find

/--
error: Termination by tailrecursion needs a nonempty codomain:
  failed to synthesize
    Nonempty (Fin n)
  Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def notinhabited (n m : Nat) : Fin n :=
  notinhabited n (m+1)
termination_by tailrecursion

def fib (n : Nat) := go 0 0 1
where
  go i fip fi :=
    if i = n then
      fi
    else
      go (i + 1) fi (fi + fip)
  termination_by tailrecursion

/--
error: fail to show termination for
  mutual1
  mutual2
with errors
failed to infer structural recursion:
Cannot use parameters n of mutual1 and n of mutual2:
  failed to eliminate recursive application
    mutual2 (m + 1) n
Cannot use parameters n of mutual1 and m of mutual2:
  failed to eliminate recursive application
    mutual2 (m + 1) n
Cannot use parameters m of mutual1 and n of mutual2:
  failed to eliminate recursive application
    mutual2 (m + 1) n
Cannot use parameters m of mutual1 and m of mutual2:
  failed to eliminate recursive application
    mutual2 (m + 1) n


Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
Call from mutual1 to mutual2 at 88:34-51:
  n m
n ? ?
m = ?
Call from mutual2 to mutual1 at 89:34-51:
  n m
n _ ?
m _ _

Please use `termination_by` to specify a decreasing measure.

Termination by tailrecursion cannot handle dependent type:
  (x : (_ : Nat) ×' Nat ⊕' (_ : Nat) ×' Nat) → PSum.casesOn x (fun _x => Unit) fun _x => Unit
-/
#guard_msgs in
mutual
def mutual1 (n m : Nat) : Unit := mutual2 (m + 1) n
def mutual2 (n m : Nat) : Unit := mutual1 (m + 1) n
end
