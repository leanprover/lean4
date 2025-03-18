import Std.Tactic.RSimp


-- A little experimental rsimp set

attribute [rsimp] Fin.ext_iff
attribute [rsimp] Fin.val_mul Fin.val_add
-- Unfortunately, `attribute` does not allow to add theorems with symm?
def Bool.cond_decide_symm := fun α p inst t e => (@Bool.cond_decide α p inst t e).symm
attribute [rsimp] Bool.cond_decide_symm
def Nat.beq_eq_symm {x y : Nat} : (x = y) = (x.beq y = true) := (@Nat.beq_eq x y).symm
attribute [rsimp] Nat.beq_eq_symm
attribute [rsimp] Std.Tactic.BVDecide.Normalize.Bool.decide_eq_true
@[rsimp] theorem Bool.cond_true_false (b : Bool) : cond b true false = b := by simp


--  A function we may want to optimize

def foo (a b : Fin 12) : Bool := if a * b = a + b then true else false

attribute [rsimp_optimize] foo

/--
info: def foo.rsimp : Fin 12 → Fin 12 → Bool :=
fun a b => (↑a * ↑b % 12).beq ((↑a + ↑b) % 12)
-/
#guard_msgs in
#print foo.rsimp

/-- info: foo.eq_rsimp : foo = foo.rsimp -/
#guard_msgs in
#check foo.eq_rsimp

/-- error: foo.rsimp has already been declared -/
#guard_msgs in
attribute [rsimp_optimize] foo

-- Now a recursive function
def bar (a b : Fin 12) : Bool :=
  if a = 0 then
    false
  else
    if a * b = a + b then true else bar (a - 1) (b + 1)

attribute [rsimp_optimize] bar

/--
info: def bar.rsimp : Fin 12 → Fin 12 → Bool :=
rsimp_iterate bar fun ih a b =>
  bif (↑a).beq ↑0 then false else bif (↑a * ↑b % 12).beq ((↑a + ↑b) % 12) then true else ih (a - 1) (b + 1)
-/
#guard_msgs in
#print bar.rsimp


namespace NotReallyRecursive

-- Mostly a curious corner case: A recursive function with recursion that will be optimized away

def bar (a b : Fin 12) : Bool :=
  if a = 0 then
    false
  else
    if true then true else bar (a - 1) (b + 1)
termination_by a

attribute [rsimp] Bool.cond_true
attribute [rsimp_optimize] bar
/--
info: def NotReallyRecursive.bar.rsimp : Fin 12 → Fin 12 → Bool :=
fun a b => bif (↑a).beq ↑0 then false else true
-/
#guard_msgs in
#print bar.rsimp

end NotReallyRecursive
