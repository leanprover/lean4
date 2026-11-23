/-!
# Tests for numeric projections of inductive types
-/

/-!
Non-recursive, no indices.
-/
inductive I0 where
  | mk (x : Nat) (xs : List Nat)
/-- info: fun v => v.1 : I0 → Nat -/
#guard_msgs in #check fun (v : I0) => v.1
/-- info: fun v => v.2 : I0 → List Nat -/
#guard_msgs in #check fun (v : I0) => v.2

/-!
Recursive, no indices.
-/
inductive I1 where
  | mk (x : Nat) (xs : I1)
/-- info: fun v => v.1 : I1 → Nat -/
#guard_msgs in #check fun (v : I1) => v.1
/-- info: fun v => v.2 : I1 → I1 -/
#guard_msgs in #check fun (v : I1) => v.2

/-!
Non-recursive, indices.
-/
inductive I2 : Nat → Type where
  | mk (x : Nat) (xs : List (Fin x)) : I2 (x + 1)
/--
error: invalid projection
  v.1
from type
  I2 2
---
info: fun v => sorry : (v : I2 2) → ?m.3 v
-/
#guard_msgs in #check fun (v : I2 2) => v.1
/--
error: invalid projection
  v.2
from type
  I2 2
---
info: fun v => sorry : (v : I2 2) → ?m.3 v
-/
#guard_msgs in #check fun (v : I2 2) => v.2

/-!
Recursive, indices.
-/
inductive I3 : Nat → Type where
  | mk (x : Nat) (xs : I3 (x + 1)) : I3 x
/--
error: invalid projection
  v.1
from type
  I3 2
---
info: fun v => sorry : (v : I3 2) → ?m.3 v
-/
#guard_msgs in #check fun (v : I3 2) => v.1
/--
error: invalid projection
  v.2
from type
  I3 2
---
info: fun v => sorry : (v : I3 2) → ?m.3 v
-/
#guard_msgs in #check fun (v : I3 2) => v.2


/-!
Make sure these can be compiled.
-/
def f0_1 (v : I0) : Nat := v.1
def f0_2 (v : I0) : List Nat := v.2
def f1_1 (v : I1) : Nat := v.1
def f1_2 (v : I1) : I1 := v.2

/--
error: invalid projection
  v.1
from type
  I2 n
-/
#guard_msgs in
def f2_1 (v : I2 n) : Nat := v.1
/--
error: invalid projection
  v.2
from type
  I2 n
-/
#guard_msgs in
def f2_2 (v : I2 n) : List (Fin (f2_1 v)) := v.2
/--
error: invalid projection
  v.1
from type
  I3 n
-/
#guard_msgs in
def f3_1 (v : I3 n) : Nat := v.1
/--
error: invalid projection
  v.2
from type
  I3 n
-/
#guard_msgs in
def f3_2 (v : I3 n) : I3 (f3_1 v + 1) := v.2
