import Std

/--
info: Try these:
  [apply] simp
  [apply] simp only
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example : True := by try?

/--
info: Try these:
  [apply] by simp
  [apply] by simp only
  [apply] by grind
  [apply] by grind only
  [apply] by simp_all
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by

/--
info: Try these:
  [apply] by simp
  [apply] by simp only [List.append_assoc]
  [apply] by grind
  [apply] by grind only
  [apply] by simp_all
---
error: unsolved goals
x y z : List Nat
⊢ x ++ (y ++ z) = x ++ y ++ z
-/
#guard_msgs in
example {x y z : List Nat} : x ++ (y ++ z) = (x ++ y) ++ z := by

/--
info: Try these:
  [apply] by exact Int.emod_add_mul_ediv a b
---
error: unsolved goals
a b : Int
⊢ a % b + b * (a / b) = a
-/
#guard_msgs in
example {a b : Int} : a % b + b * (a / b) = a := by

/--
info: Try these:
  [apply] by grind
  [apply] by grind only [= Std.ExtHashMap.getKey_erase, = Std.ExtHashMap.contains_erase,
    = Std.ExtHashMap.mem_erase, = Std.ExtHashMap.contains_insert, = Std.ExtHashMap.getElem?_insert,
    = getElem?_pos, = Std.ExtHashMap.getElem?_erase, = Std.ExtHashMap.getKey_eq, = getElem?_neg,
    =_ Std.ExtHashMap.contains_iff_mem, = Std.ExtHashMap.mem_insert]
---
error: unsolved goals
m : Std.ExtHashMap Nat Int
⊢ (m.insert 37 5).erase 37 = m.erase 37
-/
#guard_msgs in
example {m : Std.ExtHashMap Nat Int} : (m.insert 37 5).erase 37 = m.erase 37 := by

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/--
info: Try these:
  [apply] by grind [= fib]
  [apply] by grind only [fib]
---
error: unsolved goals
n : Nat
⊢ fib (n + 8) % 3 = fib n % 3
-/
#guard_msgs in
example : fib (n + 8) % 3 = fib n % 3 := by
