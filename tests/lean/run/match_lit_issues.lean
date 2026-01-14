@[simp] def f1 (i : Int) (a b : Nat) : Nat :=
  match i, a with
  | -1, _  => b
  | _,  0  => b+1
  | _, a+1 => f1 (i-1) a (b*2)

#check f1.eq_1
#check f1.eq_2

example : f1 (-1) a b = b := by simp -- should work
example : f1 (-2) 0 b = b+1 := by simp
example : f1 (-2) (a+1) b = f1 (-3) a (b*2) := by simp
example (h : i ≠ -1) : f1 i (a+1) b = f1 (i-1) a (b*2) := by simp -- should work

@[simp] def f2 (c : Char) (a b : Nat) : Nat :=
  match c, a with
  | 'a', _ => b
  | _,  0  => b+1
  | _, a+1 => f2 c a (b*2)

example : f2 'a' a b = b   := by simp
example : f2 'b' 0 b = b+1 := by simp
example : f2 'b' (a+1) b = f2 'b' a (b*2) := by simp
example (h : c ≠ 'a') : f2 c (a+1) b = f2 c a (b*2) := by simp

@[simp] def f3 (i : Fin 5) (a b : Nat) : Nat :=
  match i, a with
  | 2, _ => b
  | _,  0  => b+1
  | _, a+1 => f3 (i+1) a (b*2)

#check f3.eq_1
#check f3.eq_2

example : f3 2 a b = b   := by simp -- should work
example : f3 3 0 b = b+1 := by simp
example : f3 1 (a+1) b = f3 2 a (b*2) := by simp
example (h : i ≠ 2) : f3 i (a+1) b = f3 (i+1) a (b*2) := by simp; done -- should work

@[simp] def f4 (i : UInt16) (a b : Nat) : Nat :=
  match i, a with
  | 2, _ => b
  | _,  0  => b+1
  | _, a+1 => f4 (i+1) a (b*2)

#check f4.eq_1
#check f4.eq_2

example : f4 2 a b = b   := by simp -- should work
example : f4 3 0 b = b+1 := by simp
example : f4 1 (a+1) b = f4 2 a (b*2) := by simp
example (h : i ≠ 2) : f4 i (a+1) b = f4 (i+1) a (b*2) := by simp -- should work

@[simp] def f5 (i : BitVec 8) (a b : Nat) : Nat :=
  match i, a with
  | 2, _ => b
  | _,  0  => b+1
  | _, a+1 => f5 (i+1) a (b*2)

#check f5.eq_1
#check f5.eq_2

open BitVec

example : f5 2 a b = b   := by simp -- should work
example : f5 2#8 a b = b   := by simp -- should work
example : f5 3 0 b = b+1 := by simp
example : f5 3#8 0 b = b+1 := by simp
example : f5 1 (a+1) b = f5 2 a (b*2) := by simp
example : f5 1#8 (a+1) b = f5 2 a (b*2) := by simp
example (h : i ≠ 2#8) : f5 i (a+1) b = f5 (i+1) a (b*2) := by simp -- should work

@[simp] def f6 (i : BitVec 8) (a b : Nat) : Nat :=
  match i, a with
  | 2#8, _ => b
  | _,  0  => b+1
  | _, a+1 => f6 (i+1) a (b*2)

#check f6.eq_1
#check f6.eq_2

example : f6 2#8 a b = b   := by simp -- should work
example : f6 2#8 a b = b   := by simp -- should work
example : f6 3 0 b = b+1 := by simp
example : f6 3#8 0 b = b+1 := by simp
example : f6 1 (a+1) b = f6 2 a (b*2) := by simp
example : f6 1#8 (a+1) b = f6 2 a (b*2) := by simp
example (h : i ≠ 2#8) : f6 i (a+1) b = f6 (i+1) a (b*2) := by simp -- should work
