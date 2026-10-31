/-!
Regression test for #15987: the `rfl` proof of a structural equation lemma whose right-hand side
is a recursive call must not make the kernel compare the arguments of the two calls, here
`x =?= x * 1103515245 % 5`, which reduces `x * 1103515245` with a free `x`.
-/

def f : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => f n ((x * 1103515245) % 5)

-- Still an `rfl` proof (hence `@[backward_defeq]`), of the left-hand side unfolded once.
/--
info: @[backward_defeq] theorem f.eq_2 : ∀ (x n : Nat), f n.succ x = f n (x * 1103515245 % 5) :=
fun x n => Eq.refl (Nat.brecOn (motive := fun x => Nat → Nat) n.succ f._f x)
-/
#guard_msgs in
set_option pp.proofs true in
#print f.eq_2

example : f 1 7 = 0 := by sym => cbv

example : f 1 7 = f 0 (7 * 1103515245 % 5) := by rw [f.eq_2]

def l : List Nat → Nat → Nat
  | [], x => x
  | _ :: xs, x => l xs ((x * 1103515245) % 5)

example : l [1, 2] 7 = 0 := by sym => cbv

example (y x : Nat) (xs : List Nat) : l (y :: xs) x = l xs (x * 1103515245 % 5) := by
  rw [l.eq_2]

-- Nested inductive: the unfolding goes through the auxiliary `brecOn` of the nested type.
inductive T where
  | leaf : T
  | node : List T → T

mutual
def sz : T → Nat → Nat
  | .leaf, x => x
  | .node ts, x => szs ts ((x * 1103515245) % 5)
def szs : List T → Nat → Nat
  | [], x => x
  | t :: ts, x => szs ts ((sz t x * 1103515245) % 5)
end

/--
info: @[backward_defeq] theorem szs.eq_2 : ∀ (x : Nat) (t : T) (ts : List T),
  szs (t :: ts) x = szs ts (sz t x * 1103515245 % 5) :=
fun x t ts => Eq.refl (T.brecOn_1 (t :: ts) sz._f szs._f x)
-/
#guard_msgs in
set_option pp.proofs true in
#print szs.eq_2

example : szs [.leaf, .leaf] 7 = 0 := by sym => cbv

-- Fixed parameter.
def q (k : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => q k n ((x * k * 1103515245) % 5)

/--
info: @[backward_defeq] theorem q.eq_2 : ∀ (k x n : Nat), q k n.succ x = q k n (x * k * 1103515245 % 5) :=
fun k x n => Eq.refl (Nat.brecOn (motive := fun x => Nat → Nat) n.succ (q._f k) x)
-/
#guard_msgs in
set_option pp.proofs true in
#print q.eq_2

example : q 3 1 7 = 0 := by sym => cbv

-- The right-hand side is headed by a different function: the proof stays `Eq.refl lhs`.
mutual
def a : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => b n (x + 1)
def b : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => a n (x + 1)
end

/--
info: @[backward_defeq] theorem a.eq_2 : ∀ (x n : Nat), a n.succ x = b n (x + 1) :=
fun x n => Eq.refl (a n.succ x)
-/
#guard_msgs in
set_option pp.proofs true in
#print a.eq_2
