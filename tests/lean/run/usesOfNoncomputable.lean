noncomputable def badPair : Nat × (Nat × Nat) := ⟨1, ⟨2, 3⟩⟩
noncomputable def badFun (a : Nat) : Nat := a

structure S (n : Nat)
structure T where
  n : Nat

def test1 : S badPair.2.1 := {}

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'badPair', which is 'noncomputable'
-/
#guard_msgs in
def test2 : T := { n := badPair.2.1 }

def test3 (a : Nat) : S (badFun a) := {}
def test4 (a : Nat) : S ((badFun a) + 1) := {}

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'badFun', which is 'noncomputable'
-/
#guard_msgs in
def test5 (a : Nat) : T := { n := badFun a }

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'badFun', which is 'noncomputable'
-/
#guard_msgs in
def test6 (a : Nat) : T := { n := 2 * (badFun a) }

structure U (a : Nat × Nat)
structure V where
  a : Nat × Nat

def test7 (a : Nat) : U (⟨badFun a, 0⟩) := {}
def test8 (a : Nat) : U ((V.mk ⟨badFun a, 1⟩).a) := {}

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'badFun', which is 'noncomputable'
-/
#guard_msgs in
def test9 (a : Nat) : V := ⟨a, badFun a⟩

universe u

def Erased (α : Sort u) : Sort max 1 u :=
  { s : α → Prop // ∃ a, (a = ·) = s }

def Erased.mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

noncomputable def Erased.out {α} : Erased α → α
  | ⟨_, h⟩ => Classical.choose h

structure Foo where
  spec : Erased Nat
  data : Nat

def test10 : Foo where
  spec := Erased.mk (Erased.mk 0).out
  data := 0

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Erased.out', which is 'noncomputable'
-/
#guard_msgs in
def test11 : Foo where
  spec := Erased.mk 0
  data := (Erased.mk 0).out
