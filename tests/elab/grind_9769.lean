module
def Foo (n : Nat) := Σ (m : Nat), {f : Fin (n + 2) → Fin (m + 2) // f 0 = 0}

variable (n : Nat)

def Foo.e (f : Foo n) := f.2.1

def Foo.id : (Foo n) := ⟨n, ⟨fun x => x, rfl⟩⟩

def Foo.EqId (f : Foo n) : Prop :=
  f = (Foo.id _)

structure Bar {n m : Nat} (f : Fin (n + 2) → Fin (m + 1)) : Prop where
  out : f 1 = 1

/--
error: `grind` failed
case grind
n : Nat
f : Foo n
this : Bar fun x => x
h : ¬(Foo.EqId n f → Bar (Foo.e n f))
⊢ False
-/
#guard_msgs in
theorem EqIdToZero (f : Foo n) : f.EqId → Bar f.e := by
  have : Bar (fun x => x : Fin (n + 2) → Fin (n + 2)) := ⟨rfl⟩
  grind -verbose [Foo.e, Foo.id, Foo.EqId]

-- A simpler example that is provable and also triggers issue #9769

structure Boo (n : Nat) where
  x : Nat

example (a : Boo 1) (n : Nat) : a ≍ Boo.mk (n := n) b → n = 1 → a.x = b := by
  grind
