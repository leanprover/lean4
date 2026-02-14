inductive Foo (α : Type) (x : α) where
| c1 : Foo α x
| c2 : Foo α x

def Foo.mk (n : Nat) : Foo (Fin (n + 1)) 0 :=
  match n with
  | .zero => .c1
  | .succ _ => .c1

def Foo.num {α : Type} {x : α} (f : Foo α x) : Nat :=
  0

/-
Issue #12140: `closeGoalWithValuesEq` must check that the two interpreted values
have the same type before calling `mkEqProof`. When equivalence classes contain
heterogeneous equalities (e.g., `0 : Fin 3` and `0 : Fin 2` merged via `HEq`),
`mkEqProof` would fail with an internal error.
-/

/--
error: `grind` failed
case grind.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
n : Nat
ih : (Foo.mk n).num = 0
h : ¬(Foo.mk (n + 1)).num = 0
h_1 : n + 1 = Nat.zero + 1
h_2 : 1 = Nat.zero + 1
h_3 : 1 = Nat.zero.succ + 1
h_4 : 1 = (n + 1).succ + 1
h_5 : 1 = (Nat.zero + 2).succ + 1
h_6 : (n + 2).succ + 1 = (Nat.zero + 2).succ + 1
h_7 : 2 = Nat.zero + 2
h_8 : 1 = (Nat.zero + 3).succ + 1
h_9 : (n + 3).succ + 1 = (Nat.zero + 3).succ + 1
h_10 : 3 = Nat.zero + 3
h_11 : 1 = (Nat.zero + 4).succ + 1
h_12 : (n + 4).succ + 1 = (Nat.zero + 4).succ + 1
h_13 : 4 = Nat.zero + 4
h_14 : 1 = (Nat.zero + 5).succ + 1
h_15 : (n + 5).succ + 1 = (Nat.zero + 5).succ + 1
h_16 : 5 = Nat.zero + 5
h_17 : 1 = (Nat.zero + 6).succ + 1
⊢ False
-/
#guard_msgs in
theorem foo (n : Nat) : (Foo.mk n).num = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    grind -verbose [Foo.mk]
