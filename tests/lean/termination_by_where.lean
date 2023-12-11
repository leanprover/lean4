/-!
This module tests various indentation variants related to termination_by.

It uses `id @Nat` to make sure it fails loudly if applied to the wrong function.
-/

-- For concise recursive definition that need well-founded recursion
opaque dec1 : Nat → Nat
axiom dec1_lt (n : Nat) : dec1 n < n
opaque dec2 : Nat → Nat
axiom dec2_lt (n : Nat) : dec2 n < n

def Ex1.foo (n : Nat) : Nat := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
    decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex1.foo' (n : Nat) : Nat := foo' (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

def Ex2.foo (n : Nat) : Nat := foo (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := bar (dec2 m)
      decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex2.foo' (n : Nat) : Nat := foo' (dec1 n) + bar n
  where
    bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

def Ex3.foo (n : Nat) : Nat := foo (dec1 n) + bar n
  where bar (m : Nat) : Nat := bar (dec2 m)
        decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex3.foo' (n : Nat) : Nat := foo' (dec1 n) + bar n
  where bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

def Ex4.foo (n : Nat) : Nat := foo (dec1 n) + bar n
  where bar (m : Nat) : Nat :=
     bar (dec2 m)
        decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex4.foo' (n : Nat) : Nat := foo' (dec1 n) + bar n
  where bar (m : Nat) : Nat :=
     m
decreasing_by apply dec1_lt

def Ex6.foo (n : Nat) : Nat := foo (dec1 n) + bar n
where bar (m : Nat) : Nat := bar (dec2 m)
      decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex6.foo' (n : Nat) : Nat := foo' (dec1 n) + bar n
where bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt


def Ex7.foo (n : Nat) : Nat := foo (dec1 n) + bar n
where
  bar (m : Nat) : Nat := bar (dec2 m)
  decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

def Ex7.foo' (n : Nat) : Nat := foo' (dec1 n) + bar n
where
  bar (m : Nat) : Nat := m
decreasing_by apply dec1_lt

def Ex8.foo (n : Nat) : Nat := foo (dec1 n) + bar n
where
bar (m : Nat) : Nat := bar (dec2 m)
decreasing_by apply dec2_lt
decreasing_by apply dec1_lt

-- In this variant, there is no way to not have `bar` pick up the decreasing_by.
-- def Ex8.foo' (n : Nat) : Nat := foo' (dec1 n) + bar n
-- where
-- bar (m : Nat) : Nat := m
-- decreasing_by apply dec1_lt
