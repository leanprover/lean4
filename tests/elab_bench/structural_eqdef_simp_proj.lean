/-!
Benchmark for `size.eq_def`, where `size` recurses structurally over a type that belongs to a
large nested mutual block.

`size` has 13 alternatives and a catch-all, and recurses over `E`. `E` is in a mutual block with
26 other types `A1`, ..., `A26`, each nesting through `List`. The `simp [size]` call in `size_neg`
realizes `size.eq_1`, which realizes `size.eq_def`. The proof of `size.eq_def` simplifies long
projection chains into the `below` structure.
-/
mutual

inductive E where
  | var (n : Nat)
  | neg (a : E)
  | not (a : E)
  | paren (a : E)
  | cast (a : E)
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | idx (a b : E)
  | comma (a b : E)
  | assign (a b : E)
  | cond (c t e : E)
  | call (f : E) (args : List E)
  | a1 (x : A1)
  | a2 (x : A2)
  | a3 (x : A3)
  | a4 (x : A4)
  | a5 (x : A5)
  | a6 (x : A6)
  | a7 (x : A7)
  | a8 (x : A8)
  | a9 (x : A9)
  | a10 (x : A10)
  | a11 (x : A11)
  | a12 (x : A12)
  | a13 (x : A13)
  | a14 (x : A14)
  | a15 (x : A15)
  | a16 (x : A16)
  | a17 (x : A17)
  | a18 (x : A18)
  | a19 (x : A19)
  | a20 (x : A20)
  | a21 (x : A21)
  | a22 (x : A22)
  | a23 (x : A23)
  | a24 (x : A24)
  | a25 (x : A25)
  | a26 (x : A26)

inductive A1 where
  | leaf
  | mk (e : E) (xs : List A2)

inductive A2 where
  | leaf
  | mk (e : E) (xs : List A3)

inductive A3 where
  | leaf
  | mk (e : E) (xs : List A4)

inductive A4 where
  | leaf
  | mk (e : E) (xs : List A5)

inductive A5 where
  | leaf
  | mk (e : E) (xs : List A6)

inductive A6 where
  | leaf
  | mk (e : E) (xs : List A7)

inductive A7 where
  | leaf
  | mk (e : E) (xs : List A8)

inductive A8 where
  | leaf
  | mk (e : E) (xs : List A9)

inductive A9 where
  | leaf
  | mk (e : E) (xs : List A10)

inductive A10 where
  | leaf
  | mk (e : E) (xs : List A11)

inductive A11 where
  | leaf
  | mk (e : E) (xs : List A12)

inductive A12 where
  | leaf
  | mk (e : E) (xs : List A13)

inductive A13 where
  | leaf
  | mk (e : E) (xs : List A14)

inductive A14 where
  | leaf
  | mk (e : E) (xs : List A15)

inductive A15 where
  | leaf
  | mk (e : E) (xs : List A16)

inductive A16 where
  | leaf
  | mk (e : E) (xs : List A17)

inductive A17 where
  | leaf
  | mk (e : E) (xs : List A18)

inductive A18 where
  | leaf
  | mk (e : E) (xs : List A19)

inductive A19 where
  | leaf
  | mk (e : E) (xs : List A20)

inductive A20 where
  | leaf
  | mk (e : E) (xs : List A21)

inductive A21 where
  | leaf
  | mk (e : E) (xs : List A22)

inductive A22 where
  | leaf
  | mk (e : E) (xs : List A23)

inductive A23 where
  | leaf
  | mk (e : E) (xs : List A24)

inductive A24 where
  | leaf
  | mk (e : E) (xs : List A25)

inductive A25 where
  | leaf
  | mk (e : E) (xs : List A26)

inductive A26 where
  | leaf
  | mk (e : E) (xs : List A1)

end

mutual

def size : E → Nat
  | .var _ => 1
  | .neg a => size a + 1
  | .not a => size a + 1
  | .paren a => size a + 1
  | .cast a => size a + 1
  | .add a b => size a + size b + 1
  | .sub a b => size a + size b + 1
  | .mul a b => size a + size b + 1
  | .idx a b => size a + size b + 1
  | .comma a b => size a + size b + 1
  | .assign a b => size a + size b + 1
  | .cond c t e => size c + size t + size e + 1
  | .call f args => size f + sizeList args + 1
  | _ => 0
termination_by structural e => e

def sizeList : List E → Nat
  | [] => 0
  | e :: es => size e + sizeList es
termination_by structural es => es

end

theorem size_neg (a : E) : size (.neg a) = size a + 1 := by
  simp [size]
