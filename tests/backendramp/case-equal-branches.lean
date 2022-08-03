
inductive A where
| a1: A
| a2: A


inductive B where
| b1: B
| b2: B

def nat2A(n: Nat): A :=
match n with
| 0 => A.a1
| _ => A.a2

def nat2B(n: Nat): B :=
match n with
| 0 => B.b1
| _ => B.b2


def foo (a: A) (b: B) : Nat :=
match a with
| A.a1 => match b with
          | B.b1 => 42
          | B.b2 => 43
| A.a2 => match b with
          | B.b1 => 42
          | B.b2 => 43

def main (l: List String): IO Unit :=
match l with
  | [s, t] => do
     let n := s.toNat!;
     let m := t.toNat!;
     IO.println (foo (nat2A n) (nat2B m))
     return ()
  | _ => return ()
