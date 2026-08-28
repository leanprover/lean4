import Lean
open Lean

inductive Foo             -- 0.898 ms
  | _01 (a b : Nat) : Foo -- 6.25 ms
  | _02 (a b : Nat) : Foo -- 12.6 ms
  | _03 (a b : Nat) : Foo -- 18.6 ms
  | _04 (a b : Nat) : Foo -- 33.1 ms
  | _05 (a b : Nat) : Foo -- 42.7 ms
  | _06 (a b : Nat) : Foo -- 44.1 ms
  | _07 (a b : Nat) : Foo -- 54.3 ms
  | _08 (a b : Nat) : Foo -- 68 ms
  | _09 (a b : Nat) : Foo -- 103 ms
  | _11 (a b : Nat) : Foo -- 125 ms
  | _12 (a b : Nat) : Foo -- 156 ms
  | _13 (a b : Nat) : Foo -- 245 ms
  | _14 (a b : Nat) : Foo -- 389 ms
  | _15 (a b : Nat) : Foo -- 695 ms
  | _16 (a b : Nat) : Foo -- 1.02 s
  | _17 (a b : Nat) : Foo -- 1.82 s
  | _18 (a b : Nat) : Foo -- 3.70 s
  | _19 (a b : Nat) : Foo -- 9.95 s
  | _20 (a b : Nat) : Foo -- 16.6 s
  | _21 (a b : Nat) : Foo -- 34.2 s
  | _22 (a b : Nat) : Foo -- 78.5 s
  deriving FromJson
