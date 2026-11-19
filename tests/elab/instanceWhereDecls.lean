inductive Foo where
  | mk : Nat → Foo
  | boo : String → Foo

instance : ToString Foo where
  toString o := match o with
    | .mk n => aux1 n
    | .boo s => aux2 s
where
  aux1 (n : Nat) : String :=
    s!".mk {n}"
  aux2 (s : String) : String :=
    s!".boo {s}"

example : toString (Foo.mk 10) = ".mk 10" := rfl
