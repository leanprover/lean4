inductive one1.{l} : Type.{max 1 l}
| unit : one1

set_option pp.universes true
check one1

inductive one2.{l} : Type.{max 1 l}
| unit : one2

check one2

section foo
  universe l2
  parameter A : Type.{l2}

  inductive wrapper.{l} : Type.{max 1 l l2}
  | mk : A → wrapper
  check wrapper
end foo

check wrapper
