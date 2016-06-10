inductive List (A : Type) : Type :=
| nil  : List A
| cons : A → List A → List A
namespace List end List open List
check List.{1}
check cons.{1}
check List.rec.{1 1}
