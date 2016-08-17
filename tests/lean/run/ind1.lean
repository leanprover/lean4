inductive List (A : Type) : Type
| nil  : List
| cons : A → List → List
namespace List end List open List
check List.{1}
check cons.{1}
check List.rec.{1 1}
