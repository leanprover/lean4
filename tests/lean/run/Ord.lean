
inductive SimpleInd
| A
| B
deriving Ord

mutual 
inductive Foo
| A : Int → (3 = 3) → String → Foo
| B : Bar → Foo
deriving Ord
inductive Bar
| C
| D : Foo → Bar 
deriving Ord
end

inductive ManyConstructors | A | B | C | D | E | F | G | H | I | J | K | L 
| M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
deriving Ord

structure Person := 
  FirstName : String
  LastName : String
  Age : Nat
deriving Ord

structure Company :=
  Name : String
  CEO : Person
  NumberOfEmployees : Nat
deriving Ord