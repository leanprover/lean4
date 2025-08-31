
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
  firstName : String
  lastName : String
  age : Nat
deriving Ord

example : compare { firstName := "A", lastName := "B", age := 10 : Person } ⟨"B", "A", 9⟩ = Ordering.lt := rfl

structure Company :=
  name : String
  ceo : Person
  numberOfEmployees : Nat
deriving Ord

structure Fixed (α : Type u) where
  val : Int
deriving Ord

inductive Fixed' : Type → Type 1 where
  | mk : Int → Fixed' α
deriving Ord

-- Before fixing the definition of `Ordering.then`, this would panic,
-- because short-circuiting was not working.
def foo (a : List Nat) := Ordering.then (compare a.length 1) (compare a[0]! 1)
/-- info: Ordering.lt -/
#guard_msgs in
#eval foo []
