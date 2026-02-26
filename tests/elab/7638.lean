inductive Foo : Type
  | mk : Foo → Foo

inductive Bar : Type
  | mk : (Unit → Bar) → Bar

def Foo.elim {α : Sort u} : Foo → α
  | ⟨foo⟩ => elim foo
  termination_by structural foo => foo

def Bar.elim {α : Sort u} : Bar → α
  | ⟨bar⟩ => elim (bar ())
  termination_by structural bar => bar

inductive StressTest : Type 5
  | f (x : Type 4 → StressTest)
  | g (x : Type 3 → StressTest)
  | h (x : Type 4 → StressTest) (y : Type 3 → StressTest)

def StressTest.elim {α : Sort u} : StressTest → α
  | f x => elim (x (Type 3))
  | g x => elim (x (Type 2))
  | h x _y => elim (x (Type 3))
  termination_by structural t => t
