set_option trace.Elab.Deriving.hashable true

inductive SimpleInd
| A
| B
deriving Hashable

theorem «inductive fields have different base hashes» : ∀ x, hash x =
match x with
| SimpleInd.A => 0
| SimpleInd.B => 1 := λ x => rfl
mutual
inductive Foo : Type → Type
| A : Int → (3 = 3) → String → Foo Int
| B : Bar → Foo String
deriving Hashable
inductive Bar
| C
| D : Foo String → Bar
deriving Hashable
end

#eval hash (Foo.A 3 rfl "bla")
#eval hash (Foo.B $ Bar.D $ Foo.B Bar.C)

inductive ManyConstructors | A | B | C | D | E | F | G | H | I | J | K | L
| M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
deriving Hashable

theorem «Each constructor is hashed as a different number to make mixing better» : ∀ x, hash x =
match x with
| ManyConstructors.A => 0
| ManyConstructors.B => 1
| ManyConstructors.C => 2
| ManyConstructors.D => 3
| ManyConstructors.E => 4
| ManyConstructors.F => 5
| ManyConstructors.G => 6
| ManyConstructors.H => 7
| ManyConstructors.I => 8
| ManyConstructors.J => 9
| ManyConstructors.K => 10
| ManyConstructors.L => 11
| ManyConstructors.M => 12
| ManyConstructors.N => 13
| ManyConstructors.O => 14
| ManyConstructors.P => 15
| ManyConstructors.Q => 16
| ManyConstructors.R => 17
| ManyConstructors.S => 18
| ManyConstructors.T => 19
| ManyConstructors.U => 20
| ManyConstructors.V => 21
| ManyConstructors.W => 22
| ManyConstructors.X => 23
| ManyConstructors.Y => 24
| ManyConstructors.Z => 25 := λ x => rfl

structure Person :=
  FirstName : String
  LastName : String
  Age : Nat
deriving Hashable

structure Company :=
  Name : String
  CEO : Person
  NumberOfEmployees : Nat
deriving Hashable

-- structures hash just fine
#eval hash {
  Name := "Microsoft"
  CEO := { FirstName := "Satya", LastName := "Nadella", Age := 53 }
  NumberOfEmployees := 165000 : Company }
-- 10875484723257753924

-- syntax(name := tst) "tst" : command
-- @[command_elab «tst»] def elab_tst : CommandElab := fun stx => do
--   let declNames := #[`Foo, `Bar]
--   let declNames := #[`Foo]
--   discard $ mkHashableHandler declNames
--   pure ()
