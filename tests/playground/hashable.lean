set_option trace.Elab.Deriving.hashable true

inductive SimpleInd
| A
| B
deriving Hashable

theorem «inductive fields have different base hashes» : ∀ x, hash x = 
match x with
| SimpleInd.A => 2
| SimpleInd.B => 3 := λ x => rfl

mutual 
inductive Foo : Type → Type
| A : Int → Foo Prop → String → Foo Int
| B : Bar → Foo String 
deriving Hashable
inductive Bar
| C
| D : Foo String → Bar 
deriving Hashable
end

theorem «mutually recursive types don't hash recursively» : ∀ x y, (hash x = 
match x with
| Foo.A a _ b => mixHash (mixHash 2 (hash a)) (hash b)
| Foo.B _ => 3) ∧ (hash y = 
match y with
| Bar.C => 5
| Bar.D _ => 7) := λ x y => ⟨rfl, rfl⟩

inductive ManyConstructors | A | B | C | D | E | F | G | H | I | J | K | L 
| M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
deriving Hashable

theorem «Each constructor is hashed as a different prime to make mixing better» : ∀ x, hash x = 
match x with 
| ManyConstructors.A => 2
| ManyConstructors.B => 3
| ManyConstructors.C => 5
| ManyConstructors.D => 7
| ManyConstructors.E => 11
| ManyConstructors.F => 13
| ManyConstructors.G => 17
| ManyConstructors.H => 19
| ManyConstructors.I => 23
| ManyConstructors.J => 29
| ManyConstructors.K => 31
| ManyConstructors.L => 37
| ManyConstructors.M => 41
| ManyConstructors.N => 43
| ManyConstructors.O => 47
| ManyConstructors.P => 53
| ManyConstructors.Q => 59
| ManyConstructors.R => 61
| ManyConstructors.S => 67
| ManyConstructors.T => 71
| ManyConstructors.U => 73
| ManyConstructors.V => 79
| ManyConstructors.W => 83
| ManyConstructors.X => 89
| ManyConstructors.Y => 97
| ManyConstructors.Z => 101 := λ x => rfl

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
-- @[commandElab «tst»] def elab_tst : CommandElab := fun stx => do
--   let declNames := #[`Foo, `Bar]
--   let declNames := #[`Foo]
--   discard $ mkHashableHandler declNames
--   pure ()