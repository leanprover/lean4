open tactic

example (a b : nat) (s t : list nat) : a::s = b::t → a ≠ b → false :=
by cc

example (a b : nat) (s t : list nat) : a::s = b::t → t ≠ s → false :=
by cc

example (a c b : nat) (s t : list nat) : a::s = b::t → a ≠ c → c = b → false :=
by cc

example (a c b : nat) (s t : list nat) : a::a::s = a::b::t → a ≠ c → c = b → false :=
by cc

example (a b : nat) (s t r : list nat) : a::s = r → r = b::t → a ≠ b → false :=
by cc

example (a b : nat) (s t r : list nat) : a::s = r → r = b::t → a = b :=
by cc

example (a b : nat) (s t r : list nat) : list.cons a = list.cons b → a = b :=
begin
  intro h1,
  /- In the current implementation, cc does not "complete" partially applied
     constructor applications. So, the following one should fail. -/
  try {cc},
  /- Complete it manually. TODO(Leo): we can automate it for inhabited types. -/
  note h := congr_fun h1 [],
  cc
end

inductive foo
| mk1 : nat → nat → foo
| mk2 : nat → nat → foo

example (a b : nat) : foo.mk1 a = foo.mk2 b → false :=
begin
  intro h1,
  /- In the current implementation, cc does not "complete" partially applied
     constructor applications. So, the following one should fail. -/
  try {cc},
  note h := congr_fun h1 0,
  cc
end

universe variables u
inductive Vec (α : Type u) : nat → Type (max 1 u)
| nil  : Vec 0
| cons : ∀ {n}, α → Vec n → Vec (nat.succ n)

example (α : Type u) (a b c d : α) (n : nat) (s t : Vec α n) : Vec.cons a s = Vec.cons b t → a ≠ b → false :=
by cc

example (α : Type u) (a b c d : α) (n : nat) (s t : Vec α n) : Vec.cons a s = Vec.cons b t → t ≠ s → false :=
by cc

example (α : Type u) (a b c d : α) (n : nat) (s t : Vec α n) : Vec.cons a (Vec.cons a s) = Vec.cons a (Vec.cons b t) → b ≠ c → c = a → false :=
by cc
