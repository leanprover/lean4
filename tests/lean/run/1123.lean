class OpAssoc (op : α → α → α) : Prop where
  protected op_assoc (x y z) : op (op x y) z = op x (op y z)

abbrev op_assoc (op : α → α → α) [self : OpAssoc op] := self.op_assoc

@[reducible]
structure SemigroupSig (α) where
  op : α → α → α

@[reducible]
structure SemiringSig (α) where
  add : α → α → α
  mul : α → α → α

def SemiringSig.toAddSemigroupSig (s : SemiringSig α) : SemigroupSig α where
  op := s.add

def SemiringSig.toMulSemigroupSig (s : SemiringSig α) : SemigroupSig α where
  op := s.mul

unif_hint (s : SemiringSig α) (t : SemigroupSig α) where
  t =?= s.toAddSemigroupSig ⊢ t.op =?= s.add

unif_hint (s : SemiringSig α) (t : SemigroupSig α) where
  t =?= s.toMulSemigroupSig ⊢ t.op =?= s.mul

class Semigroup (s : SemigroupSig α) : Prop where
  protected op_assoc (x y z) : s.op (s.op x y) z = s.op x (s.op y z)

instance Semirgoup.toOpAssoc (s : SemigroupSig α) [Semigroup s] : OpAssoc (no_index s.op) := ⟨Semigroup.op_assoc⟩

class Semiring (s : SemiringSig α) : Prop where
  protected add_assoc (x y z) : s.add (s.add x y) z = s.add x (s.add y z)
  protected mul_assoc (x y z) : s.mul (s.mul x y) z = s.mul x (s.mul y z)

instance Semiring.toAddSemigroup (s : SemiringSig α) [Semiring s] : Semigroup (no_index s.toAddSemigroupSig) where
  op_assoc := Semiring.add_assoc

instance Semiring.toMulSemigroup (s : SemiringSig α) [Semiring s] : Semigroup (no_index s.toMulSemigroupSig) where
  op_assoc := Semiring.mul_assoc

section Test
variable (s : SemiringSig α) [Semiring s]

local infix:70 " ⋆ " => s.mul

example (w x y z : α) : (w ⋆ x) ⋆ (y ⋆ z) = w ⋆ ((x ⋆ y) ⋆ z) := by
  repeat rw [op_assoc (.⋆.)]

end Test
