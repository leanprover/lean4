/- Type classes are heavily used in Lean -/
namespace Example

class Mul (α : Type u) where
  mul : α → α → α

infixl:70 " * " => Mul.mul

def double [Mul α] (a : α) := a * a

class Semigroup (α : Type u) extends Mul α where
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)

instance : Semigroup Nat where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc

#eval double 5

class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : (α → β) → f α → f β

infixr:100 " <$> " => Functor.map

class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  id_map   (x : f α) : id <$> x = x
  comp_map (g : α → β) (h : β → γ) (x : f α) :(h ∘ g) <$> x = h <$> g <$> x

end Example

/-
`Deriving instances automatically`

We have seen `deriving Repr` in a few examples.
It is an instance generator.
Lean comes equipped with generators for the following classes.
`Repr`, `Inhabited`, `BEq`, `DecidableEq`,
`Hashable`, `Ord`, `FromToJson`, `SizeOf`
-/

inductive Tree (α : Type u) where
  | leaf (val : α)
  | node (left right : Tree α)
  deriving DecidableEq, Ord, Inhabited, Repr
