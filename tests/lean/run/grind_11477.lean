class Rel (a: Type u) where
  rel: a → a → Prop

class Test {a: Type u} [Rel a] (x: a) (p: outParam (a → Prop)) where
  pf: ∀ y: a, Rel.rel x y = p y

theorem test
  {a: Type u} [Rel a]
  (x y: a)
  {p: a → Prop} [Test x p]
  : Rel.rel x y = p y
  := by
    simp [Test.pf]

grind_pattern test => Rel.rel x y

theorem testGrind
  {a: Type u} [Rel a]
  (x y: a)
  {p: a → Prop} [Test x p]
  : Rel.rel x y = p y
  := by
    grind

class TestBis {a: Type u} [Rel a] (x: a) (p: outParam (a → Prop)) where
  pf: ∀ y: a, Rel.rel x y = p y

instance {a: Type u} [Rel a] (x: a) (p: a → Prop) [TestBis x p]: Test x p where
  pf := TestBis.pf

theorem testBisGrind
  {a: Type u} [Rel a]
  (x y: a)
  {p: a → Prop} [TestBis x p]
  : Rel.rel x y = p y
  := by
    grind

section TestHierarchy
class Refl (a: Type u) [Rel a] where
  refl: ∀ x: a, Rel.rel x x

theorem refl
  {a: Type u} [Rel a] [Refl a]
  (x: a)
  : Rel.rel x x
  := by
    apply Refl.refl

grind_pattern refl => Rel.rel x x

class AllRel (a: Type u) [Rel a] where
  all: ∀ x y: a, Rel.rel x y

instance {a} [Rel a] [AllRel a]: Refl a where
  refl := by simp [AllRel.all]

theorem refl_allrel
  {a: Type u} [Rel a] [AllRel a]
  (x: a)
  : Rel.rel x x
  := by
    grind
end TestHierarchy
