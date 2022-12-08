class magma (α) where op : α → α → α

infix:70 " ⋆ " => magma.op (self := inferInstance)

class leftIdMagma (α) extends magma α where
  identity : α
  id_op (a : α) : identity ⋆ a = a := by intros; rfl

class rightIdMagma (α) extends magma α where
  identity : α
  op_id (a : α) : a ⋆ identity = a := by intros; rfl

class semigroup (α) extends magma α where
  assoc (a b c : α) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by intros; rfl

class idMagma (α) extends leftIdMagma α, rightIdMagma α

class monoid (α) extends idMagma α, semigroup α

def magmaMonoid : leftIdMagma (base → base) := {
  op := Function.comp
  identity := id
}

def fnCompMonoid : monoid (base → base) := {
  op := Function.comp, identity := id
}

namespace Ex2

structure A (α) where
  subsingleton : ∀ a b : α, a = b := by assumption

structure B (α) where
  op : α → α → α
  idempotent : ∀ a : α, op a a = a := by assumption
  fav : α := by assumption

structure C (α) where
  op : α → α → α
  comm : ∀ a b : α, op a b = op b a := by assumption

structure D (α) extends A α, B α
structure E (α) extends C α, B α

-- Let's reuse these
theorem s (a b : Unit) : a = b := rfl
def op (_ _ : Unit) : Unit := ()
def i (a : Unit) : op a a = a := s _ a
def c (a b : Unit) : op a b = op b a := s _ _

-- Successfully defined
def d : D Unit := have := s; have := i; have := ()
                  { op }

def e : E Unit := have := c; have := i; have := ()
                  { op }

structure F (α) extends D α, E α
structure G (α) extends E α, D α

def f : F Unit := have := s; have := i; have := c; have := ()
                  { op }
-- `idempotent`, `fav` missing
def g : G Unit := have := s; have := i; have := c; have := ()
                  { op }

end Ex2
