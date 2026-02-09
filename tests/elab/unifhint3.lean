/- Coercion pullback example from the paper "Hints in Unification" -/

universe u

structure Monoid where
  α    : Type u
  op   : α → α → α
  unit : α

structure Group where
  α    : Type u
  op   : α → α → α
  unit : α
  inv : α → α

structure Ring where
  α    : Type u
  mul  : α → α → α
  add  : α → α → α
  neg  : α → α
  one  : α
  zero : α

def Group.ofRing (r : Ring) : Group where
  α    := r.α
  op   := r.add
  inv  := r.neg
  unit := r.zero

def Monoid.ofRing (r : Ring) : Monoid where
  α    := r.α
  op   := r.mul
  unit := r.one

instance : CoeSort Ring (Type u) where
  coe s := s.α

instance : CoeSort Monoid (Type u) where
  coe s := s.α

instance : CoeSort Group (Type u) where
  coe s := s.α

def gop {s : Group} (a b : s) : s :=
  s.op a b

def mop {s : Monoid} (a b : s) : s :=
  s.op a b

infix:70 (priority := high) "*" => mop
infix:65 (priority := high) "+" => gop

unif_hint (r : Ring) (g : Group) where
  g =?= Group.ofRing r
  |-
  r.α =?= g.α

unif_hint (r : Ring) (m : Monoid) where
  m =?= Monoid.ofRing r
  |-
  r.α =?= m.α

def distrib {r : Ring} (a b c : r) := a * (b + c) = a * b + a * c

theorem ex1 {r : Ring} (a b c : r) : distrib a b c = (a * (b + c) = a * b + a * c) :=
  rfl

theorem ex2 {r : Ring} (a b c : r) : distrib a b c = (mop a (gop b c) = gop (mop a b) (mop a c)) :=
  rfl
