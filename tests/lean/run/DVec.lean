/-- A `Vec` is just a `List α` of statically known size -/
def Vec (α : Type _) (n : Nat) : Type _
  := Fin n → α

abbrev TypeVec : Nat → Type _
  := Vec (Type _)

/-- A dependent vector is a heterogenous list of statically known size -/
def DVec {n : Nat} (αs : TypeVec n) : Type _
  := (i : Fin n) → (αs i)

/-- A vector that repeats a single element `a` -/
def Vec.const {α : Type _} (a : α) (n : Nat) : Vec α n
  := fun _ => a

/- `Vec` is defeq to a `DVec` with constant type -/
unif_hint (α : Type _) (n : Nat) where
  |- Vec α n =?= DVec (Vec.const α n)

namespace DVec
  def hd {n : Nat} {αs : TypeVec (n+1)} (v : DVec αs) : (αs 0)
    := v 0
end DVec

namespace Vec
  export DVec (hd)
end Vec

def ts : TypeVec 1 := Vec.const Nat 1

-- works
example (v : DVec ts) : Nat :=
  v.hd

-- works
example (v : Vec Nat 1) : Nat :=
  DVec.hd v

-- Vec.hd exists
#check @Vec.hd

-- works
example (v : Vec Nat 1) : Nat :=
  v.hd
