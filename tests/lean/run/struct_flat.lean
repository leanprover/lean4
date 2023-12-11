structure AddHom (α) [Add α] where
  toFun : α → α
  map_add (a b : α) : toFun (a + b) = toFun a + toFun b

structure MulHom (α) [Mul α] where
  toFun : α → α
  map_mul (a b : α) : toFun (a * b) = toFun a * toFun b

structure DistribHom (α) [Add α] [Mul α] extends AddHom α, MulHom α
structure DistribHomFlatAdd (α) [Add α] [Mul α] extends flat AddHom α, MulHom α

#print DistribHom.mk
#print DistribHomFlatAdd.mk

-- the flat version has less noise when in a goal view
set_option pp.proofs.withType false
#check {toFun := id, map_add := fun _ _ => rfl, map_mul := fun _ _ => rfl : DistribHom Nat}
#check {toFun := id, map_add := fun _ _ => rfl, map_mul := fun _ _ => rfl : DistribHomFlatAdd Nat}

-- marking `MulHom` as flat makes no difference, since `Add` has already been flattened.
structure DistribHomFlatMul (α) [Add α] [Mul α] extends AddHom α, flat MulHom α
structure DistribHomFlatBoth (α) [Add α] [Mul α] extends flat AddHom α, flat MulHom α
#print DistribHomFlatMul.mk
#print DistribHomFlatBoth.mk
