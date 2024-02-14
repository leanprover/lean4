/-!
# Delaboration of projection functions
-/

structure A where
  x : Nat

structure B extends A where
  y : Nat

structure C extends B where
  z : Nat

variable (a : A) (b : B) (c : C)

section
/-!
Checking projection delaboration, including parent projection collapse.
-/

#check a.x
#check b.x
#check c.x

#check b.y
#check c.y

#check c.z

end

section
/-!
Checking `pp.structureProjections` can turn off this delaborator.
-/

set_option pp.structureProjections false

#check a.x
#check b.x
#check c.x

#check b.y
#check c.y

#check c.z

end
