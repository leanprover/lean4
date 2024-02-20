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

structure Fin0 where
  val : Nat

structure Fin' extends Fin0

structure Fin'' (n : Nat) extends Fin0

structure D (n : Nat) extends A

variable (x : Fin0) (y : Fin') (z : Fin'' 5) (d : D 5)

section
/-!
Checking handling of parameters.
-/

#check x.val
#check y.val
#check z.val
#check d.x

end

section
/-!
Check handling of parameters when `pp.explicit` is true.
-/
set_option pp.explicit true
-- TODO: double check whether the following outputs are the expected ones
#check c.x
#check x.val
#check y.val
#check z.val
#check d.x

end

structure Fn (α β : Type) where
  toFun : α → β

variable (f : Fn Nat Int)

/-!
Check overapplication.
-/

#check f.toFun 0
