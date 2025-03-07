class One (α : Type) where
  one : α

variable (R A : Type) [One R] [One A]

class OneHom where
  toFun : R → A
  map_one : toFun One.one = One.one

structure Subone where
  mem : R → Prop
  one_mem : mem One.one

structure Subalgebra [OneHom R A] : Type extends Subone A where
  algebraMap_mem : ∀ r : R, mem (OneHom.toFun r)
  one_mem := OneHom.map_one (R := R) (A := A) ▸ algebraMap_mem One.one

/--
error: fields missing: 'one_mem'
-/
#guard_msgs in
example [OneHom R A] : Subalgebra R A where
  mem := _
  algebraMap_mem := _
