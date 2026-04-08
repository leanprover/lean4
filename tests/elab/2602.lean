inductive Units : Bool → Type where
| seconds : Units false
| hours : Units true

open Units

structure Quantity (d : Bool) : Type where
  quantity : Unit
  units : Units d

instance (d : Bool) : ToString (Quantity d) where
  toString q := match q.units with | seconds => "seconds" | hours => "hours"

