import Std.WP
open Std.WP

/-! The frame-closure transport theorems accept a monad and a resource type in any universe. -/

#guard_msgs (drop info) in
#check (MonadicWP.isLaxMonadMorphism_withFrameClosure (m := StateT (ULift.{1} Nat) Id))

#guard_msgs (drop info) in
#check (MonadicWP.isLaxMonadMorphism_withFrameClosure (R := ULift.{1} Nat))

#guard_msgs (drop info) in
#check (MonadicWP.isMonotone_withFrameClosure (m := StateT (ULift.{1} Nat) Id))
