import Std.WP
open Std.WP

/-! `WPMonad.withFrameClosure` accepts a monad and a resource type in any universe. -/

#guard_msgs (drop info) in
#check (WPMonad.withFrameClosure (m := StateT (ULift.{1} Nat) Id))

#guard_msgs (drop info) in
#check (WPMonad.withFrameClosure (R := ULift.{1} Nat))
