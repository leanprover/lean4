import Std.WP
open Std.WP

/-! `WPMonad.withFrameClosure` accepts a monad and a resource type in any universe. -/

#check (WPMonad.withFrameClosure (m := StateT (ULift.{1} Nat) Id))
#check (WPMonad.withFrameClosure (R := ULift.{1} Nat))
