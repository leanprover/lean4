namespace Ex1

class A where

class B (n : Nat) where

class C where

instance test [B 10000] [C] : A where

instance Bsucc {n : Nat} [B n] : B n.succ where

instance instB0 : B 0 where

instance instB10000 : B 10000 where

/--
error: failed to synthesize
  A
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth A -- should fail quickly

end Ex1

namespace Ex2

class A where
class B (n : Nat) where
class C where

instance test' [B 10] : A where
instance test [B 0] [C] : A where
instance foo {n : Nat} [B n.succ] : B n where
instance instB (n : Nat) : B n where

/--
info: test'
-/
#guard_msgs in
#synth A

end Ex2
