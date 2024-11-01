class A (n : Nat) where

instance [A n] : A n.succ where

class B [A 20050] where

set_option trace.Meta.debug true

class C [A 20000] extends B where

#check C.toB

instance : A 20050 where

class D where

instance inst1 : D where
instance inst2 [B] : D where

#synth D
