import logic data.unit

structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

open point

check rec     -- error, rec is protected
