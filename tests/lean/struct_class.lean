prelude
import init.core

class point (A : Type*) (B : Type*) :=
mk :: (x : A) (y : B)

#print point

structure point2 (A : Type*) (B : Type*) :=
mk :: (x : A) (y : B)

#print point2
