prelude
import init.core

structure [class] point (A : Type*) (B : Type*) :=
mk :: (x : A) (y : B)

print classes

structure point2 (A : Type*) (B : Type*) :=
mk :: (x : A) (y : B)

print classes
