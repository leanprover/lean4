class foo (F : Type) where
  foo : F

class foobar (F : outParam Type) [foo F] where
  bar : F
