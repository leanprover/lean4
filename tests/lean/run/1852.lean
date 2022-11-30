class foo (F : Type) where
  foo : F

class foobar (F : OutParam Type) [foo F] where
  bar : F
