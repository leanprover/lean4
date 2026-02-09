
structure Power where
  x : String
  k : Nat
  deriving BEq, ReflBEq, LawfulBEq

inductive Mon where
  | unit
  | mult (p : Power)
  deriving BEq, ReflBEq

deriving instance LawfulBEq for Mon
