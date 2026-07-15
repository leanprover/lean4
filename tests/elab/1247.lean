inductive TestResult (p : Prop) where
  | success : TestResult p

abbrev DecorationsOf (p : Prop) := Prop

def check (p' : DecorationsOf p) (x : TestResult p') : Unit :=
  match x with
  | .success => ()
