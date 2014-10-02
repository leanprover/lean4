import data.num

definition id (A : Type) (a : A) := a

check id Type num

check id Type' num

check id Type.{1} num

check id _ num

check id Type.{_+1} num

check id Type.{0+1} num

check id Type Type.{1}

check id Type' Type.{1}
