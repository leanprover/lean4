import data.num

definition id2 (A : Type) (a : A) := a

check id2 Type num

check id2 Type' num

check id2 Type.{1} num

check id2 _ num

check id2 Type.{_+1} num

check id2 Type.{0+1} num

check id2 Type Type.{1}

check id2 Type' Type.{1}
