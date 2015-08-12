import data.examples.vector data.prod
open nat vector prod

variables {A B : Type}

definition unzip : Π {n}, vector (A × B) n → vector A n × vector B n
| unzip nil           := (nil, nil)
| unzip ((a, b) :: t) := (a :: pr₁ (unzip t), b :: pr₂ (unzip t))

theorem unzip_nil : unzip nil = (@nil A, @nil B) :=
rfl

theorem unzip_cons {n : nat} (a : A) (b : B) (t : vector (A × B) n) :
  unzip ((a, b) :: t) = (a :: pr₁ (unzip t), b :: pr₂ (unzip t)) :=
rfl
