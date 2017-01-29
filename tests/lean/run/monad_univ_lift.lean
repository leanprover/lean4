universe variables u v

def M : Type u → Type v :=
sorry

instance : monad M :=
sorry

def act1 : M unit :=
return ()

def act2 : M (Σ (A : Type), A) :=
return ⟨nat, 0⟩


def {t s} up {A : Type s} (a : M A) : M (ulift.{t} A) :=
sorry

def {t s} down {A : Type s} (a : M (ulift.{t} A)) : M A :=
sorry

prefix `↑`:10 := up.{1}
prefix `↓`:10 := down.{1}

def ex : M unit :=
↓do
  ↑act1,
  act2,
  ↑act1,
  act2,
  ↑act1
