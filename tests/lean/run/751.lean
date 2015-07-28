inductive foo (A : Type) :=
| intro : foo A → foo A
with bar : Type :=
| intro : bar A
