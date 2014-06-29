import logic

definition id {A : Type} (a : A) := a

theorem tst {A B : Bool} (H1 : A) (H2 : B) : id A
:= by [!echo "message" 5, unfold id, exact]

theorem tst2 {A B : Bool} (H1 : A) (H2 : B) : id A
:= by [repeat echo "message" 5, unfold id, exact]