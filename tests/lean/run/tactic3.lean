import logic

theorem tst {A B : Bool} (H1 : A) (H2 : B) : A
:= by [echo "first try",  show, now  |
       echo "second try", fail       |
       echo "third try", exact]
