(*
simple_tac = Repeat(conj_tac()) .. assumption_tac()
*)

theorem T4 (a b : Bool) : a → b → a /\ b /\ a := _.
        simple_tac
        done

print environment 1.