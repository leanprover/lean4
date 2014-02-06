import macros

theorem T (a b c d e : Bool) : (a → b) → (a → b → c) → d ∧ a → (d → c → e) → e
:= assume Hab Habc Hda Hde,
     have Hd : d,
       from and_eliml Hda,
     have Ha : a,
       from and_elimr Hda,
     have Hc : c,
       from (have Hb : b,
               from Hab Ha,
             show c,
               from Habc Ha Hb),
     show e,
       from Hde Hd Hc
