open tactic

meta def issue (hs : hinst_lemmas) : tactic unit :=
rsimp {} hs
