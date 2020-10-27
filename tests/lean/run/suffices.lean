variables {a b c : Prop}

theorem ex1 (Ha : a) (Hab : a → b) (Hbc : b → c) : c :=
  suffices b from Hbc this
  suffices a from Hab this
  Ha

theorem ex2 (Ha : a) (Hab : a → b) (Hbc : b → c) : c :=
  suffices b by apply Hbc; assumption
  suffices a by apply Hab; exact this
  Ha

theorem ex3 (Ha : a) (Hab : a → b) (Hbc : b → c) : c := by
  suffices b by apply Hbc; assumption
  suffices a by apply Hab; assumption
  assumption
