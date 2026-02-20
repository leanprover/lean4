variable {a b c : Prop}

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

theorem ex4 (Ha : a) (Hab : a → b) (Hbc : b → c) : c :=
  suffices h1 : b from Hbc h1
  suffices h2 : a from Hab h2
  Ha

theorem ex5 (Ha : a) (Hab : a → b) (Hbc : b → c) : c := by
  suffices h1 : b by apply Hbc; assumption
  suffices h2 : a by apply Hab; exact h2
  assumption
