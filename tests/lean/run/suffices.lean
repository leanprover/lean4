variables {a b c : Prop}

theorem foo (Ha : a) (Hab : a → b) (Hbc : b → c) : c :=
suffices b, from Hbc this,
suffices a, from Hab this,
Ha
