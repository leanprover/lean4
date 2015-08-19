variables {a b c : Prop}

theorem foo (Ha : a) (Hab : a → b) (Hbc : b → c) : c :=
suffices to show b, from Hbc this,
suffices to show a, from Hab this,
Ha
