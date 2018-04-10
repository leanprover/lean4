open tactic

example (a b : nat) : a = 1 → b = 2 → a = b → false :=
by cc

example (a b c : int) : a = 1 → c = -2 → a = b → c = b → false :=
by cc

example (a b : char) : a = 'h' → b = 'w' → a = b → false :=
by cc

example (a b : string) : a = "hello" → b = "world" → a = b → false :=
by cc

example (a b c : string) : a = c → a = "hello" → c = "world" → c = b → false :=
by cc
