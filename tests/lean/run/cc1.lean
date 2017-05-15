open tactic

set_option pp.implicit true

example (a b c d : nat) (f : nat → nat → nat) : a = b → b = c → d + (if b > 0 then a else b) = 0 → f (b + b) b ≠ f (a + c) c → false :=
by do intros,
      s ← cc_state.mk_using_hs,
      trace s,
      t₁ ← to_expr `(f (b + b) b),
      t₂ ← to_expr `(f (a + c) c),
      b  ← to_expr `(b),
      d  ← to_expr `(d),
      guard (s^.inconsistent),
      guard (s^.eqc_size b = 4),
      guard (not (s^.in_singlenton_eqc b)),
      guard (s^.in_singlenton_eqc d),
      trace ">>> Equivalence roots",
      trace s^.roots,
      trace ">>> b's equivalence class",
      trace (s^.eqc_of b),
      pr ← s^.eqv_proof t₁ t₂,
      note `h none pr,
      contradiction

example (a b : nat) (f : nat → nat) : a = b → f a = f b :=
by cc

example (a b : nat) (f : nat → nat) : a = b → f a ≠ f b → false :=
by cc

example (a b : nat) (f : nat → nat) : a = b → f (f a) ≠ f (f b) → false :=
by cc

example (a b c : nat) (f : nat → nat) : a = b → c = b → f (f a) ≠ f (f c) → false :=
by cc

example (a b c : nat) (f : nat → nat → nat) : a = b → c = b → f (f a b) a ≠ f (f c c) c → false :=
by cc

example (a b c : nat) (f : nat → nat → nat) : a = b → c = b → f (f a b) a = f (f c c) c :=
by cc

example (a b c d : nat) : a == b → b = c → c == d → a == d :=
by cc

example (a b c d : nat) : a = b → b = c → c == d → a == d :=
by cc

example (a b c d : nat) : a = b → b == c → c == d → a == d :=
by cc

example (a b c d : nat) : a == b → b == c → c = d → a == d :=
by cc

example (a b c d : nat) : a == b → b = c → c = d → a == d :=
by cc

example (a b c d : nat) : a = b → b = c → c = d → a == d :=
by cc

example (a b c d : nat) : a = b → b == c → c = d → a == d :=
by cc

constant f {α : Type} : α → α → α
constant g : nat → nat

example (a b c : nat) : a = b → g a == g b :=
by cc

example (a b c : nat) : a = b → c = b → f (f a b) (g c) = f (f c a) (g b) :=
by cc

example (a b c d e x y : nat) : a = b → a = x → b = y → c = d → c = e → c = b → a = e :=
by cc
