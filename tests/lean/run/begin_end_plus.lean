example (a b c : Prop) : a → b → c → a ∧ c ∧ b :=
assume Ha Hb Hc,
have aux : c ∧ b, from and.intro Hc Hb,
begin+  -- the whole context is visible
  split,
  state,
  repeat assumption
end

example (a b c : Prop) : a → b → c → a ∧ c ∧ b :=
assume Ha Hb Hc,
have aux : c ∧ b, from and.intro Hc Hb,
by+ split; repeat assumption
