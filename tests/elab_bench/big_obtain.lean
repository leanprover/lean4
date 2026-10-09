/-!
Destructures a dependent chain of 40 existentials (80 pattern names) with `obtain` and repacks it.
Each component's type mentions earlier components, so the terms that `rcases` builds for the
eliminated hypotheses carry free variables at every level.
-/

def Chain : Prop :=
    ∃ x1 : Nat, x1 + x1 + x1 + x1 + 1 = x1 + x1 + x1 + x1 + 1 ∧
    ∃ x2 : Nat, x2 + x2 + x2 + x2 + 2 = x2 + x2 + x2 + x2 + 2 ∧
    ∃ x3 : Nat, x3 + x1 + x3 + x1 + 3 = x3 + x1 + x3 + x1 + 3 ∧
    ∃ x4 : Nat, x4 + x4 + x4 + x2 + 4 = x4 + x4 + x4 + x2 + 4 ∧
    ∃ x5 : Nat, x5 + x4 + x5 + x5 + 5 = x5 + x1 + x5 + x2 + 5 ∧
    ∃ x6 : Nat, x6 + x4 + x6 + x4 + 6 = x6 + x4 + x6 + x4 + 6 ∧
    ∃ x7 : Nat, x7 + x4 + x7 + x3 + 7 = x7 + x2 + x7 + x1 + 7 ∧
    ∃ x8 : Nat, x8 + x4 + x8 + x2 + 8 = x8 + x8 + x8 + x6 + 8 ∧
    ∃ x9 : Nat, x9 + x4 + x9 + x1 + 9 = x9 + x7 + x9 + x4 + 9 ∧
    ∃ x10 : Nat, x10 + x4 + x10 + x10 + 10 = x10 + x6 + x10 + x2 + 10 ∧
    ∃ x11 : Nat, x11 + x4 + x11 + x10 + 11 = x11 + x5 + x11 + x11 + 11 ∧
    ∃ x12 : Nat, x12 + x4 + x12 + x10 + 12 = x12 + x4 + x12 + x10 + 12 ∧
    ∃ x13 : Nat, x13 + x4 + x13 + x10 + 13 = x13 + x3 + x13 + x9 + 13 ∧
    ∃ x14 : Nat, x14 + x4 + x14 + x10 + 14 = x14 + x2 + x14 + x8 + 14 ∧
    ∃ x15 : Nat, x15 + x4 + x15 + x10 + 15 = x15 + x1 + x15 + x7 + 15 ∧
    ∃ x16 : Nat, x16 + x4 + x16 + x10 + 16 = x16 + x16 + x16 + x6 + 16 ∧
    ∃ x17 : Nat, x17 + x4 + x17 + x10 + 17 = x17 + x16 + x17 + x5 + 17 ∧
    ∃ x18 : Nat, x18 + x4 + x18 + x10 + 18 = x18 + x16 + x18 + x4 + 18 ∧
    ∃ x19 : Nat, x19 + x4 + x19 + x10 + 19 = x19 + x16 + x19 + x3 + 19 ∧
    ∃ x20 : Nat, x20 + x4 + x20 + x10 + 20 = x20 + x16 + x20 + x2 + 20 ∧
    ∃ x21 : Nat, x21 + x4 + x21 + x10 + 21 = x21 + x16 + x21 + x1 + 21 ∧
    ∃ x22 : Nat, x22 + x4 + x22 + x10 + 22 = x22 + x16 + x22 + x22 + 22 ∧
    ∃ x23 : Nat, x23 + x4 + x23 + x10 + 23 = x23 + x16 + x23 + x22 + 23 ∧
    ∃ x24 : Nat, x24 + x4 + x24 + x10 + 24 = x24 + x16 + x24 + x22 + 24 ∧
    ∃ x25 : Nat, x25 + x4 + x25 + x10 + 25 = x25 + x16 + x25 + x22 + 25 ∧
    ∃ x26 : Nat, x26 + x4 + x26 + x10 + 26 = x26 + x16 + x26 + x22 + 26 ∧
    ∃ x27 : Nat, x27 + x4 + x27 + x10 + 27 = x27 + x16 + x27 + x22 + 27 ∧
    ∃ x28 : Nat, x28 + x4 + x28 + x10 + 28 = x28 + x16 + x28 + x22 + 28 ∧
    ∃ x29 : Nat, x29 + x4 + x29 + x10 + 29 = x29 + x16 + x29 + x22 + 29 ∧
    ∃ x30 : Nat, x30 + x4 + x30 + x10 + 30 = x30 + x16 + x30 + x22 + 30 ∧
    ∃ x31 : Nat, x31 + x4 + x31 + x10 + 31 = x31 + x16 + x31 + x22 + 31 ∧
    ∃ x32 : Nat, x32 + x4 + x32 + x10 + 32 = x32 + x16 + x32 + x22 + 32 ∧
    ∃ x33 : Nat, x33 + x4 + x33 + x10 + 33 = x33 + x16 + x33 + x22 + 33 ∧
    ∃ x34 : Nat, x34 + x4 + x34 + x10 + 34 = x34 + x16 + x34 + x22 + 34 ∧
    ∃ x35 : Nat, x35 + x4 + x35 + x10 + 35 = x35 + x16 + x35 + x22 + 35 ∧
    ∃ x36 : Nat, x36 + x4 + x36 + x10 + 36 = x36 + x16 + x36 + x22 + 36 ∧
    ∃ x37 : Nat, x37 + x4 + x37 + x10 + 37 = x37 + x16 + x37 + x22 + 37 ∧
    ∃ x38 : Nat, x38 + x4 + x38 + x10 + 38 = x38 + x16 + x38 + x22 + 38 ∧
    ∃ x39 : Nat, x39 + x4 + x39 + x10 + 39 = x39 + x16 + x39 + x22 + 39 ∧
    ∃ x40 : Nat, x40 + x4 + x40 + x10 + 40 = x40 + x16 + x40 + x22 + 40

theorem chain_obtain (h : Chain) : Chain := by
  obtain ⟨
    x1, h1, x2, h2, x3, h3, x4, h4, x5, h5, x6, h6, x7, h7, x8, h8, x9, h9, x10, h10, x11, h11,
    x12, h12, x13, h13, x14, h14, x15, h15, x16, h16, x17, h17, x18, h18, x19, h19, x20, h20,
    x21, h21, x22, h22, x23, h23, x24, h24, x25, h25, x26, h26, x27, h27, x28, h28, x29, h29,
    x30, h30, x31, h31, x32, h32, x33, h33, x34, h34, x35, h35, x36, h36, x37, h37, x38, h38,
    x39, h39, x40, h40⟩ := h
  exact ⟨
    x1, h1, x2, h2, x3, h3, x4, h4, x5, h5, x6, h6, x7, h7, x8, h8, x9, h9, x10, h10, x11, h11,
    x12, h12, x13, h13, x14, h14, x15, h15, x16, h16, x17, h17, x18, h18, x19, h19, x20, h20,
    x21, h21, x22, h22, x23, h23, x24, h24, x25, h25, x26, h26, x27, h27, x28, h28, x29, h29,
    x30, h30, x31, h31, x32, h32, x33, h33, x34, h34, x35, h35, x36, h36, x37, h37, x38, h38,
    x39, h39, x40, h40⟩

theorem chain_rcases (h : Chain) : Chain := by
  rcases h with ⟨
    x1, h1, x2, h2, x3, h3, x4, h4, x5, h5, x6, h6, x7, h7, x8, h8, x9, h9, x10, h10, x11, h11,
    x12, h12, x13, h13, x14, h14, x15, h15, x16, h16, x17, h17, x18, h18, x19, h19, x20, h20,
    x21, h21, x22, h22, x23, h23, x24, h24, x25, h25, x26, h26, x27, h27, x28, h28, x29, h29,
    x30, h30, x31, h31, x32, h32, x33, h33, x34, h34, x35, h35, x36, h36, x37, h37, x38, h38,
    x39, h39, x40, h40⟩
  exact ⟨
    x1, h1, x2, h2, x3, h3, x4, h4, x5, h5, x6, h6, x7, h7, x8, h8, x9, h9, x10, h10, x11, h11,
    x12, h12, x13, h13, x14, h14, x15, h15, x16, h16, x17, h17, x18, h18, x19, h19, x20, h20,
    x21, h21, x22, h22, x23, h23, x24, h24, x25, h25, x26, h26, x27, h27, x28, h28, x29, h29,
    x30, h30, x31, h31, x32, h32, x33, h33, x34, h34, x35, h35, x36, h36, x37, h37, x38, h38,
    x39, h39, x40, h40⟩
