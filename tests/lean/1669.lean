def f : ℕ → ℕ
| a := f a
using_well_founded ⟨{0}, well_founded_tactics.default_dec_tac⟩
