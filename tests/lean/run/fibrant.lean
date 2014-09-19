import hott.fibrant
open prod sum fibrant

theorem test_fibrant : fibrant (nat × (nat ⊎ nat))
