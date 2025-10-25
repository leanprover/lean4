opaque p : α → Int → Int → Prop

#guard_msgs (drop error, trace) in
example :
  a₁ ≥ 0 → a₂ ≥ 0 → a₃ ≥ 0 → a₄ ≥ 0 → a₅ ≥ 0 → a₆ ≥ 0 → a₇ ≥ 0 → a₈ ≥ 0 →
    p true a₁ a₂ → p 1 a₃ a₄ → p 'a' a₅ a₆ → p "" a₇ a₈ → False := by
  set_option trace.grind.split true in -- mbtc should not produce any case split
  grind
