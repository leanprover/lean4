example {x : BitVec 2} : x - 2 * x + x = 0 := by
  grind -- succeeds

example {x : BitVec 2} : x - 2 • x + x = 0 := by
  grind -- fails

-- There are several independent problems here!

-- 1. Cutsat doesn't evaluate `2 ^ 2`:
-- [cutsat] Assignment satisfying linear constraints
-- [assign] 「2 ^ 2」 := 0

-- 2. We don't normalize `3 * 2 • x` to `6 * x` in the ring solver:
-- [ring] Rings ▼
--   [] Ring `BitVec 2` ▼
--     [diseqs] Disequalities ▼
--       [_] ¬2 * x + 3 * 2 • x = 0
-- This should then give a contradiction because the characteristic of `BitVec 2` is 4.

-- 3. In `Int`, we're not normalizing `*` and `•`:
-- [ring] Rings ▼
--   [] Ring `Int` ▼
--     [basis] Basis ▼
--       [_] 2 * ↑x + -1 * ↑(2 • x) + -4 * ((2 * ↑x + -1 * ↑(2 • x)) / 4) + -1 * ((2 * ↑x + -1 * ↑(2 • x)) % 4) = 0
