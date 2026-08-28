-- Solution's hole has a different type; should be rejected even though the
-- theorem body is `sorry`.
def n : Int := 17

theorem foo : 17 + 17 = 34 := sorry
