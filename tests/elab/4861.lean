/-!
Regression test for #4861: a large polynomial identity leaves many stuck type class problems.
The heartbeat bound fails if they are retried after every default instance again.
-/

set_option maxHeartbeats 10000 in
theorem foo (x y z p q : Int) : False :=
  have : (1 * x ^ 1 + z ^ 1 * p) *
        (1 / 1 * p ^ 1 * x ^ 1 + 1 * q * p ^ 1 * x * z + 1 * q ^ 1 * p ^ 1 * x ^ 1 +
                            1 * q ^ 1 * p ^ 1 * x * z -
                          1 * q * p ^ 1 * y ^ 1 +
                        1 * q ^ 1 * p ^ 1 * x ^ 1 +
                      1 * q ^ 1 * p ^ 1 * x * z -
                    1 * q ^ 1 * p ^ 1 * y ^ 1 +
                  1 * q ^ 1 * p ^ 1 * x ^ 1 +
                1 * q ^ 1 * p ^ 1 * x * z -
              1 * q ^ 1 * p ^ 1 * y ^ 1 +
            1 * q ^ 1 * x ^ 1 -
          1 * q ^ 1 * p * y ^ 1) +
      z * (1 * y) *
        (-(1 / 1 * p ^ 1 * x * y) + 1 * q * p ^ 1 * z * y - 1 * q ^ 1 * p ^ 1 * x * y +
                  1 * q ^ 1 * p ^ 1 * z * y -
                1 * q ^ 1 * p ^ 1 * x * y +
              1 * q ^ 1 * p ^ 1 * z * y -
            1 * q ^ 1 * p ^ 1 * x * y +
          1 / 1 * q ^ 1 * p ^ 1 * z * y) +
    (-y ^ 1 + p * x * (1 * z) + q * (1 * z ^ 1)) *
      (-(1 / 1 * p ^ 1 * x * z) - 1 * q * p ^ 1 * x ^ 1 - 1 * q ^ 1 * p ^ 1 * x * z -
                1 * q ^ 1 * p ^ 1 * x ^ 1 -
              1 * q ^ 1 * p ^ 1 * x * z -
            1 * q ^ 1 * p ^ 1 * x ^ 1 -
          1 * q ^ 1 * p ^ 1 * x * z -
        1 * q ^ 1 * p * x ^ 1) =
  1 *
        (1 / 1 * p ^ 1 * x ^ 1 + 1 * q * p ^ 1 * x * z + 1 * q ^ 1 * p ^ 1 * x ^ 1 +
                            1 * q ^ 1 * p ^ 1 * x * z -
                          1 * q * p ^ 1 * y ^ 1 +
                        1 * q ^ 1 * p ^ 1 * x ^ 1 +
                      1 * q ^ 1 * p ^ 1 * x * z -
                    1 * q ^ 1 * p ^ 1 * y ^ 1 +
                  1 * q ^ 1 * p ^ 1 * x ^ 1 +
                1 * q ^ 1 * p ^ 1 * x * z -
              1 * q ^ 1 * p ^ 1 * y ^ 1 +
            1 * q ^ 1 * x ^ 1 -
          1 * q ^ 1 * p * y ^ 1) +
      1 *
        (-(1 / 1 * p ^ 1 * x * y) + 1 * q * p ^ 1 * z * y - 1 * q ^ 1 * p ^ 1 * x * y +
                  1 * q ^ 1 * p ^ 1 * z * y -
                1 * q ^ 1 * p ^ 1 * x * y +
              1 * q ^ 1 * p ^ 1 * z * y -
            1 * q ^ 1 * p ^ 1 * x * y +
          1 / 1 * q ^ 1 * p ^ 1 * z * y) +
    1 *
      (-(1 / 1 * p ^ 1 * x * z) - 1 * q * p ^ 1 * x ^ 1 - 1 * q ^ 1 * p ^ 1 * x * z -
                1 * q ^ 1 * p ^ 1 * x ^ 1 -
              1 * q ^ 1 * p ^ 1 * x * z -
            1 * q ^ 1 * p ^ 1 * x ^ 1 -
          1 * q ^ 1 * p ^ 1 * x * z -
        1 * q ^ 1 * p * x ^ 1) := sorry
  sorry
