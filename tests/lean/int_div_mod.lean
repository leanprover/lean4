-- Divide by zero tests
#guard ( 0 : Int) / 0 = 0
#guard ( 0 : Int) % 0 == 0
#guard ( 4 : Int) / 0 == 0
#guard ( 4 : Int) % 0 == 4
#guard (-4 : Int) / 0 == 0
#guard (-4 : Int) % 0 == -4
#guard ( 0 : Int) /  4 == 0
#guard ( 0 : Int) %  4 == 0
#guard ( 0 : Int) / -4 == 0
#guard ( 0 : Int) % -4 == 0

-- Euclidean division tests
#guard ( 4 : Int) / 3 == 1
#guard ( 4 : Int) % 3 == 1
#guard ( 5 : Int) / 3 == 1
#guard ( 5 : Int) % 3 == 2
#guard ( 6 : Int) / 3 == 2
#guard ( 6 : Int) % 3 == 0
#guard ( 7 : Int) / 4 == 1
#guard ( 7 : Int) % 4 == 3

#guard ( 4 : Int) / -3 == -1
#guard ( 4 : Int) % -3 == 1
#guard ( 5 : Int) / -3 == -1
#guard ( 5 : Int) % -3 == 2
#guard ( 6 : Int) / -3 == -2
#guard ( 6 : Int) % -3 == 0
#guard ( 7 : Int) / -4 == -1
#guard ( 7 : Int) % -4 == 3

#guard (-4 : Int) / 3 == -2
#guard (-4 : Int) % 3 == 2
#guard (-5 : Int) / 3 == -2
#guard (-5 : Int) % 3 == 1
#guard (-6 : Int) / 3 == -2
#guard (-6 : Int) % 3 == 0
#guard (-7 : Int) / 4 == -2
#guard (-7 : Int) % 4 == 1

#guard (-4 : Int) / -3 == 2
#guard (-4 : Int) % -3 == 2
#guard (-5 : Int) / -3 == 2
#guard (-5 : Int) % -3 == 1
#guard (-6 : Int) / -3 == 2
#guard (-6 : Int) % -3 == 0
#guard (-7 : Int) / -4 == 2
#guard (-7 : Int) % -4 == 1

-- Basic big integer tests
#guard let n : Int := 0;  let d : Int :=  2^64; n / d = 0 ∧ n % d = n
#guard let n : Int := 1;  let d : Int :=  2^64; n / d = 0 ∧ n % d = n
#guard let n : Int := -1; let d : Int :=  2^64; n / d = -1 ∧ n % d = (d + n)
#guard let n : Int := 2^128;  let d : Int :=  3;    d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d
#guard let n : Int := 2^128;  let d : Int :=  2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d
#guard let n : Int := -2^128; let d : Int :=  2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d
#guard let n : Int := 2^128;  let d : Int := -2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d.natAbs
#guard let n : Int := -2^128; let d : Int := -2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d.natAbs
#guard let n : Int := 2^128+7;  let d : Int :=  2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d
#guard let n : Int := -2^128+3; let d : Int :=  2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d
#guard let n : Int := 2^128+2;  let d : Int := -2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d.natAbs
#guard let n : Int := -2^128+2; let d : Int := -2^64; d * (n / d) + n % d = n ∧ n % d ≥ 0 ∧ n % d < d.natAbs
