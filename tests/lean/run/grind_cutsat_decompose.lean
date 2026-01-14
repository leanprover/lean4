module
example (n : Int) : n = 1000 * (n / 1000) + 100 * ((n / 100) % 10) + 10 * ((n / 10) % 10) + n % 10 := by
  grind
