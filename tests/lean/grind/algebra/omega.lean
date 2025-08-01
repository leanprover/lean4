-- Comparisons against `omega`:

-- The next three problems are solved by
-- grind_pattern Fin.isLt => Fin.val self
-- but I *think* they should be solved anyway via the `ToInt (Fin n)` instances.

theorem Fin.range_natAdd.extracted_1 (m n : Nat) (i : Fin (m + n)) (hi : m ≤ ↑i) : ↑i - m < n := by
  grind

theorem Fin.image_addNat_Ici.extracted_1 {n : Nat} (m : Nat) (i : Fin n) ⦃j : Fin (n + m)⦄
    (this : ↑i + m ≤ ↑j) : ↑j - m < n := by
  grind

theorem List.find?_ofFn_eq_some.extracted_1 {n : Nat} (i : Fin n) (j : Nat) (hj : j < ↑i) : j < n := by
  grind

-- This one is much slower (~10s in the kernel) than omega (~2s in the kernel).
example {a b c d e f a' b' c' d' e' f' : Int}
  (h₁ : c = a + 3 * b) (h₂ : c' = a' + b') (h₃ : d = 2 * a + 3 * b) (h₄ : d' = 2 * a' + b') (h₅ : e = a + b)
  (h₆ : e' = 3 * a' + b') (h₇ : f = a + 2 * b) (h₈ : f' = 3 * a' + 2 * b')
  (ha :
    a = 0 ∧ a' = 0 ∨
      a = 1 ∧ a' = 1 ∨
        a = -1 ∧ a' = -1 ∨
          a = 1 ∧ a' = 2 ∨
            a = 2 ∧ a' = 1 ∨
              a = -1 ∧ a' = -2 ∨
                a = -2 ∧ a' = -1 ∨ a = 1 ∧ a' = 3 ∨ a = 3 ∧ a' = 1 ∨ a = -1 ∧ a' = -3 ∨ a = -3 ∧ a' = -1)
  (hb :
    b = 0 ∧ b' = 0 ∨
      b = 1 ∧ b' = 1 ∨
        b = -1 ∧ b' = -1 ∨
          b = 1 ∧ b' = 2 ∨
            b = 2 ∧ b' = 1 ∨
              b = -1 ∧ b' = -2 ∨
                b = -2 ∧ b' = -1 ∨ b = 1 ∧ b' = 3 ∨ b = 3 ∧ b' = 1 ∨ b = -1 ∧ b' = -3 ∨ b = -3 ∧ b' = -1)
  (hc :
    c = 0 ∧ c' = 0 ∨
      c = 1 ∧ c' = 1 ∨
        c = -1 ∧ c' = -1 ∨
          c = 1 ∧ c' = 2 ∨
            c = 2 ∧ c' = 1 ∨
              c = -1 ∧ c' = -2 ∨
                c = -2 ∧ c' = -1 ∨ c = 1 ∧ c' = 3 ∨ c = 3 ∧ c' = 1 ∨ c = -1 ∧ c' = -3 ∨ c = -3 ∧ c' = -1)
  (hd :
    d = 0 ∧ d' = 0 ∨
      d = 1 ∧ d' = 1 ∨
        d = -1 ∧ d' = -1 ∨
          d = 1 ∧ d' = 2 ∨
            d = 2 ∧ d' = 1 ∨
              d = -1 ∧ d' = -2 ∨
                d = -2 ∧ d' = -1 ∨ d = 1 ∧ d' = 3 ∨ d = 3 ∧ d' = 1 ∨ d = -1 ∧ d' = -3 ∨ d = -3 ∧ d' = -1)
  (he :
    e = 0 ∧ e' = 0 ∨
      e = 1 ∧ e' = 1 ∨
        e = -1 ∧ e' = -1 ∨
          e = 1 ∧ e' = 2 ∨
            e = 2 ∧ e' = 1 ∨
              e = -1 ∧ e' = -2 ∨
                e = -2 ∧ e' = -1 ∨ e = 1 ∧ e' = 3 ∨ e = 3 ∧ e' = 1 ∨ e = -1 ∧ e' = -3 ∨ e = -3 ∧ e' = -1)
  (hf :
    f = 0 ∧ f' = 0 ∨
      f = 1 ∧ f' = 1 ∨
        f = -1 ∧ f' = -1 ∨
          f = 1 ∧ f' = 2 ∨
            f = 2 ∧ f' = 1 ∨
              f = -1 ∧ f' = -2 ∨
                f = -2 ∧ f' = -1 ∨ f = 1 ∧ f' = 3 ∨ f = 3 ∧ f' = 1 ∨ f = -1 ∧ f' = -3 ∨ f = -3 ∧ f' = -1) :
  a = 0 ∧ b = 0 := by grind (splits := 50)
