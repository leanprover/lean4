import data.nat
open nat eq.ops

theorem lcm_dvd {m n k : nat} (H1 : m ∣ k) (H2 : (n ∣ k)) : (lcm m n ∣ k) :=
match eq_zero_or_pos k with
| @or.inl _ _ kzero :=
    begin
      rewrite kzero,
      apply dvd_zero
    end
| @or.inr _ _ kpos  :=
    obtain (p : nat) (km : k = m * p), from exists_eq_mul_right_of_dvd H1,
    obtain (q : nat) (kn : k = n * q), from exists_eq_mul_right_of_dvd H2,
    begin
      have mpos : m > 0, from pos_of_dvd_of_pos H1 kpos,
      have npos : n > 0, from pos_of_dvd_of_pos H2 kpos,
      have gcd_pos : gcd m n > 0, from gcd_pos_of_pos_left n mpos,
      have ppos : p > 0,
        begin
          apply pos_of_mul_pos_left,
          apply (eq.rec_on km),
          exact kpos
        end,
      have qpos : q > 0, from pos_of_mul_pos_left (kn ▸ kpos),
      have H3 : p * q * (m * n * gcd p q) = p * q * (gcd m n * k),
        begin
          apply sorry
        end,
      have H4 : m * n * gcd p q = gcd m n * k, from
        !eq_of_mul_eq_mul_left (mul_pos ppos qpos) H3,
      have H5 : gcd m n * (lcm m n * gcd p q) = gcd m n * k,
        begin
          rewrite [-mul.assoc, gcd_mul_lcm],
          exact H4
        end,
      have H6 : lcm m n * gcd p q = k, from
        !eq_of_mul_eq_mul_left gcd_pos H5,
      exact (dvd.intro H6)
    end
end
