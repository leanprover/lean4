import data.nat
open nat

inductive Parity : nat → Type :=
| even : ∀ n : nat, Parity (2 * n)
| odd  : ∀ n : nat, Parity (2 * n + 1)

open Parity

definition parity : Π (n : nat), Parity n
| parity 0     := even 0
| parity (n+1) :=
  begin
    have aux : Parity n, from parity n,
    cases aux with (k, k),
    begin
      apply (odd k)
    end,
    begin
      change (Parity (2*k + 2*1)),
      rewrite -mul.left_distrib,
      apply (even (k+1))
    end
  end

print definition parity

definition half (n : nat) : nat :=
match ⟨n, parity n⟩ with
| ⟨⌞2 * k⌟,     even k⟩ := k
| ⟨⌞2 * k + 1⌟, odd k⟩  := k
end
