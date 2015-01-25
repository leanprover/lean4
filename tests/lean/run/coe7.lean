import logic
namespace experiment
constant nat : Type.{1}
constant int : Type.{1}
constant of_nat : nat → int
attribute of_nat [coercion]

theorem tst (n : nat) : n = n :=
have H : true, from trivial,
calc n    = n : eq.refl _
      ... = n : eq.refl _
end experiment
