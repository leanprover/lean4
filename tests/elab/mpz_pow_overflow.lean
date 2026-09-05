/-!
Regression test for a non-termination in `mpz::pow`, the `Nat.pow` used when
Lean is built with `USE_GMP=OFF`.

Its loop advanced a doubling `unsigned mask` while `mask <= p`. At `mask = 2^31`
the body still ran, and `mask << 1` then overflowed to zero, after which
`0 <= p` held forever, so the call never returned. Both the interpreter and the
kernel reach it: `type_checker::reduce_pow` bounds the exponent only to
`UINT_MAX` and skips its result-size guard when the base is `0` or `1`, which is
exactly the case where the result stays small enough to be worth computing.

These evaluate `Nat.pow` at exponents at or above `2^31`, which used to hang.
-/

#eval (1 : Nat) ^ 2147483648

#eval (0 : Nat) ^ 2147483648

#eval (1 : Nat) ^ 4294967295

#eval (0 : Nat) ^ 4294967295
