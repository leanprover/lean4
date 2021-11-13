# Metaprogramming

Macros are a language feature that allows writing code that writes other code (metaprogramming).

In Lean 4, macros are used pervasively. So much so that core language features such as `do` notation
is implemented via macros! As a language user, macros are useful to easily
embed domain-specific languages and to generate code at compile-time, to name a few uses.

## References
- [Hygenic Macro Expansion for Theorem Proving Languages](https://arxiv.org/abs/2001.10490)
