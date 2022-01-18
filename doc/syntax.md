# Syntax Extensions

[Lean's syntax](lexical_structure.md) can be extended and customized
by users at every level, ranging from basic "mixfix" notations to
custom elaborators. In fact, all builtin syntax is parsed and
processed using the same mechanisms and APIs open to users. In this
section, we will describe and explain the various extension points.
Significant syntax extensions already builtin into Lean such as the
[`do` notation](./do.md) are described in subsections.

While [introducing new notations](./notation.md) is a relatively rare feature in
programming languages and sometimes even frowned upon because of its
potential to obscure code, it is an invaluable tool in formalization
for expressing established conventions and notations of the respective
field succinctly in code. Going beyond basic notations, Lean's ability
to factor out common boilerplate code into (well-behaved) macros and
to embed entire custom domain specific languages (DSLs) to textually
encode subproblems efficiently and readably can be of great benefit to
both programmers and proof engineers alike.

## Syntax and Macros

## Elaborators

TODO. See [Lean Together 2021: Metaprogramming in Lean
4](https://youtu.be/hxQ1vvhYN_U) for an overview as well [the
continuation](https://youtu.be/vy4JWIiiXSY) about tactic programming.
For more information on antiquotations, see also §4.1 of [Beyond
Notations: Hygienic Macro Expansion for Theorem Proving
Languages](https://arxiv.org/pdf/2001.10490.pdf#page=11).
