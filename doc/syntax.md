# Syntax Extensions

Lean's syntax can be extended and customized
by users at every level, ranging from [basic "mixfix" notations](./notation.md)
over [macro transformers](./macro_overview.md) to
[type-aware elaborators](./elaborators.md). In fact, all builtin syntax is parsed and
processed using the same mechanisms and APIs open to users. In this
section, we will describe and explain the various extension points.
Significant syntax extensions already builtin into Lean such as the
[`do` notation](./do.md) are described in subsections.

While introducing new syntax is a relatively rare feature in
programming languages and sometimes even frowned upon because of its
potential to obscure code, it is an invaluable tool in formalization
for expressing established conventions and notations of the respective
field succinctly in code. Going beyond basic notations, Lean's ability
to factor out common boilerplate code into (well-behaved) macros and
to embed entire custom domain specific languages (DSLs) to textually
encode subproblems efficiently and readably can be of great benefit to
both programmers and proof engineers alike.
