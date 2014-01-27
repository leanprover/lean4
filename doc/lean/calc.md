Calculational Proofs
====================

A calculational proof is just a chain of intermediate results that are
meant to be composed by basic principles such as the transitivity of
`=`. In Lean, a calculation proof starts with the keyword `calc`, and has
the following syntax

        calc  <expr>_0  'op_1'  <expr>_1  ':'  <proof>_1
                '...'   'op_2'  <expr>_2  ':'  <proof>_2
          ...
                '...'   'op_n'  <expr>_n  ':'  <proof>_n

Each `<proof>_i` is a proof for `<expr>_{i-1} op_i <expr>_i`.
Recall that proofs are also expressions in Lean. The `<proof>_i`
may also be of the form `{ <pr> }`, where `<pr>` is a proof
for some equality `a = b`. The form `{ <pr> }` is just syntax sugar
for

          subst (refl <expr>_{i-1}) <pr>

That is, we are claiming we can obtain `<expr>_i` by replacing `a` with `b`
in `<expr>_{i-1}`.

Here is an example

```lean
        variables a b c d e : Nat.
        axiom Ax1 : a = b.
        axiom Ax2 : b = c + 1.
        axiom Ax3 : c = d.
        axiom Ax4 : e = 1 + d.

        theorem T : a = e
        := calc a    =  b     : Ax1
                ...  =  c + 1 : Ax2
                ...  =  d + 1 : { Ax3 }
                ...  =  1 + d : Nat::add_comm d 1
                ...  =  e     : symm Ax4.
```

The proof expressions `<proof>_i` do not need to be explicitly provided.
We can use `by <tactic>` or `by <solver>` to (try to) automatically construct the
proof expression using the given tactic or solver.

Even when tactics and solvers are not used, we can still use the elaboration engine to fill
gaps in our calculational proofs. In the previous examples, we can use `_` as arguments for the
`Nat::add_comm` theorem. The Lean elaboration engine will infer `d` and `1` for us.
Here is the same example using placeholders.

```lean
        theorem T' : a = e
        := calc a    =  b     : Ax1
                ...  =  c + 1 : Ax2
                ...  =  d + 1 : { Ax3 }
                ...  =  1 + d : Nat::add_comm _ _
                ...  =  e     : symm Ax4.
```

We can also use the operators `=>`, `⇒`, `<=>`, `⇔` and `≠` in calculational proofs.
Here is an example.

```lean
       theorem T2 (a b c : Nat) (H1 : a = b) (H2 : b = c + 1) : a ≠ 0
       := calc  a = b      : H1
              ... = c + 1  : H2
              ... ≠ 0      : Nat::succ_nz _.
```

The Lean `let` construct can also be used to build calculational-like proofs.

```lean
      variable P : Nat → Nat → Bool.
      variable f : Nat → Nat.
      axiom Axf (a : Nat) : f (f a) = a.

      theorem T3 (a b : Nat) (H : P (f (f (f (f a)))) (f (f b))) : P a b
      := let s1 : P (f (f a)) (f (f b))   :=   subst H  (Axf a),
             s2 : P a (f (f b))           :=   subst s1 (Axf a),
             s3 : P a b                   :=   subst s2 (Axf b)
         in s3.
```

Finally, the [Nat (natural number) builtin library](../../src/builtin/Nat.lean) makes extensive use of calculational proofs.

The Lean simplifier can be used to reduce the size of calculational proofs.
In the following example, we create a rewrite rule set with basic theorems from the Natural number library, and some of the axioms
declared above.

```lean
       import tactic
       rewrite_set simple
       add_rewrite Nat::add_comm Nat::add_assoc Nat::add_left_comm Ax1 Ax2 Ax3 eq_id : simple
       theorem T'' : a = e
        := calc a    =  1 + d : (by simp simple)
                ...  =  e     : symm Ax4
```
