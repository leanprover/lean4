# Signatures of V lemmas

The signature of a V lemma should be very consistent with the corresponding proof-taking counterpart or the `!` counterpart. However, there are some complications in the translation.

* Instead of `head`/`head!`, use `headV` (for example) in the statement.
* The `V` operations require a `Nonempty` instance for their return type (so that we can return a garbage value if something's wrong). Other than the proof-taking variants, they don't explicitly take any other kind of proof.
  * `head` takes a proof of `xs \ne []`, `headV` requires a `Nonempty` instance.
* The `V` lemma signatures should not have unnecessary requirements. If only a `Nonempty` instance is needed but the proof-taking counterpart requires a proof of, say, `i < xs.length`, then drop the proof. However, sometimes the proof is necessary to make the statement true. Flag cases in which you are unsure.
* You can test whether a statement even type-checks by using the lean-lsp-mcp to run Lean code.
* When the LHS is, say, `xs.headV`, and there's a `[Nonempty \a]` instance parameter, use `{_ : Nonempty \a}` instead: These lemmas are used by `rw` and `simp`, which will infer the instance by unification with `headV` in this case.
* However, when the theorem is not an equation, Lean won't be able to obtain `Nonempty` by unification. In such cases, use `[Nonempty \a]`.
* `omega` does not work in all files, especially not in the more basic files.
* Use proof non-simp-normal-form parameters such as `i < (l.map f).length` only if you expect them to be inferred by unification of the LHS. Otherwise, use the simp normal form `i < l.length`.
* Whenever an element witness of the right type is available in the signature (e.g., `x : α` being inserted/pushed), prefer `haveI : Nonempty α := ⟨x⟩` over `{_ : Nonempty α}`. This avoids requiring callers to provide a `Nonempty` instance when one can be derived from available data.
* `Classical.ofNonempty : α` always returns the same value regardless of context. This means:
  * For `eraseIdx`-style lemmas: output-side bounds (e.g., `j < n - 1`) can be dropped because both sides return the same `Classical.ofNonempty` out-of-bounds.
  * For `insertIdx`/`push`-style lemmas: bounds must be KEPT because the RHS has a specific value (the inserted element) that differs from `Classical.ofNonempty`.
  * For `zip`-style lemmas: bounds must be KEPT because `Classical.ofNonempty (α × β)` may differ from `(Classical.ofNonempty α, Classical.ofNonempty β)`.
* For product types (`zip`, etc.): prefer `{_ : Nonempty (α × β)}` over separate `{_ : Nonempty α}` and `{_ : Nonempty β}`, because the result type's `getElemV` needs `Nonempty (α × β)` and the product `ofNonempty` may differ from the pair of component `ofNonempty` values.
