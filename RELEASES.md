v4.0.0-m4 (WIP)
---------

* Support notation `let <pattern> := <expr> | <else-case>` in `do` blocks.

* Remove support for "auto" `pure`. In the [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/for.2C.20unexpected.20need.20for.20type.20ascription/near/269083574), the consensus seemed to be that "auto" `pure` is more confusing than it's worth.

* Remove restriction in `congr` theorems that all function arguments on the left-hand-side must be free variables. For example, the following theorem is now a valid `congr` theorem.
```lean
@[congr]
theorem dep_congr [DecidableEq ι] {p : ι → Set α} [∀ i, Inhabited (p i)] :
                  ∀ {i j} (h : i = j) (x : p i) (y : α) (hx : x = y), Pi.single (f := (p ·)) i x = Pi.single (f := (p ·)) j ⟨y, hx ▸ h ▸ x.2⟩ :=
```

* [Partially applied congruence theorems.](https://github.com/leanprover/lean4/issues/988)

* Improve elaboration postponement heuristic when expected type is a metavariable. Lean now reduces the expected type before performing the test.

* [Remove deprecated leanpkg](https://github.com/leanprover/lean4/pull/985) in favor of [Lake](https://github.com/leanprover/lake) now bundled with Lean.

* Various improvements to go-to-definition & find-all-references accuracy.

* Auto generated congruence lemmas with support for casts on proofs and `Decidable` instances (see [whishlist](https://github.com/leanprover/lean4/issues/988)).

* Rename option `autoBoundImplicitLocal` => `autoImplicit`.

* [Relax auto-implicit restrictions](https://github.com/leanprover/lean4/pull/1011). The command `set_option relaxedAutoImplicit false` disables the relaxations.

* `contradiction` tactic now closes the goal if there is a `False.elim` application in the target.
