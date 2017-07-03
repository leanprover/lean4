master branch (aka work in progress branch)
-------------

*Features*

* In addition to user-defined notation parsers introduced in Lean 3.2.0, users may now also define top-level commands in Lean. For an example, see the [`coinductive` command](https://github.com/leanprover/lean/blob/814a5edaf172c3835c000e3f631bddd85bd879ab/library/init/meta/coinductive_predicates.lean#L551-L552) that has been ported to the new model.

* Add new simplifier configuration option `simp_config.single_pass`. It is useful for simplification rules that may produce non-termination.
  Example: `simp {single_pass := tt}`

* The rewrite tactic has support for equational lemmas. Example: Given a definition `f`, `rw [f]` will try to rewrite the goal using the equational lemmas for `f`.
  The tactic fails if none of the equational lemmas can be used.

* Add `simp_all` tactic. It is similar to `simp`, but acts on all hypotheses.
  Simplified hypotheses are automatically inserted into the simplification set
  as additional simplification rules.

* Add `«id»` notation that can be used to declare and refer to identifiers containing prohibited characters.
  For example, `a.«b.c»` is a two-part identifier with parts `a` and `b.c`.

* `simp` tactic now handles lemmas with metavariables. Example `simp [add_comm _ b]`.

* `conv { ... }` tactic for applying simplification and rewriting steps.
  In the block `{...}`, we can use tactics from `conv.interactive`.
  Examples:
  - `conv at h in (f _ _) { simp }` applies `simp` to first subterm matching `f _ _` at hypothesis `h`.
  - `conv in (_ = _) { to_lhs, whnf }` replace the left-hand-side of the equality in target with its weak-head-normal-form.
  - `conv at h in (0 + _) { rw [zero_add] }`
  - `conv { for (f _ _) [1, 3] {rw [h]}, simp }`, first execute `rw[h]` to the first and third occurrences of an `f`-application,
     and then execute `simp`.

* `simp` tactics in interactive mode have a new configuration parameter (`discharger : tactic unit`)
   a tactic for discharging subgoals created by the simplifier. If the tactic fails, the simplifier
   tries to discharge the subgoal by reducing it to `true`.
   Example: `simp {discharger := assumption}`.

* `simp` and `dsimp` can be used to unfold projection applications when the argument is a type class instance.
   Example: `simp [has_add.add]` will replace `@has_add.add nat nat.has_add a b` with `nat.add a b`

* `dsimp` has several new configuration options to control reduction (e.g., `iota`, `beta`, `zeta`, ...).

*Changes*

* We now have two type classes for converting to string: `has_to_string` and `has_repr`.
The `has_to_string` type class in v3.2.0 is roughly equivalent to `has_repr`.
For more details, see discussion [here](https://github.com/leanprover/lean/pull/1664).

* Merged `assert` and `note` tactics and renamed -> `have`.

* Renamed `pose` tactic -> `let`

* `assume` and `suppose` are now real tactics that do not exit tactic mode.

* Modified `apply` tactic configuration object, and implemented [RFC #1342](https://github.com/leanprover/lean/issues/1342). It now has support for `auto_param` and `opt_param`. The new `eapply` tactic only creates subgoals for non dependent premises, and it simulates the behavior of the `apply` tactic in version 3.2.0.

* Add configuration object `rewrite_cfg` to `rw`/`rewrite` tactic. It now has support for `auto_param` and `opt_param`.
  The new goals are ordered using the same strategies available for `apply`.

* All `dsimp` tactics fail if they did not change anything.
  We can simulate the v3.2.0 using `dsimp {fail_if_unchaged := ff}` or `try dsimp`.

* `dsimp` does not unfold reducible definitions by default anymore.
  Example: `function.comp` applications will not be unfolded by default.
  We should use `dsimp [f]` if we want to reduce a reducible definition `f`.
  Another option is to use the new configuration parameter `unfold_reducible`.
  Example `dsimp {unfold_reducible := tt}`

* All `dunfold` and `unfold` tactics fail if they did not unfold anything.
  We can simulate the v3.2.0 using `unfold f {fail_if_unchaged := ff}` or `try {unfold f}`.

* `dunfold_occs` was deleted, the new `conv` tactical should be used instead.

* `unfold` tactic is now implemented on top of the `simp` tactics. So, we can use it to unfold
   declarations defined using well founded recursion. The `unfold1` variant does not unfold recursively,
   and it is shorthand for `unfold f {single_pass := tt}`.
   Remark: in v3.2.0, `unfold` was just an alias for the `dunfold` tactic.

*API name changes*

* `tactic.dsimp` and `tactic.dsimp_core` => `tactic.dsimp_target`
* `tactic.dsimp_at_core` and `tactic.dsimp_at` => `tactic.dsimp_hyp`
* `tactic.delta_expr` => `tactic.delta`
* `tactic.delta` => `tactic.delta_target`
* `tactic.delta_at` => `tactic.delta_hyp`
* `tactic.simplify_goal` => `tactic.simp_target`
* `tactic.unfold_projection` => `tactic.unfold_proj`
* `tactic.unfold_projections_core` => `tactic.unfold_projs`
* `tactic.unfold_projections` => `tactic.unfold_projs_target`
* `tactic.unfold_projections_at` => `tactic.unfold_projs_hyp`
* `tactic.simp_intros_using`, `tactic.simph_intros_using`, `tactic.simp_intro_lst_using`, `tactic.simph_intro_lst_using` => `tactic.simp_intros`

v3.2.0 (18 June 2017)
-------------

Lean is still evolving rapidly, and we apologize for the resulting instabilities. The lists below summarizes some of the new features and incompatibilities with respect to release 3.1.0.

*Features*

* Holes `{! ... !}` expressions and (user-defined) hole commands.
In Emacs, hole commands are executed using the keybinding C-c SPC.
The available commands can be found [here](https://github.com/leanprover/lean/blob/master/library/init/meta/hole_command.lean).

* The `leanpkg` package manager now manages projects and dependencies. See the documentation [here](https://github.com/leanprover/lean/tree/master/leanpkg). Parts of the standard library, like the superposition theorem prover `super`, have been moved to their own repositories. `.project` files are no longer needed to use `emacs` with projects.

* Well-founded recursion is now supported. (Details and examples for this and the next two items will soon appear in _Theorem Proving in Lean_.)

* Mutually (non meta) recursive definitions are now supported.

* Nested and mutual inductive data types are now supported.

* There is support for coinductive predicates.

* The `simp` tactic has been improved and supports more options, like wildcards. Hover over `simp` in an editor to see the documentation string (docstring).

* Additional interactive tactics have been added, and can be found [here](https://github.com/leanprover/lean/blob/master/library/init/meta/interactive.lean).

* A `case` tactic can now be used to structure proofs by cases and by induction. See [here](https://github.com/leanprover/lean/pull/1515).

* Various data structures, such as hash maps, have been added to the standard library [here](https://github.com/leanprover/lean/tree/master/library/data).

* There is preliminary support for user-defined parser extensions. More information can be found [here](https://github.com/leanprover/lean/pull/1617), and some examples can be found [here](https://github.com/leanprover/lean/blob/814a5edaf172c3835c000e3f631bddd85bd879ab/library/init/meta/interactive_base.lean#L184-L215).

* Numerous improvements have been made to the parallel compilation infrastructure and editor interfaces, for example, as described [here](https://github.com/leanprover/lean/pull/1405) and [here](https://github.com/leanprover/lean/pull/1534).

* There is a `transfer` method that can be used to transfer results e.g. to isomorphic structures; see [here](https://github.com/leanprover/lean/pull/1435).

* The monadic hierarchy now includes axioms for monadic classes. (See [here](https://github.com/leanprover/lean/pull/1485).)

* The tactic notation `tac ; [tac_1, ..., tac_n]` has been added.

* The type classes `has_well_founded`, `has_map`, `has_seq`, `has_orelse` have been added.

* Type classes can have input/output parameters. Some examples can be found [here](https://github.com/leanprover/lean/blob/master/library/init/core.lean).

* `tactic.run_io` can now be used to perform IO in tactics.

*Changes*

* Type class instances are not `[reducible]` by default anymore.

* Commands that produce output are now preceded by a hash symbol, as in `#check`, `#print`, `#eval` and `#reduce`. The `#eval` command calls the bytecode evaluator, and `#reduce` does definitional reduction in the kernel. Many instances of alternative syntax like `premise` for `variable` and `hypothesis` for `parameter` have been eliminated. See the discussion [here](https://github.com/leanprover/lean/issues/1432).

* The hierarchy of universes is now named `Sort 0`, `Sort 1`, `Sort 2`, and so on. `Prop` is alternative syntax for `Sort 0`, `Type` is alternative syntax for `Sort 1`, and `Type n` is alternative syntax for `Sort (n + 1)`. Many general constructors have been specialized from arbitrary `Sort`s to `Type` in order to simplify elaboration.

* Automatically generate dependent eliminators for inductive predicates.

* Improve unification hint matcher.

* Improve unifier. In function applications, explicit arguments are unified before implicit ones.
  Moreover, more aggresive unfolding is used when processing implicit arguments.

* Use `universe u` instead of `universe variable u` to declare a universe variable.

* The syntax `l^.map f` for projections is now deprecated in favor of `l.map f`.

* The behavior of the `show` tactic in interactive tactic mode has changed. It no longer leaves tactic mode. Also, it can now be used to select a goal other than the current one.

* The `assertv` and `definev` tactics have been eliminated in favor of `note` and `pose`.

* `has_andthen` type class is now heterogeneous,

* The encoding of structures has been changed, following the strategy described [here](https://github.com/leanprover/lean/wiki/Refactoring-structures). Generic operations like `add` and `mul` are replaced by `has_add.add` and `has_mul.mul`, respectively. One can provisionally obtain the old encodings with `set_option old_structure_cmd true
`.

* Syntax for quotations in metaprograms has changed. The notation `` `(t)`` elaborates `t` at definition time and produces an expression. The notation ``` ``(t) ``` resolves names at definition time produces a pre-expression, and ```` ```(t)```` resolves names at tactic execution time, and produces a pre-expression. Details can be found in the paper Ebner et al, _A Metaprogramming Framework for Formal Verification_.

* The types `expr` for expressions and `pexpr` for pre-expressions have been unified, so that `pexpr` is defined as `expr ff`. See [here](https://github.com/leanprover/lean/pull/1580).

* Handling of the `io` monad has changed. Examples can be found [here](https://github.com/leanprover/lean/tree/master/leanpkg/leanpkg) in the code for `leanpkg`, which is written in Lean itself.

- `state` and `state_t` are universe polymorphic.

* GCC 7 compatibility

* Use single quotes for character literals (e.g., 'a').
