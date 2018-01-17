master branch (aka work in progress branch)
-------------

*Features*

* Implement [RFC #1820](https://github.com/leanprover/lean/issues/1820)

* Add `string.iterator` abstraction for traversing strings.
  The VM contains an efficient implementation of this type.

* Add support for non-ASCII char literals. Example: `'α'`.

* Unicode escape characters in string and char literals. For example, `'\u03B1'` is equivalent to `'α'`.

* Predictable runtime cost model for recursive functions. The equation compiler uses
  different techniques for converting recursive equations into recursors and/or
  well-founded fixed points. The new approach used in the code generator ignores
  these encoding tricks when producing byte code. So, the runtime cost model
  is identical to the one in regular strict functional languages.

* Add `d_array n α` (array type where value type may depend on index),
  where (α : fin n → Type u).

* Add instance for `decidable_eq (d_array n α)` and `decidable_eq (array n α)`.
  The new instance is more efficient than the one in mathlib because it doesn't
  convert the array into a list.

* Add aliasing pattern syntax `id@pat`, which introduces the name `id` for the value matched by
  the pattern `pat`.

* Add alternative syntax `{..., ..s}` for the structure update `{s with ...}`.
  Multiple fallback sources can be given: `{..., ..s, ..t}` will fall back to
  searching a field in `s`, then in `t`. The last component can also be `..`,
  which will replace any missing fields with a placeholder.
  The old notation will be removed in the future.

* Add support for structure instance notation `{...}` in patterns. Use `..` to ignore
  unmatched fields.

* Type class `has_equiv` for `≈` notation.

* Add `funext ids*` tactic for applying the funext lemma.

* Add `iterate n { t }` for applying tactic `t` `n` times.
  Remark: `iterate { t }` applies `t` until it fails.

* Add `with_cases { t }`. This tactic applies `t` to the main goal,
  and reverts any new hypothesis in the resulting subgoals. `with_cases` also enable "goal tagging".
  Remark: `induction` and `cases` tag goals using constructor names. `apply` and `constructor` tag goals
  using parameter names. The `case` tactic can select goals using tags.

* Add `cases_matching p` tactic for applying the `cases` tactic to a hypothesis `h : t` s.t.
  `t` matches the pattern `p`. Alternative versions: `cases_matching* p` and `cases_matching [p_1, ..., p_n]`.
  Example: `cases_matching* [_ ∨ _, _ ∧ _]` destructs all conjunctions and disjunctions in the main goal.

* Add `cases_type I` tactic for applying the `cases` tactic to a hypothesis `h : I ...`.
  `cases_type! I` only succeeds when the number of resulting goals is <= 1.
  Alternative versions: `cases_type I_1 ... I_n`, `cases_type* I`, `cases_type!* I`.
  Example: `cases_type* and or` destructs all conjunctions and disjunctions in the main goal.

* Add `constructor_matching p` tactic. It is syntax sugar for `match_target p; constructor`.
  The variant `constructor_matching* p` is more efficient than `focus1 { repeat { match_target p; constructor } }`
  because the patterns are compiled only once.

* `injection h` now supports nested and mutually recursive datatypes.

* Display number of goals in the `*Lean Goal*` buffer (if number of goals > 1).

* `hide id*` command for hiding aliases.
  The following command  hides the alias `is_true` for `decidable.is_true`.
  ```
  hide is_true
  ```

* Add `abbreviation` declaration command. `abbreviation d : t := v` is equivalent to
  `@[reducible, inline] def d : t := v` and a kernel reducibility hint.
  Before this command, we had to use meta programming for setting the kernel reducibility hint.
  This was problematic because we could only define abbreviations after the meta programming
  framework was defined.

* Add "smart unfolding". The idea is to prevent internal compilation details
  used by the equation compiler to "leak" during unification, tactic execution and
  reduction. With "smart unfolding", the term `nat.add a (nat.succ b)` reduces
  to `nat.succ (nat.add a b)` instead of `nat.succ (... incomprehensible mess ...)`.
  This feature addresses a problem reported by many users.
  See [issue #1794](https://github.com/leanprover/lean/issues/1794).
  The command `set_option type_context.smart_unfolding false` disables this feature.

* Add support for "auto params" at `simp` tactic. Example: given
  ```
  @[simp] lemma fprop1 (x : nat) (h : x > 0 . tactic.assumption) : f x = x := ...
  ```
  The simplifier will try to use tactic `assumption` to synthesize parameter `h`.

* Add interactive `sorry` tactic (alias for `admit`).

* `simp` now reduces equalities `c_1 ... = c_2 ...` to `false` if `c_1` and `c_2` are distinct
   constructors. This feature can be disabled using `simp {constructor_eq := ff}`.

* `simp` now reduces equalities `c a_1 ... a_n = c b_1 ... b_n` to `a_1 = b_1 /\ ... /\ a_n = b_n` if `c` is a constructor.
   This feature can be disabled using `simp {constructor_eq := ff}`.

* `subst` and `subst_vars` now support heterogeneous equalities that are actually homogeneous
   (i.e., `@heq α a β b` where `α` and `β` are definitionally equal).

* Add interactive `subst_vars` tactic.

* Add `leanpkg add foo/bar` as a shorthand for `leanpkg add https://github.com/foo/bar`.

* Add `leanpkg help <command>`.

* Add `[norm]` simp set. It contains all lemmas tagged with `[simp]` plus any
  lemma tagged with `[norm]`.
  These rules are used to produce normal forms and/or reduce the
  number of constants used in a goal. For example, we plan to
  add the lemma `f <$> x = x >>= pure ∘ f` to `[norm]`.

*Changes*

* Replace `inout` modifier in type class declarations with `out_param` modifier.
  Reason: counterintuitive behavior in the type class resolution procedure.
  The result could depend on partial information available in the `inout`
  parameter. Now a parameter `(R : inout α → β → Prop)` should be written
  as `(R : out_param (α → β → Prop))` or `(R : out_param $ α → β → Prop)`.
  Remark: users may define their own notation for declaring `out_param`s.
  Example:
  ```
  notation `out`:1024 a:0 := out_param a
  ```
  We did not include this notation in core lib because `out` is frequently used to
  name parameters, local variables, etc.

* `case` tactic now supports the `with_cases { t }` tactic. See entry above about `with_cases`.
  The tag and new hypotheses are now separated with `:`. Example:
  - `case pos { t }`: execute tactic `t` to goal tagged `pos`
  - `case pos neg { t }`: execute tactic `t` to goal tagged `pos neg`
  - `case : x y { t }`: execute tactic `t` to main goal after renaming the first two hypotheses produced by preceding `with_case { t' }`.
  - `case pos neg : x y { t }` : execute tactic `t` to goal tagged `pos neg` after renaming the first two hypotheses produced by preceding `with_case { t' }`.

* `cases h` now also tries to clear `h` when performing dependent elimination.

* `repeat { t }` behavior changed. Now, it applies `t` to each goal. If the application succeeds,
  the tactic is applied recursively to all the generated subgoals until it eventually fails.
  The recursion stops in a subgoal when the tactic has failed to make progress.
  The previous `repeat` tactic was renamed to `iterate`.

* The automatically generated recursor `C.rec` for an inductive datatype
  now uses `ih` to name induction hypotheses instead of `ih_1` if there is only one.
  If there is more than one induction hypotheses, the name is generated by concatenating `ih_`
  before the constructor field name. For example, for the constructor
  ```
  | node (left right : tree) (val : A) : tree
  ```
  The induction hypotheses are now named: `ih_left` and `ih_right`.
  This change only affects tactical proofs where explicit names are not provided
  to `induction` and `cases` tactics.

* `induction h` and `cases h` tactic use a new approach for naming new hypotheses.
   If names are not provided by the user, these tactics will create a "base" name
   by concatenating the input hypothesis name with the constructor field name.
   If there is only one field, the tactic simply reuses the hypothesis name.
   The final name is generated by making sure the "base" name is unique.
   Remarks:
   - If `h` is not a hypothesis, then no concatenation is performed.
   - The old behavior can be obtained by using the following command
   ```
   set_option tactic.induction.concat_names false
   ```
   This change was suggested by Tahina Ramananandro. The idea is to have more
   robust tactic scripts when helper tactics that destruct many hypotheses automatically
   are used.
   Remark: The new `guard_names { t }` tactical can be used to generate
   robust tactic scripts that are not sensitive to naming generation strategies used by `t`.

* Remove `[simp]` attribute from lemmas `or.assoc`, `or.comm`, `or.left_comm`, `and.assoc`, `and.comm`, `and.left_comm`, `add_assoc`, `add_comm`, `add_left_com`, `mul_assoc`, `mul_comm` and `mul_left_comm`.
  These lemmas were being used to "sort" arguments of AC operators: and, or, (+) and (*).
  This was producing unstable proofs. The old behavior can be retrieved by using the commands `local attribute [simp] ...` or `attribute [simp] ...` in the affected files.

* `string` is now a list of unicode scalar values. Moreover, in the VM,
  strings are implemented as an UTF-8 encoded array of bytes.

* `array α n` is now written `array n α`. Motivation: consistency `d_array n α`.

* Move `rb_map` and `rb_tree` to the `native` namespace. We will later add
  pure Lean implementations. Use `open native` to port files.

* `apply t` behavior changed when type of `t` is of the form `forall (a_1 : A_1) ... (a_n : A_n), ?m ...`, where `?m` is an unassigned metavariable.
  In this case, `apply t` behaves as `apply t _ ... _` where `n` `_` have been added, independently of the goal target type.
  The new behavior is useful when using `apply` with eliminator-like definitions.

* `ginduction t with h h1 h2` is now `induction h : t with h1 h2`.

* `apply_core` now also returns the parameter name associated with new metavariables.

* `apply` now also returns the new metavariables (and the parameter name associated with them). Even the assigned metavariables are returned.

* `by_cases p with h` ==> `by_cases h : p`

* leanpkg now always stores .lean package files in a separate `src` directory.

*API name changes*

v3.3.0 (14 September 2017)
-------------

*Features*

* In addition to user-defined notation parsers introduced in Lean 3.2.0, users may now also define top-level commands in Lean. For an example, see the [`coinductive` command](https://github.com/leanprover/lean/blob/814a5edaf172c3835c000e3f631bddd85bd879ab/library/init/meta/coinductive_predicates.lean#L551-L552) that has been ported to the new model.

* Add new simplifier configuration option `simp_config.single_pass`. It is useful for simplification rules that may produce non-termination.
  Example: `simp {single_pass := tt}`

* The rewrite tactic has support for equational lemmas. Example: Given a definition `f`, `rw [f]` will try to rewrite the goal using the equational lemmas for `f`.
  The tactic fails if none of the equational lemmas can be used.

* Add `simp * at *` variant. It acts on all (non dependent propositional) hypotheses.
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

* Non-exhaustive pattern matches now show missing cases.

* `induction e` now also works on non-variable `e`. Unlike `ginduction`, it will not introduce equalities relating `e` to the inductive cases.

* Add notation `#[a, b, c, d]` for `bin_tree.node (bin_tree.node (bin_tree.leaf a) (bin_tree.leaf b)) (bin_tree.node (bin_tree.leaf c) (bin_tree.leaf d))`.
  There is a coercion from `bin_tree` to `list`. The new notation allows to input long sequences efficiently.
  It also prevents system stack overflows.

* Tactics that accept a location parameter, like `rw thm at h`, may now use `⊢` or the ASCII version `|-`
  to select the goal as well as any hypotheses, for example `rw thm at h1 h2 ⊢`.

* Add `user_attribute.after_set/before_unset` handlers that can be used for validation as well as side-effecting attributes.

* Field notation can now be used to make recursive calls.

```
def list.append : list α → list α → list α
| []       l := l
| (h :: s) t := h :: s.append t
```

* leanpkg now stores the intended Lean version in the `leanpkg.toml` file and reports a warning if the version does not match the installed Lean version.

* `simp` and `dsimp` can now unfold let-bindings in the local context.  Use `dsimp [x]` or `simp [x]` to unfold the let-binding `x : nat := 3`.

* User-defined attributes can now take parameters parsed by a `lean.parser`. A `[derive]` attribute that can derive typeclasses such as `decidable_eq` and `inhabited` has been implemented on top of this.

*Changes*

* We now have two type classes for converting to string: `has_to_string` and `has_repr`.
The `has_to_string` type class in v3.2.0 is roughly equivalent to `has_repr`.
For more details, see discussion [here](https://github.com/leanprover/lean/pull/1664).

* Merged `assert` and `note` tactics and renamed -> `have`.

* Renamed `pose` tactic -> `let`

* `assume` is now a real tactic that does not exit tactic mode.

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

* Deleted `simph` and `simp_using_hs` tactics. We should use `simp [*]` instead.

* Use `simp [-h]` and `dsimp [-h]` instead of `simp without h` and `dsimp without h`.
  Moreover, `simp [*, -h]` if `h` is a hypothesis, we are adding all hypotheses but `h`
  as additional simplification lemmas.

* Changed notation `rw [-h]` to `rw [← h]` to avoid confusion with the new `simp [-h]` notation.
  The ASCII version `rw [<- h]` is also supported.

* `rw [t] at *` now skips any hypothesis used by `t`. See discussion [here](https://github.com/leanprover/lean/issues/1813).

* Removed the redundant keywords `take` (replace with `assume`) and `suppose` (replace with the new anonymous `assume :`)

* Universes `max u v + 1` and `imax u v + 1` are now parsed as `(max u v) + 1` and `(imax u v) + 1`.

* Merged `generalize` and `generalize2` tactics into new `generalize id? : expr = id` tactic

* `standard.lean` has been removed. Any files that `import standard` can simply remove the line as
  most things that were once imported by this are now imported by default.

* The type classes for orders have been refactored to combine both the `(<)`
  and `(≤)` operations.  The new classes are `preorder`, `partial_order`, and
  `linear_order`.  The `partial_order` class corresponds to `weak_order`,
  `strict_order`, `order_pair`, and `strong_order_pair`.  The `linear_order`
  class corresponds to `linear_order_pair`, and `linear_strong_order_pair`.

* `injection` and `injections` tactics generate fresh names when user does not provide names.
  The fresh names are of the form `h_<idx>`. See discussion [here](https://github.com/leanprover/lean/issues/1805).

* Use `structure` to declare `and`. This change allows us to use `h.1` and `h.2` as shorthand for `h.left` and `h.right`.

* Add attribute `[pp_using_anonymous_constructor]` to `and`. Now, `and.intro h1 h2` is pretty printed as
  `⟨h1, h2⟩`. This change is motivated by the previous one. Without it, `and.intro h1 h2` would be
  pretty printed as `{left := h1, right := h2}`.

* User attributes can no longer be set with `set_basic_attribute`.  You need to use `user_attribute.set` now.

* The Emacs mode has been moved into its own repository and MELPA packages: https://github.com/leanprover/lean-mode

*API name changes*

* `list.dropn` => `list.drop`
* `list.taken` => `list.take`
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
* `tactic.simp_at` => `tactic.simp_hyp`
* deleted `tactic.simp_at_using`
* deleted `tactic.simph_at`

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

* `option_map` and `option_bind` have been renamed to `option.map` and `option.bind`, respectively.

* GCC 7 compatibility

* Use single quotes for character literals (e.g., 'a').
