# Lean 4 releases

We intend to provide regular "minor version" releases of the Lean language at approximately monthly intervals.
There is not yet a strong guarantee of backwards compatibility between versions,
only an expectation that breaking changes will be documented in this file.

This file contains work-in-progress notes for the upcoming release, as well as previous stable releases.
Please check the [releases](https://github.com/leanprover/lean4/releases) page for the current status
of each version.

v4.3.0
---------

* `simp [f]` does not unfold partial applications of `f` anymore. See issue [#2042](https://github.com/leanprover/lean4/issues/2042).
  To fix proofs affected by this change, use `unfold f` or `simp (config := { unfoldPartialApp := true }) [f]`.
* By default, `simp` will no longer try to use Decidable instances to rewrite terms. In particular, not all decidable goals will be closed by `simp`, and the `decide` tactic may be useful in such cases. The `decide` simp configuration option can be used to locally restore the old `simp` behavior, as in `simp (config := {decide := true})`; this includes using Decidable instances to verify side goals such as numeric inequalities.

* Many bug fixes:
  * [Add left/right actions to term tree coercion elaborator and make `^`` a right action](https://github.com/leanprover/lean4/pull/2778)
  * [Fix for #2775, don't catch max recursion depth errors](https://github.com/leanprover/lean4/pull/2790)
  * [Reduction of `Decidable` instances very slow when using `cases` tactic](https://github.com/leanprover/lean4/issues/2552)
  * [`simp` not rewriting in binder](https://github.com/leanprover/lean4/issues/1926)
  * [`simp` unfolding `let` even with `zeta := false` option](https://github.com/leanprover/lean4/issues/2669)
  * [`simp` (with beta/zeta disabled) and discrimination trees](https://github.com/leanprover/lean4/issues/2281)
  * [unknown free variable introduced by `rw ... at h`](https://github.com/leanprover/lean4/issues/2711)
  * [`dsimp` doesn't use `rfl` theorems which consist of an unapplied constant](https://github.com/leanprover/lean4/issues/2685)
  * [`dsimp` does not close reflexive equality goals if they are wrapped in metadata](https://github.com/leanprover/lean4/issues/2514)
  * [`rw [h]` uses `h` from the environment in preference to `h` from the local context](https://github.com/leanprover/lean4/issues/2729)
  * [missing `withAssignableSyntheticOpaque` for `assumption` tactic](https://github.com/leanprover/lean4/issues/2361)
  * [ignoring default value for field warning](https://github.com/leanprover/lean4/issues/2178)
* [Cancel outstanding tasks on document edit in the language server](https://github.com/leanprover/lean4/pull/2648).
* [Remove unnecessary `%` operations in `Fin.mod` and `Fin.div`](https://github.com/leanprover/lean4/pull/2688)
* [Avoid `DecidableEq` in `Array.mem`](https://github.com/leanprover/lean4/pull/2774)
* [Ensure `USize.size` unifies with `?m + 1`](https://github.com/leanprover/lean4/issues/1926)
* [Improve compatibility with emacs eglot client](https://github.com/leanprover/lean4/pull/2721)

**Lake:**

* [Sensible defaults for `lake new MyProject math`](https://github.com/leanprover/lean4/pull/2770)
* Changed `postUpdate?` configuration option to a `post_update` declaration. See the `post_update` syntax docstring for more information on the new syntax.
* [A manifest is automatically created on workspace load if one does not exists.](https://github.com/leanprover/lean4/pull/2680).
* The `:=` syntax for configuration declarations (i.e., `package`, `lean_lib`, and `lean_exe`) has been deprecated. For example, `package foo := {...}` is deprecated.
* [support for overriding package URLs via `LAKE_PKG_URL_MAP`](https://github.com/leanprover/lean4/pull/2709)
* Moved the default build directory (e.g., `build`), default packages directory (e.g., `lake-packages`), and the compiled configuration (e.g., `lakefile.olean`) into a new dedicated directory for Lake outputs, `.lake`. The cloud release build archives are also stored here, fixing [#2713](https://github.com/leanprover/lean4/issues/2713).
* Update manifest format to version 7 (see [lean4#2801](https://github.com/leanprover/lean4/pull/2801) for details on the changes).
* Deprecate the `manifestFile` field of a package configuration.
* There is now a more rigorous check on `lakefile.olean` compatibility (see [#2842](https://github.com/leanprover/lean4/pull/2842) for more details).


v4.2.0
---------

* [isDefEq cache for terms not containing metavariables.](https://github.com/leanprover/lean4/pull/2644).
* Make [`Environment.mk`](https://github.com/leanprover/lean4/pull/2604) and [`Environment.add`](https://github.com/leanprover/lean4/pull/2642) private, and add [`replay`](https://github.com/leanprover/lean4/pull/2617) as a safer alternative.
* `IO.Process.output` no longer inherits the standard input of the caller.
* [Do not inhibit caching](https://github.com/leanprover/lean4/pull/2612) of default-level `match` reduction.
* [List the valid case tags](https://github.com/leanprover/lean4/pull/2629) when the user writes an invalid one.
* The derive handler for `DecidableEq` [now handles](https://github.com/leanprover/lean4/pull/2591) mutual inductive types.
* [Show path of failed import in Lake](https://github.com/leanprover/lean4/pull/2616).
* [Fix linker warnings on macOS](https://github.com/leanprover/lean4/pull/2598).
* **Lake:** Add `postUpdate?` package configuration option. Used by a package to specify some code which should be run after a successful `lake update` of the package or one of its downstream dependencies. ([lake#185](https://github.com/leanprover/lake/issues/185))
* Improvements to Lake startup time ([#2572](https://github.com/leanprover/lean4/pull/2572), [#2573](https://github.com/leanprover/lean4/pull/2573))
* `refine e` now replaces the main goal with metavariables which were created during elaboration of `e` and no longer captures pre-existing metavariables that occur in `e` ([#2502](https://github.com/leanprover/lean4/pull/2502)).
  * This is accomplished via changes to `withCollectingNewGoalsFrom`, which also affects `elabTermWithHoles`, `refine'`, `calc` (tactic), and `specialize`. Likewise, all of these now only include newly-created metavariables in their output.
  * Previously, both newly-created and pre-existing metavariables occurring in `e` were returned inconsistently in different edge cases, causing duplicated goals in the infoview (issue [#2495](https://github.com/leanprover/lean4/issues/2495)), erroneously closed goals (issue [#2434](https://github.com/leanprover/lean4/issues/2434)), and unintuitive behavior due to `refine e` capturing previously-created goals appearing unexpectedly in `e` (no issue; see PR).

v4.1.0
---------

* The error positioning on missing tokens has been [improved](https://github.com/leanprover/lean4/pull/2393). In particular, this should make it easier to spot errors in incomplete tactic proofs.

* After elaborating a configuration file, Lake will now cache the configuration to a `lakefile.olean`. Subsequent runs of Lake will import this OLean instead of elaborating the configuration file. This provides a significant performance improvement (benchmarks indicate that using the OLean cuts Lake's startup time in half), but there are some important details to keep in mind:
  + Lake will regenerate this OLean after each modification to the `lakefile.lean` or `lean-toolchain`. You can also force a reconfigure by passing the new `--reconfigure` / `-R` option to `lake`.
  + Lake configuration options (i.e., `-K`) will be fixed at the moment of elaboration. Setting these options when `lake` is using the cached configuration will have no effect. To change options, run `lake` with `-R` / `--reconfigure`.
  + **The `lakefile.olean` is a local configuration and should not be committed to Git. Therefore, existing Lake packages need to add it to their `.gitignore`.**

* The signature of `Lake.buildO` has changed, `args` has been split into `weakArgs` and `traceArgs`. `traceArgs` are included in the input trace and `weakArgs` are not. See Lake's [FFI example](src/lake/examples/ffi/lib/lakefile.lean) for a demonstration of how to adapt to this change.

* The signatures of `Lean.importModules`, `Lean.Elab.headerToImports`, and `Lean.Elab.parseImports`
  have [changed](https://github.com/leanprover/lean4/pull/2480) from taking `List Import` to `Array Import`.

* There is now [an `occs` field](https://github.com/leanprover/lean4/pull/2470)
  in the configuration object for the `rewrite` tactic,
  allowing control of which occurrences of a pattern should be rewritten.
  This was previously a separate argument for `Lean.MVarId.rewrite`,
  and this has been removed in favour of an additional field of `Rewrite.Config`.
  It was not previously accessible from user tactics.

v4.0.0
---------

* [`Lean.Meta.getConst?` has been renamed](https://github.com/leanprover/lean4/pull/2454).
  We have renamed `getConst?` to `getUnfoldableConst?` (and `getConstNoEx?` to `getUnfoldableConstNoEx?`).
  These were not intended to be part of the public API, but downstream projects had been using them
  (sometimes expecting different behaviour) incorrectly instead of `Lean.getConstInfo`.

* [`dsimp` / `simp` / `simp_all` now fail by default if they make no progress](https://github.com/leanprover/lean4/pull/2336).

  This can be overridden with the `(config := { failIfUnchanged := false })` option.
  This change was made to ease manual use of `simp` (with complicated goals it can be hard to tell if it was effective)
  and to allow easier flow control in tactics internally using `simp`.
  See the [summary discussion](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/simp.20fails.20if.20no.20progress/near/380153295)
  on zulip for more details.

* [`simp_all` now preserves order of hypotheses](https://github.com/leanprover/lean4/pull/2334).

  In order to support the `failIfUnchanged` configuration option for `dsimp` / `simp` / `simp_all`
  the way `simp_all` replaces hypotheses has changed.
  In particular it is now more likely to preserve the order of hypotheses.
  See [`simp_all` reorders hypotheses unnecessarily](https://github.com/leanprover/lean4/pull/2334).
  (Previously all non-dependent propositional hypotheses were reverted and reintroduced.
  Now only such hypotheses which were changed, or which come after a changed hypothesis,
  are reverted and reintroduced.
  This has the effect of preserving the ordering amongst the non-dependent propositional hypotheses,
  but now any dependent or non-propositional hypotheses retain their position amongst the unchanged
  non-dependent propositional hypotheses.)
  This may affect proofs that use `rename_i`, `case ... =>`, or `next ... =>`.

* [New `have this` implementation](https://github.com/leanprover/lean4/pull/2247).

  `this` is now a regular identifier again that is implicitly introduced by anonymous `have :=` for the remainder of the tactic block. It used to be a keyword that was visible in all scopes and led to unexpected behavior when explicitly used as a binder name.

* [Show typeclass and tactic names in profile output](https://github.com/leanprover/lean4/pull/2170).

* [Make `calc` require the sequence of relation/proof-s to have the same indentation](https://github.com/leanprover/lean4/pull/1844),
  and [add `calc` alternative syntax allowing underscores `_` in the first relation](https://github.com/leanprover/lean4/pull/1844).

  The flexible indentation in `calc` was often used to align the relation symbols:
  ```lean
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc
        (x + y) * (x + y) = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
                        -- improper indentation
                        _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
                        _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
                        _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
  ```

  This is no longer legal.  The new syntax puts the first term right after the `calc` and each step has the same indentation:
  ```lean
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc (x + y) * (x + y)
      _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
  ```


* Update Lake to latest prerelease.

* [Make go-to-definition on a typeclass projection application go to the instance(s)](https://github.com/leanprover/lean4/pull/1767).

* [Include timings in trace messages when `profiler` is true](https://github.com/leanprover/lean4/pull/1995).

* [Pretty-print signatures in hover and `#check <ident>`](https://github.com/leanprover/lean4/pull/1943).

* [Introduce parser memoization to avoid exponential behavior](https://github.com/leanprover/lean4/pull/1799).

* [feat: allow `doSeq` in `let x <- e | seq`](https://github.com/leanprover/lean4/pull/1809).

* [Add hover/go-to-def/refs for options](https://github.com/leanprover/lean4/pull/1783).

* [Add empty type ascription syntax `(e :)`](https://github.com/leanprover/lean4/pull/1797).

* [Make tokens in `<|>` relevant to syntax match](https://github.com/leanprover/lean4/pull/1744).

* [Add `linter.deprecated` option to silence deprecation warnings](https://github.com/leanprover/lean4/pull/1768).

* [Improve fuzzy-matching heuristics](https://github.com/leanprover/lean4/pull/1710).

* [Implementation-detail hypotheses](https://github.com/leanprover/lean4/pull/1692).

* [Hover information for `cases`/`induction` case names](https://github.com/leanprover/lean4/pull/1660).

* [Prefer longer parse even if unsuccessful](https://github.com/leanprover/lean4/pull/1658).

* [Show declaration module in hover](https://github.com/leanprover/lean4/pull/1638).

* [New `conv` mode structuring tactics](https://github.com/leanprover/lean4/pull/1636).

* `simp` can track information and can print an equivalent `simp only`. [PR #1626](https://github.com/leanprover/lean4/pull/1626).

* Enforce uniform indentation in tactic blocks / do blocks. See issue [#1606](https://github.com/leanprover/lean4/issues/1606).

* Moved `AssocList`, `HashMap`, `HashSet`, `RBMap`, `RBSet`, `PersistentArray`, `PersistentHashMap`, `PersistentHashSet` to the Lean package. The [standard library](https://github.com/leanprover/std4) contains versions that will evolve independently to simplify bootstrapping process.

* Standard library moved to the [std4 GitHub repository](https://github.com/leanprover/std4).

* `InteractiveGoals` now has information that a client infoview can use to show what parts of the goal have changed after applying a tactic. [PR #1610](https://github.com/leanprover/lean4/pull/1610).

* Add `[inheritDoc]` attribute. [PR #1480](https://github.com/leanprover/lean4/pull/1480).

* Expose that `panic = default`. [PR #1614](https://github.com/leanprover/lean4/pull/1614).

* New [code generator](https://github.com/leanprover/lean4/tree/master/src/Lean/Compiler/LCNF) project has started.

* Remove description argument from `register_simp_attr`. [PR #1566](https://github.com/leanprover/lean4/pull/1566).

* [Additional concurrency primitives](https://github.com/leanprover/lean4/pull/1555).

* [Collapsible traces with messages](https://github.com/leanprover/lean4/pull/1448).

* [Hygienic resolution of namespaces](https://github.com/leanprover/lean4/pull/1442).

* [New `Float` functions](https://github.com/leanprover/lean4/pull/1460).

* Many new doc strings have been added to declarations at `Init`.

v4.0.0-m5 (07 August 2022)
---------

* Update Lake to v4.0.0. See the [v4.0.0 release notes](https://github.com/leanprover/lake/releases/tag/v4.0.0) for detailed changes.

* Mutual declarations in different namespaces are now supported. Example:
  ```lean
  mutual
    def Foo.boo (x : Nat) :=
      match x with
      | 0 => 1
      | x + 1 => 2*Boo.bla x

    def Boo.bla (x : Nat) :=
      match x with
      | 0 => 2
      | x+1 => 3*Foo.boo x
  end
  ```
  A `namespace` is automatically created for the common prefix. Example:
  ```lean
  mutual
    def Tst.Foo.boo (x : Nat) := ...
    def Tst.Boo.bla (x : Nat) := ...
  end
  ```
  expands to
  ```lean
  namespace Tst
  mutual
    def Foo.boo (x : Nat) := ...
    def Boo.bla (x : Nat) := ...
  end
  end Tst
  ```

* Allow users to install their own `deriving` handlers for existing type classes.
  See example at [Simple.lean](https://github.com/leanprover/lean4/blob/master/tests/pkg/deriving/UserDeriving/Simple.lean).

* Add tactic `congr (num)?`. See doc string for additional details.

* [Missing doc linter](https://github.com/leanprover/lean4/pull/1390)

* `match`-syntax notation now checks for unused alternatives. See issue [#1371](https://github.com/leanprover/lean4/issues/1371).

* Auto-completion for structure instance fields. Example:
  ```lean
  example : Nat × Nat := {
    f -- HERE
  }
  ```
  `fst` now appears in the list of auto-completion suggestions.

* Auto-completion for dotted identifier notation. Example:
  ```lean
  example : Nat :=
    .su -- HERE
  ```
  `succ` now appears in the list of auto-completion suggestions.

* `nat_lit` is not needed anymore when declaring `OfNat` instances. See issues [#1389](https://github.com/leanprover/lean4/issues/1389) and [#875](https://github.com/leanprover/lean4/issues/875). Example:
  ```lean
  inductive Bit where
    | zero
    | one

  instance inst0 : OfNat Bit 0 where
    ofNat := Bit.zero

  instance : OfNat Bit 1 where
    ofNat := Bit.one

  example : Bit := 0
  example : Bit := 1
  ```

* Add `[elabAsElim]` attribute (it is called `elab_as_eliminator` in Lean 3). Motivation: simplify the Mathlib port to Lean 4.

* `Trans` type class now accepts relations in `Type u`. See this [Zulip issue](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Calc.20mode/near/291214574).

* Accept unescaped keywords as inductive constructor names. Escaping can often be avoided at use sites via dot notation.
  ```lean
  inductive MyExpr
    | let : ...

  def f : MyExpr → MyExpr
    | .let ... => .let ...
  ```

* Throw an error message at parametric local instances such as `[Nat -> Decidable p]`. The type class resolution procedure
  cannot use this kind of local instance because the parameter does not have a forward dependency.
  This check can be disabled using `set_option checkBinderAnnotations false`.

* Add option `pp.showLetValues`. When set to `false`, the info view hides the value of `let`-variables in a goal.
  By default, it is `true` when visualizing tactic goals, and `false` otherwise.
  See [issue #1345](https://github.com/leanprover/lean4/issues/1345) for additional details.

* Add option `warningAsError`. When set to true, warning messages are treated as errors.

* Support dotted notation and named arguments in patterns. Example:
  ```lean
  def getForallBinderType (e : Expr) : Expr :=
    match e with
    | .forallE (binderType := type) .. => type
    | _ => panic! "forall expected"
  ```

* "jump-to-definition" now works for function names embedded in the following attributes
  `@[implementedBy funName]`, `@[tactic parserName]`, `@[termElab parserName]`, `@[commandElab parserName]`,
  `@[builtinTactic parserName]`, `@[builtinTermElab parserName]`, and `@[builtinCommandElab parserName]`.
   See [issue #1350](https://github.com/leanprover/lean4/issues/1350).

* Improve `MVarId` methods discoverability. See [issue #1346](https://github.com/leanprover/lean4/issues/1346).
  We still have to add similar methods for `FVarId`, `LVarId`, `Expr`, and other objects.
  Many existing methods have been marked as deprecated.

* Add attribute `[deprecated]` for marking deprecated declarations. Examples:
  ```lean
  def g (x : Nat) := x + 1

  -- Whenever `f` is used, a warning message is generated suggesting to use `g` instead.
  @[deprecated g]
  def f (x : Nat) := x + 1

  #check f 0 -- warning: `f` has been deprecated, use `g` instead

  -- Whenever `h` is used, a warning message is generated.
  @[deprecated]
  def h (x : Nat) := x + 1

  #check h 0 -- warning: `h` has been deprecated
  ```

* Add type `LevelMVarId` (and abbreviation `LMVarId`) for universe level metavariable ids.
  Motivation: prevent meta-programmers from mixing up universe and expression metavariable ids.

* Improve `calc` term and tactic. See [issue #1342](https://github.com/leanprover/lean4/issues/1342).

* [Relaxed antiquotation parsing](https://github.com/leanprover/lean4/pull/1272) further reduces the need for explicit `$x:p` antiquotation kind annotations.

* Add support for computed fields in inductives. Example:
  ```lean
  inductive Exp
    | var (i : Nat)
    | app (a b : Exp)
  with
    @[computedField] hash : Exp → Nat
      | .var i => i
      | .app a b => a.hash * b.hash + 1
  ```
  The result of the `Exp.hash` function is then stored as an extra "computed" field in the `.var` and `.app` constructors;
  `Exp.hash` accesses this field and thus runs in constant time (even on dag-like values).

* Update `a[i]` notation. It is now based on the typeclass
  ```lean
  class GetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop)) where
    getElem (xs : cont) (i : idx) (h : dom xs i) : Elem
  ```
  The notation `a[i]` is now defined as follows
  ```lean
  macro:max x:term noWs "[" i:term "]" : term => `(getElem $x $i (by get_elem_tactic))
  ```
  The proof that `i` is a valid index is synthesized using the tactic `get_elem_tactic`.
  For example, the type `Array α` has the following instances
  ```lean
  instance : GetElem (Array α) Nat α fun xs i => LT.lt i xs.size where ...
  instance : GetElem (Array α) USize α fun xs i => LT.lt i.toNat xs.size where ...
  ```
  You can use the notation `a[i]'h` to provide the proof manually.
  Two other notations were introduced: `a[i]!` and `a[i]?`, For `a[i]!`, a panic error message is produced at
  runtime if `i` is not a valid index. `a[i]?` has type `Option α`, and `a[i]?` evaluates to `none` if the
  index `i` is not valid.
  The three new notations are defined as follows:
  ```lean
  @[inline] def getElem' [GetElem cont idx elem dom] (xs : cont) (i : idx) (h : dom xs i) : elem :=
  getElem xs i h

  @[inline] def getElem! [GetElem cont idx elem dom] [Inhabited elem] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem :=
    if h : _ then getElem xs i h else panic! "index out of bounds"

  @[inline] def getElem? [GetElem cont idx elem dom] (xs : cont) (i : idx) [Decidable (dom xs i)] : Option elem :=
    if h : _ then some (getElem xs i h) else none

  macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)
  macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)
  macro x:term noWs "[" i:term "]'" h:term:max : term => `(getElem' $x $i $h)
  ```
  See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/String.2EgetOp/near/287855425).
  Examples:
  ```lean
  example (a : Array Int) (i : Nat) : Int :=
    a[i] -- Error: failed to prove index is valid ...

  example (a : Array Int) (i : Nat) (h : i < a.size) : Int :=
    a[i] -- Ok

  example (a : Array Int) (i : Nat) : Int :=
    a[i]! -- Ok

  example (a : Array Int) (i : Nat) : Option Int :=
    a[i]? -- Ok

  example (a : Array Int) (h : a.size = 2) : Int :=
    a[0]'(by rw [h]; decide) -- Ok

  example (a : Array Int) (h : a.size = 2) : Int :=
    have : 0 < a.size := by rw [h]; decide
    have : 1 < a.size := by rw [h]; decide
    a[0] + a[1] -- Ok

  example (a : Array Int) (i : USize) (h : i.toNat < a.size) : Int :=
    a[i] -- Ok
  ```
  The `get_elem_tactic` is defined as
  ```lean
  macro "get_elem_tactic" : tactic =>
    `(first
      | get_elem_tactic_trivial
      | fail "failed to prove index is valid, ..."
     )
  ```
  The `get_elem_tactic_trivial` auxiliary tactic can be extended using `macro_rules`. By default, it tries `trivial`, `simp_arith`, and a special case for `Fin`. In the future, it will also try `linarith`.
  You can extend `get_elem_tactic_trivial` using `my_tactic` as follows
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| my_tactic)
  ```
  Note that `Idx`'s type in `GetElem` does not depend on `Cont`. So, you cannot write the instance `instance : GetElem (Array α) (Fin ??) α fun xs i => ...`, but the Lean library comes equipped with the following auxiliary instance:
  ```lean
  instance [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
    getElem xs i h := getElem xs i.1 h
  ```
  and helper tactic
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Fin.val_lt_of_le; get_elem_tactic_trivial; done)
  ```
  Example:
  ```lean
  example (a : Array Nat) (i : Fin a.size) :=
    a[i] -- Ok

  example (a : Array Nat) (h : n ≤ a.size) (i : Fin n) :=
    a[i] -- Ok
  ```

* Better support for qualified names in recursive declarations. The following is now supported:
  ```lean
  namespace Nat
    def fact : Nat → Nat
    | 0 => 1
    | n+1 => (n+1) * Nat.fact n
  end Nat
  ```

* Add support for `CommandElabM` monad at `#eval`. Example:
  ```lean
  import Lean

  open Lean Elab Command

  #eval do
    let id := mkIdent `foo
    elabCommand (← `(def $id := 10))

  #eval foo -- 10
  ```

* Try to elaborate `do` notation even if the expected type is not available. We still delay elaboration when the expected type
  is not available. This change is particularly useful when writing examples such as
  ```lean
  #eval do
    IO.println "hello"
    IO.println "world"
  ```
  That is, we don't have to use the idiom `#eval show IO _ from do ...` anymore.
  Note that auto monadic lifting is less effective when the expected type is not available.
  Monadic polymorphic functions (e.g., `ST.Ref.get`) also require the expected type.

* On Linux, panics now print a backtrace by default, which can be disabled by setting the environment variable `LEAN_BACKTRACE` to `0`.
  Other platforms are TBD.

* The `group(·)` `syntax` combinator is now introduced automatically where necessary, such as when using multiple parsers inside `(...)+`.

* Add ["Typed Macros"](https://github.com/leanprover/lean4/pull/1251): syntax trees produced and accepted by syntax antiquotations now remember their syntax kinds, preventing accidental production of ill-formed syntax trees and reducing the need for explicit `:kind` antiquotation annotations. See PR for details.

* Aliases of protected definitions are protected too. Example:
  ```lean
  protected def Nat.double (x : Nat) := 2*x

  namespace Ex
  export Nat (double) -- Add alias Ex.double for Nat.double
  end Ex

  open Ex
  #check Ex.double -- Ok
  #check double -- Error, `Ex.double` is alias for `Nat.double` which is protected
  ```

* Use `IO.getRandomBytes` to initialize random seed for `IO.rand`. See discussion at [this PR](https://github.com/leanprover/lean4-samples/pull/2).

* Improve dot notation and aliases interaction. See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Namespace-based.20overloading.20does.20not.20find.20exports/near/282946185) for additional details.
  Example:
  ```lean
  def Set (α : Type) := α → Prop
  def Set.union (s₁ s₂ : Set α) : Set α := fun a => s₁ a ∨ s₂ a
  def FinSet (n : Nat) := Fin n → Prop

  namespace FinSet
    export Set (union) -- FinSet.union is now an alias for `Set.union`
  end FinSet

  example (x y : FinSet 10) : FinSet 10 :=
    x.union y -- Works
  ```

* `ext` and `enter` conv tactics can now go inside let-declarations. Example:
  ```lean
  example (g : Nat → Nat) (y : Nat) (h : let x := y + 1; g (0+x) = x) : g (y + 1) = y + 1 := by
    conv at h => enter [x, 1, 1]; rw [Nat.zero_add]
    /-
      g : Nat → Nat
      y : Nat
      h : let x := y + 1;
          g x = x
      ⊢ g (y + 1) = y + 1
    -/
    exact h
  ```

* Add `zeta` conv tactic to expand let-declarations. Example:
  ```lean
  example (h : let x := y + 1; 0 + x = y) : False := by
    conv at h => zeta; rw [Nat.zero_add]
    /-
      y : Nat
      h : y + 1 = y
      ⊢ False
    -/
    simp_arith at h
  ```

* Improve namespace resolution. See issue [#1224](https://github.com/leanprover/lean4/issues/1224). Example:
  ```lean
  import Lean
  open Lean Parser Elab
  open Tactic -- now opens both `Lean.Parser.Tactic` and `Lean.Elab.Tactic`
  ```

* Rename `constant` command to `opaque`. See discussion at [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/What.20is.20.60opaque.60.3F/near/284926171).

* Extend `induction` and `cases` syntax: multiple left-hand-sides in a single alternative. This extension is very similar to the one implemented for `match` expressions. Examples:
  ```lean
  inductive Foo where
    | mk1 (x : Nat) | mk2 (x : Nat) | mk3

  def f (v : Foo) :=
    match v with
    | .mk1 x => x + 1
    | .mk2 x => 2*x + 1
    | .mk3   => 1

  theorem f_gt_zero : f v > 0 := by
    cases v with
    | mk1 x | mk2 x => simp_arith!  -- New feature used here!
    | mk3 => decide
  ```

* [`let/if` indentation in `do` blocks in now supported.](https://github.com/leanprover/lean4/issues/1120)

* Add unnamed antiquotation `$_` for use in syntax quotation patterns.

* [Add unused variables linter](https://github.com/leanprover/lean4/pull/1159). Feedback welcome!

* Lean now generates an error if the body of a declaration body contains a universe parameter that does not occur in the declaration type, nor is an explicit parameter.
  Examples:
  ```lean
  /-
  The following declaration now produces an error because `PUnit` is universe polymorphic,
  but the universe parameter does not occur in the function type `Nat → Nat`
  -/
  def f (n : Nat) : Nat :=
    let aux (_ : PUnit) : Nat := n + 1
    aux ⟨⟩

  /-
  The following declaration is accepted because the universe parameter was explicitly provided in the
  function signature.
  -/
  def g.{u} (n : Nat) : Nat :=
    let aux (_ : PUnit.{u}) : Nat := n + 1
    aux ⟨⟩
  ```

* Add `subst_vars` tactic.

* [Fix `autoParam` in structure fields lost in multiple inheritance.](https://github.com/leanprover/lean4/issues/1158).

* Add `[eliminator]` attribute. It allows users to specify default recursor/eliminators for the `induction` and `cases` tactics.
  It is an alternative for the `using` notation. Example:
  ```lean
  @[eliminator] protected def recDiag {motive : Nat → Nat → Sort u}
      (zero_zero : motive 0 0)
      (succ_zero : (x : Nat) → motive x 0 → motive (x + 1) 0)
      (zero_succ : (y : Nat) → motive 0 y → motive 0 (y + 1))
      (succ_succ : (x y : Nat) → motive x y → motive (x + 1) (y + 1))
      (x y : Nat) :  motive x y :=
    let rec go : (x y : Nat) → motive x y
      | 0,     0 => zero_zero
      | x+1, 0   => succ_zero x (go x 0)
      | 0,   y+1 => zero_succ y (go 0 y)
      | x+1, y+1 => succ_succ x y (go x y)
    go x y
  termination_by go x y => (x, y)

  def f (x y : Nat) :=
    match x, y with
    | 0,   0   => 1
    | x+1, 0   => f x 0
    | 0,   y+1 => f 0 y
    | x+1, y+1 => f x y
  termination_by f x y => (x, y)

  example (x y : Nat) : f x y > 0 := by
    induction x, y <;> simp [f, *]
  ```

* Add support for `casesOn` applications to structural and well-founded recursion modules.
  This feature is useful when writing definitions using tactics. Example:
  ```lean
  inductive Foo where
    | a | b | c
    | pair: Foo × Foo → Foo

  def Foo.deq (a b : Foo) : Decidable (a = b) := by
    cases a <;> cases b
    any_goals apply isFalse Foo.noConfusion
    any_goals apply isTrue rfl
    case pair a b =>
      let (a₁, a₂) := a
      let (b₁, b₂) := b
      exact match deq a₁ b₁, deq a₂ b₂ with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁,h₂])
      | isFalse h₁, _ => isFalse (fun h => by cases h; cases (h₁ rfl))
      | _, isFalse h₂ => isFalse (fun h => by cases h; cases (h₂ rfl))
  ```

* `Option` is again a monad. The auxiliary type `OptionM` has been removed. See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Do.20we.20still.20need.20OptionM.3F/near/279761084).

* Improve `split` tactic. It used to fail on `match` expressions of the form `match h : e with ...` where `e` is not a free variable.
  The failure used to occur during generalization.


* New encoding for `match`-expressions that use the `h :` notation for discriminants. The information is not lost during delaboration,
  and it is the foundation for a better `split` tactic. at delaboration time. Example:
  ```lean
  #print Nat.decEq
  /-
  protected def Nat.decEq : (n m : Nat) → Decidable (n = m) :=
  fun n m =>
    match h : Nat.beq n m with
    | true => isTrue (_ : n = m)
    | false => isFalse (_ : ¬n = m)
  -/
  ```

* `exists` tactic is now takes a comma separated list of terms.

* Add `dsimp` and `dsimp!` tactics. They guarantee the result term is definitionally equal, and only apply
  `rfl`-theorems.

* Fix binder information for `match` patterns that use definitions tagged with `[matchPattern]` (e.g., `Nat.add`).
  We now have proper binder information for the variable `y` in the following example.
  ```lean
  def f (x : Nat) : Nat :=
    match x with
    | 0 => 1
    | y + 1 => y
  ```

* (Fix) the default value for structure fields may now depend on the structure parameters. Example:
  ```lean
  structure Something (i: Nat) where
  n1: Nat := 1
  n2: Nat := 1 + i

  def s : Something 10 := {}
  example : s.n2 = 11 := rfl
  ```

* Apply `rfl` theorems at the `dsimp` auxiliary method used by `simp`. `dsimp` can be used anywhere in an expression
  because it preserves definitional equality.

* Refine auto bound implicit feature. It does not consider anymore unbound variables that have the same
  name of a declaration being defined. Example:
  ```lean
  def f : f → Bool := -- Error at second `f`
    fun _ => true

  inductive Foo : List Foo → Type -- Error at second `Foo`
    | x : Foo []
  ```
  Before this refinement, the declarations above would be accepted and the
  second `f` and `Foo` would be treated as auto implicit variables. That is,
  `f : {f : Sort u} → f → Bool`, and
  `Foo : {Foo : Type u} → List Foo → Type`.


* Fix syntax highlighting for recursive declarations. Example
  ```lean
  inductive List (α : Type u) where
    | nil : List α  -- `List` is not highlighted as a variable anymore
    | cons (head : α) (tail : List α) : List α

  def List.map (f : α → β) : List α → List β
    | []    => []
    | a::as => f a :: map f as -- `map` is not highlighted as a variable anymore
  ```
* Add `autoUnfold` option to `Lean.Meta.Simp.Config`, and the following macros
  - `simp!` for `simp (config := { autoUnfold := true })`
  - `simp_arith!` for `simp (config := { autoUnfold := true, arith := true })`
  - `simp_all!` for `simp_all (config := { autoUnfold := true })`
  - `simp_all_arith!` for `simp_all (config := { autoUnfold := true, arith := true })`

  When the `autoUnfold` is set to true, `simp` tries to unfold the following kinds of definition
  - Recursive definitions defined by structural recursion.
  - Non-recursive definitions where the body is a `match`-expression. This
    kind of definition is only unfolded if the `match` can be reduced.
  Example:
  ```lean
  def append (as bs : List α) : List α :=
    match as with
    | [] => bs
    | a :: as => a :: append as bs

  theorem append_nil (as : List α) : append as [] = as := by
    induction as <;> simp_all!

  theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
    induction as <;> simp_all!
  ```

* Add `save` tactic for creating checkpoints more conveniently. Example:
  ```lean
  example : <some-proposition> := by
    tac_1
    tac_2
    save
    tac_3
    ...
  ```
  is equivalent to
  ```lean
  example : <some-proposition> := by
    checkpoint
      tac_1
      tac_2
    tac_3
    ...
  ```

* Remove support for `{}` annotation from inductive datatype constructors. This annotation was barely used, and we can control the binder information for parameter bindings using the new inductive family indices to parameter promotion. Example: the following declaration using `{}`
  ```lean
  inductive LE' (n : Nat) : Nat → Prop where
    | refl {} : LE' n n -- Want `n` to be explicit
    | succ  : LE' n m → LE' n (m+1)
  ```
  can now be written as
  ```lean
  inductive LE' : Nat → Nat → Prop where
    | refl (n : Nat) : LE' n n
    | succ : LE' n m → LE' n (m+1)
  ```
  In both cases, the inductive family has one parameter and one index.
  Recall that the actual number of parameters can be retrieved using the command `#print`.

* Remove support for `{}` annotation in the `structure` command.

* Several improvements to LSP server. Examples: "jump to definition" in mutually recursive sections, fixed incorrect hover information in "match"-expression patterns, "jump to definition" for pattern variables, fixed auto-completion in function headers, etc.

* In `macro ... xs:p* ...` and similar macro bindings of combinators, `xs` now has the correct type `Array Syntax`

* Identifiers in syntax patterns now ignore macro scopes during matching.

* Improve binder names for constructor auto implicit parameters. Example, given the inductive datatype
  ```lean
  inductive Member : α → List α → Type u
    | head : Member a (a::as)
    | tail : Member a bs → Member a (b::bs)
  ```
  before:
  ```lean
  #check @Member.head
  -- @Member.head : {x : Type u_1} → {a : x} → {as : List x} → Member a (a :: as)
  ```
  now:
  ```lean
  #check @Member.head
  -- @Member.head : {α : Type u_1} → {a : α} → {as : List α} → Member a (a :: as)
  ```

* Improve error message when constructor parameter universe level is too big.

* Add support for `for h : i in [start:stop] do .. ` where `h : i ∈ [start:stop]`. This feature is useful for proving
  termination of functions such as:
  ```lean
  inductive Expr where
    | app (f : String) (args : Array Expr)

  def Expr.size (e : Expr) : Nat := Id.run do
    match e with
    | app f args =>
      let mut sz := 1
      for h : i in [: args.size] do
        -- h.upper : i < args.size
        sz := sz + size (args.get ⟨i, h.upper⟩)
      return sz
  ```

* Add tactic `case'`. It is similar to `case`, but does not admit the goal on failure.
  For example, the new tactic is useful when writing tactic scripts where we need to use `case'`
  at `first | ... | ...`, and we want to take the next alternative when `case'` fails.

* Add tactic macro
  ```lean
  macro "stop" s:tacticSeq : tactic => `(repeat sorry)
  ```
  See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Partial.20evaluation.20of.20a.20file).

* When displaying goals, we do not display inaccessible proposition names
if they do not have forward dependencies. We still display their types.
For example, the goal
  ```lean
  case node.inl.node
  β : Type u_1
  b : BinTree β
  k : Nat
  v : β
  left : Tree β
  key : Nat
  value : β
  right : Tree β
  ihl : BST left → Tree.find? (Tree.insert left k v) k = some v
  ihr : BST right → Tree.find? (Tree.insert right k v) k = some v
  h✝ : k < key
  a✝³ : BST left
  a✝² : ForallTree (fun k v => k < key) left
  a✝¹ : BST right
  a✝ : ForallTree (fun k v => key < k) right
  ⊢ BST left
  ```
  is now displayed as
  ```lean
  case node.inl.node
  β : Type u_1
  b : BinTree β
  k : Nat
  v : β
  left : Tree β
  key : Nat
  value : β
  right : Tree β
  ihl : BST left → Tree.find? (Tree.insert left k v) k = some v
  ihr : BST right → Tree.find? (Tree.insert right k v) k = some v
   : k < key
   : BST left
   : ForallTree (fun k v => k < key) left
   : BST right
   : ForallTree (fun k v => key < k) right
  ⊢ BST left
  ```

* The hypothesis name is now optional in the `by_cases` tactic.

* [Fix inconsistency between `syntax` and kind names](https://github.com/leanprover/lean4/issues/1090).
  The node kinds `numLit`, `charLit`, `nameLit`, `strLit`, and `scientificLit` are now called
  `num`, `char`, `name`, `str`, and `scientific` respectively. Example: we now write
  ```lean
  macro_rules | `($n:num) => `("hello")
  ```
  instead of
  ```lean
  macro_rules | `($n:numLit) => `("hello")
  ```

* (Experimental) New `checkpoint <tactic-seq>` tactic for big interactive proofs.

* Rename tactic `nativeDecide` => `native_decide`.

* Antiquotations are now accepted in any syntax. The `incQuotDepth` `syntax` parser is therefore obsolete and has been removed.

* Renamed tactic `nativeDecide` => `native_decide`.

* "Cleanup" local context before elaborating a `match` alternative right-hand-side. Examples:
  ```lean
  example (x : Nat) : Nat :=
    match g x with
    | (a, b) => _ -- Local context does not contain the auxiliary `_discr := g x` anymore

  example (x : Nat × Nat) (h : x.1 > 0) : f x > 0 := by
    match x with
    | (a, b) => _ -- Local context does not contain the `h✝ : x.fst > 0` anymore
  ```

* Improve `let`-pattern (and `have`-pattern) macro expansion. In the following example,
  ```lean
  example (x : Nat × Nat) : f x > 0 := by
    let (a, b) := x
    done
  ```
  The resulting goal is now `... |- f (a, b) > 0` instead of `... |- f x > 0`.

* Add cross-compiled [aarch64 Linux](https://github.com/leanprover/lean4/pull/1066) and [aarch64 macOS](https://github.com/leanprover/lean4/pull/1076) releases.

* [Add tutorial-like examples to our documentation](https://github.com/leanprover/lean4/tree/master/doc/examples), rendered using LeanInk+Alectryon.

v4.0.0-m4 (23 March 2022)
---------

* `simp` now takes user-defined simp-attributes. You can define a new `simp` attribute by creating a file (e.g., `MySimp.lean`) containing
  ```lean
  import Lean
  open Lean.Meta

  initialize my_ext : SimpExtension ← registerSimpAttr `my_simp "my own simp attribute"
  ```
  If you don't need to access `my_ext`, you can also use the macro
  ```lean
  import Lean

  register_simp_attr my_simp "my own simp attribute"
  ```
  Recall that the new `simp` attribute is not active in the Lean file where it was defined.
  Here is a small example using the new feature.
  ```lean
  import MySimp

  def f (x : Nat) := x + 2
  def g (x : Nat) := x + 1

  @[my_simp] theorem f_eq : f x = x + 2 := rfl
  @[my_simp] theorem g_eq : g x = x + 1 := rfl

  example : f x + g x = 2*x + 3 := by
    simp_arith [my_simp]
  ```

* Extend `match` syntax: multiple left-hand-sides in a single alternative. Example:
  ```lean
  def fib : Nat → Nat
  | 0 | 1 => 1
  | n+2 => fib n + fib (n+1)
  ```
  This feature was discussed at [issue 371](https://github.com/leanprover/lean4/issues/371). It was implemented as a macro expansion. Thus, the following is accepted.
  ```lean
  inductive StrOrNum where
    | S (s : String)
    | I (i : Int)

  def StrOrNum.asString (x : StrOrNum) :=
    match x with
    | I a | S a => toString a
  ```


* Improve `#eval` command. Now, when it fails to synthesize a `Lean.MetaEval` instance for the result type, it reduces the type and tries again. The following example now works without additional annotations
  ```lean
  def Foo := List Nat

  def test (x : Nat) : Foo :=
    [x, x+1, x+2]

  #eval test 4
  ```

* `rw` tactic can now apply auto-generated equation theorems for a given definition. Example:
  ```lean
  example (a : Nat) (h : n = 1) : [a].length = n := by
    rw [List.length]
    trace_state -- .. |- [].length + 1 = n
    rw [List.length]
    trace_state -- .. |- 0 + 1 = n
    rw [h]
  ```

* [Fuzzy matching for auto completion](https://github.com/leanprover/lean4/pull/1023)

* Extend dot-notation `x.field` for arrow types. If type of `x` is an arrow, we look up for `Function.field`.
For example, given `f : Nat → Nat` and `g : Nat → Nat`, `f.comp g` is now notation for `Function.comp f g`.

* The new `.<identifier>` notation is now also accepted where a function type is expected.
  ```lean
  example (xs : List Nat) : List Nat := .map .succ xs
  example (xs : List α) : Std.RBTree α ord := xs.foldl .insert ∅
  ```

* [Add code folding support to the language server](https://github.com/leanprover/lean4/pull/1014).

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

* Auto generated congruence lemmas with support for casts on proofs and `Decidable` instances (see [wishlist](https://github.com/leanprover/lean4/issues/988)).

* Rename option `autoBoundImplicitLocal` => `autoImplicit`.

* [Relax auto-implicit restrictions](https://github.com/leanprover/lean4/pull/1011). The command `set_option relaxedAutoImplicit false` disables the relaxations.

* `contradiction` tactic now closes the goal if there is a `False.elim` application in the target.

* Renamed tatic `byCases` => `by_cases` (motivation: enforcing naming convention).

* Local instances occurring in patterns are now considered by the type class resolution procedure. Example:
  ```lean
  def concat : List ((α : Type) × ToString α × α) → String
    | [] => ""
    | ⟨_, _, a⟩ :: as => toString a ++ concat as
  ```

* Notation for providing the motive for `match` expressions has changed.
  before:
  ```lean
  match x, rfl : (y : Nat) → x = y → Nat with
  | 0,   h => ...
  | x+1, h => ...
  ```
  now:
  ```lean
  match (motive := (y : Nat) → x = y → Nat) x, rfl with
  | 0,   h => ...
  | x+1, h => ...
  ```
  With this change, the notation for giving names to equality proofs in `match`-expressions is not whitespace sensitive anymore. That is,
  we can now write
  ```lean
  match h : sort.swap a b with
  | (r₁, r₂) => ... -- `h : sort.swap a b = (r₁, r₂)`
  ```

* `(generalizing := true)` is the default behavior for `match` expressions even if the expected type is not a proposition. In the following example, we used to have to include `(generalizing := true)` manually.
  ```lean
  inductive Fam : Type → Type 1 where
    | any : Fam α
    | nat : Nat → Fam Nat

  example (a : α) (x : Fam α) : α :=
    match x with
    | Fam.any   => a
    | Fam.nat n => n
  ```

* We now use `PSum` (instead of `Sum`) when compiling mutually recursive definitions using well-founded recursion.

* Better support for parametric well-founded relations. See [issue #1017](https://github.com/leanprover/lean4/issues/1017). This change affects the low-level `termination_by'` hint because the fixed prefix of the function parameters in not "packed" anymore when constructing the well-founded relation type. For example, in the following definition, `as` is part of the fixed prefix, and is not packed anymore. In previous versions, the `termination_by'` term would be written as `measure fun ⟨as, i, _⟩ => as.size - i`
  ```lean
  def sum (as : Array Nat) (i : Nat) (s : Nat) : Nat :=
    if h : i < as.size then
      sum as (i+1) (s + as.get ⟨i, h⟩)
    else
      s
  termination_by' measure fun ⟨i, _⟩ => as.size - i
  ```

* Add `while <cond> do <do-block>`, `repeat <do-block>`, and `repeat <do-block> until <cond>` macros for `do`-block. These macros are based on `partial` definitions, and consequently are useful only for writing programs we don't want to prove anything about.

* Add `arith` option to `Simp.Config`, the macro `simp_arith` expands to `simp (config := { arith := true })`. Only `Nat` and linear arithmetic is currently supported. Example:
  ```lean
  example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
    simp_arith
  ```

* Add `fail <string>?` tactic that always fail.

* Add support for acyclicity at dependent elimination. See [issue #1022](https://github.com/leanprover/lean4/issues/1022).

* Add `trace <string>` tactic for debugging purposes.

* Add nontrivial `SizeOf` instance for types `Unit → α`, and add support for them in the auto-generated `SizeOf` instances for user-defined inductive types. For example, given the inductive datatype
  ```lean
  inductive LazyList (α : Type u) where
    | nil                               : LazyList α
    | cons (hd : α) (tl : LazyList α)   : LazyList α
    | delayed (t : Thunk (LazyList α))  : LazyList α
  ```
  we now have `sizeOf (LazyList.delayed t) = 1 + sizeOf t` instead of `sizeOf (LazyList.delayed t) = 2`.

* Add support for guessing (very) simple well-founded relations when proving termination. For example, the following function does not require a `termination_by` annotation anymore.
  ```lean
  def Array.insertAtAux (i : Nat) (as : Array α) (j : Nat) : Array α :=
    if h : i < j then
      let as := as.swap! (j-1) j;
      insertAtAux i as (j-1)
    else
      as
  ```

* Add support for `for h : x in xs do ...` notation where `h : x ∈ xs`. This is mainly useful for showing termination.

* Auto implicit behavior changed for inductive families. An auto implicit argument occurring in inductive family index is also treated as an index (IF it is not fixed, see next item). For example
  ```lean
  inductive HasType : Index n → Vector Ty n → Ty → Type where
  ```
  is now interpreted as
  ```lean
  inductive HasType : {n : Nat} → Index n → Vector Ty n → Ty → Type where
  ```

* To make the previous feature more convenient to use, we promote a fixed prefix of inductive family indices to parameters. For example, the following declaration is now accepted by Lean
  ```lean
  inductive Lst : Type u → Type u
    | nil  : Lst α
    | cons : α → Lst α → Lst α
  ```
  and `α` in `Lst α` is a parameter. The actual number of parameters can be inspected using the command `#print Lst`. This feature also makes sure we still accept the declaration
  ```lean
  inductive Sublist : List α → List α → Prop
    | slnil : Sublist [] []
    | cons l₁ l₂ a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
    | cons2 l₁ l₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)
  ```

* Added auto implicit "chaining". Unassigned metavariables occurring in the auto implicit types now become new auto implicit locals. Consider the following example:
  ```lean
  inductive HasType : Fin n → Vector Ty n → Ty → Type where
    | stop : HasType 0 (ty :: ctx) ty
    | pop  : HasType k ctx ty → HasType k.succ (u :: ctx) ty
  ```
  `ctx` is an auto implicit local in the two constructors, and it has type `ctx : Vector Ty ?m`. Without auto implicit "chaining", the metavariable `?m` will remain unassigned. The new feature creates yet another implicit local `n : Nat` and assigns `n` to `?m`. So, the declaration above is shorthand for
  ```lean
  inductive HasType : {n : Nat} → Fin n → Vector Ty n → Ty → Type where
    | stop : {ty : Ty} → {n : Nat} → {ctx : Vector Ty n} → HasType 0 (ty :: ctx) ty
    | pop  : {n : Nat} → {k : Fin n} → {ctx : Vector Ty n} → {ty : Ty} → HasType k ctx ty → HasType k.succ (u :: ctx) ty
  ```

* Eliminate auxiliary type annotations (e.g, `autoParam` and `optParam`) from recursor minor premises and projection declarations. Consider the following example
  ```lean
  structure A :=
    x : Nat
    h : x = 1 := by trivial

  example (a : A) : a.x = 1 := by
    have aux := a.h
    -- `aux` has now type `a.x = 1` instead of `autoParam (a.x = 1) auto✝`
    exact aux

  example (a : A) : a.x = 1 := by
    cases a with
    | mk x h =>
      -- `h` has now type `x = 1` instead of `autoParam (x = 1) auto✝`
      assumption
  ```

* We now accept overloaded notation in patterns, but we require the set of pattern variables in each alternative to be the same. Example:
  ```lean
  inductive Vector (α : Type u) : Nat → Type u
    | nil : Vector α 0
    | cons : α → Vector α n → Vector α (n+1)

  infix:67 " :: " => Vector.cons -- Overloading the `::` notation

  def head1 (x : List α) (h : x ≠ []) : α :=
    match x with
    | a :: as => a -- `::` is `List.cons` here

  def head2 (x : Vector α (n+1)) : α :=
    match x with
    | a :: as => a -- `::` is `Vector.cons` here
  ```

* New notation `.<identifier>` based on Swift. The namespace is inferred from the expected type. See [issue #944](https://github.com/leanprover/lean4/issues/944). Examples:
  ```lean
  def f (x : Nat) : Except String Nat :=
    if x > 0 then
      .ok x
    else
      .error "x is zero"

  namespace Lean.Elab
  open Lsp

  def identOf : Info → Option (RefIdent × Bool)
    | .ofTermInfo ti => match ti.expr with
      | .const n .. => some (.const n, ti.isBinder)
      | .fvar id .. => some (.fvar id, ti.isBinder)
      | _ => none
    | .ofFieldInfo fi => some (.const fi.projName, false)
    | _ => none

  def isImplicit (bi : BinderInfo) : Bool :=
    bi matches .implicit

  end Lean.Elab
  ```
