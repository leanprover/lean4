# Lean 4 releases

We intend to provide regular "minor version" releases of the Lean language at approximately monthly intervals.
There is not yet a strong guarantee of backwards compatibility between versions,
only an expectation that breaking changes will be documented in this file.

This file contains work-in-progress notes for the upcoming release, as well as previous stable releases.
Please check the [releases](https://github.com/leanprover/lean4/releases) page for the current status
of each version.

v4.8.0
---------

### Language features, tactics, and metaprograms

* **Functional induction principles.**
  [#3432](https://github.com/leanprover/lean4/pull/3432), [#3620](https://github.com/leanprover/lean4/pull/3620),
  [#3754](https://github.com/leanprover/lean4/pull/3754), [#3762](https://github.com/leanprover/lean4/pull/3762),
  [#3738](https://github.com/leanprover/lean4/pull/3738), [#3776](https://github.com/leanprover/lean4/pull/3776),
  [#3898](https://github.com/leanprover/lean4/pull/3898).

  Derived from the definition of a (possibly mutually) recursive function,
  a **functional induction principle** is created that is tailored to proofs about that function.

  For example from:
  ```
  def ackermann : Nat → Nat → Nat
    | 0, m => m + 1
    | n+1, 0 => ackermann n 1
    | n+1, m+1 => ackermann n (ackermann (n + 1) m)
  ```
  we get
  ```
  ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
    (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
    (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
    (x x : Nat) : motive x x
  ```

  It can be used in the `induction` tactic using the `using` syntax:
  ```
  induction n, m using ackermann.induct
  ```
* The termination checker now recognizes more recursion patterns without an
  explicit `termination_by`. In particular the idiom of counting up to an upper
  bound, as in
  ```
  def Array.sum (arr : Array Nat) (i acc : Nat) : Nat :=
    if _ : i < arr.size then
      Array.sum arr (i+1) (acc + arr[i])
    else
      acc
  ```
  is recognized without having to say `termination_by arr.size - i`.
  * [#3630](https://github.com/leanprover/lean4/pull/3630) makes `termination_by?` not use `sizeOf` when not needed
  * [#3652](https://github.com/leanprover/lean4/pull/3652) improves the `termination_by` syntax.
  * [#3658](https://github.com/leanprover/lean4/pull/3658) changes how termination arguments are elaborated.
  * [#3665](https://github.com/leanprover/lean4/pull/3665) refactors GuessLex to allow inferring more complex termination arguments
  * [#3666](https://github.com/leanprover/lean4/pull/3666) infers termination arguments such as `xs.size - i`
* [#3629](https://github.com/leanprover/lean4/pull/3629),
  [#3655](https://github.com/leanprover/lean4/pull/3655),
  [#3747](https://github.com/leanprover/lean4/pull/3747):
  Adds `@[induction_eliminator]` and `@[cases_eliminator]` attributes to be able to define custom eliminators
  for the `induction` and `cases` tactics, replacing the `@[eliminator]` attribute.
  Gives custom eliminators for `Nat` so that `induction` and `cases` put goal states into terms of `0` and `n + 1`
  rather than `Nat.zero` and `Nat.succ n`.
  Added option `tactic.customEliminators` to control whether to use custom eliminators.
  Added a hack for `rcases`/`rintro`/`obtain` to use the custom eliminator for `Nat`.
* **Shorter instances names.** There is a new algorithm for generating names for anonymous instances.
  Across Std and Mathlib, the median ratio between lengths of new names and of old names is about 72%.
  With the old algorithm, the longest name was 1660 characters, and now the longest name is 202 characters.
  The new algorithm's 95th percentile name length is 67 characters, versus 278 for the old algorithm.
  While the new algorithm produces names that are 1.2% less unique,
  it avoids cross-project collisions by adding a module-based suffix
  when it does not refer to declarations from the same "project" (modules that share the same root).
  [#3089](https://github.com/leanprover/lean4/pull/3089)
  and [#3934](https://github.com/leanprover/lean4/pull/3934).
* [8d2adf](https://github.com/leanprover/lean4/commit/8d2adf521d2b7636347a5b01bfe473bf0fcfaf31)
  Importing two different files containing proofs of the same theorem is no longer considered an error.
  This feature is particularly useful for theorems that are automatically generated on demand (e.g., equational theorems).
* [84b091](https://github.com/leanprover/lean4/commit/84b0919a116e9be12f933e764474f45d964ce85c)
  Lean now generates an error if the type of a theorem is **not** a proposition.
* **Definition transparency.** [47a343](https://github.com/leanprover/lean4/commit/47a34316fc03ce936fddd2d3dce44784c5bcdfa9). `@[reducible]`, `@[semireducible]`, and `@[irreducible]` are now scoped and able to be set for imported declarations.
* `simp`/`dsimp`
  * [#3607](https://github.com/leanprover/lean4/pull/3607) enables kernel projection reduction in `dsimp`
  * [b24fbf](https://github.com/leanprover/lean4/commit/b24fbf44f3aaa112f5d799ef2a341772d1eb222d)
    and [acdb00](https://github.com/leanprover/lean4/commit/acdb0054d5a0efa724cff596ac26852fad5724c4):
    `dsimproc` command
    to define defeq-preserving simplification procedures.
  * [#3624](https://github.com/leanprover/lean4/pull/3624) makes `dsimp` normalize raw nat literals as `OfNat.ofNat` applications.
  * [#3628](https://github.com/leanprover/lean4/pull/3628) makes `simp` correctly handle `OfScientific.ofScientific` literals.
  * [#3654](https://github.com/leanprover/lean4/pull/3654) makes `dsimp?` report used simprocs.
  * [dee074](https://github.com/leanprover/lean4/commit/dee074dcde03a37b7895a4901df2e4fa490c73c7) fixes equation theorem
    handling in `simp` for non-recursive definitions.
  * [#3819](https://github.com/leanprover/lean4/pull/3819) improved performance when simp encounters a loop.
  * [#3821](https://github.com/leanprover/lean4/pull/3821) fixes discharger/cache interaction.
  * [#3824](https://github.com/leanprover/lean4/pull/3824) keeps `simp` from breaking `Char` literals.
  * [#3838](https://github.com/leanprover/lean4/pull/3838) allows `Nat` instances matching to be more lenient.
  * [#3870](https://github.com/leanprover/lean4/pull/3870) documentation for `simp` configuration options.
  * [#3972](https://github.com/leanprover/lean4/pull/3972) fixes simp caching.
  * [#4044](https://github.com/leanprover/lean4/pull/4044) improves cache behavior for "well-behaved" dischargers.
* `omega`
  * [#3639](https://github.com/leanprover/lean4/pull/3639), [#3766](https://github.com/leanprover/lean4/pull/3766),
    [#3853](https://github.com/leanprover/lean4/pull/3853), [#3875](https://github.com/leanprover/lean4/pull/3875):
    introduces a term canonicalizer.
  * [#3736](https://github.com/leanprover/lean4/pull/3736) improves handling of positivity for the modulo operator for `Int`.
  * [#3828](https://github.com/leanprover/lean4/pull/3828) makes it work as a `simp` discharger.
  * [#3847](https://github.com/leanprover/lean4/pull/3847) adds helpful error messages.
* `rfl`
  * [#3671](https://github.com/leanprover/lean4/pull/3671), [#3708](https://github.com/leanprover/lean4/pull/3708): upstreams the `@[refl]` attribute and the `rfl` tactic.
  * [#3751](https://github.com/leanprover/lean4/pull/3751) makes `apply_rfl` not operate on `Eq` itself.
  * [#4067](https://github.com/leanprover/lean4/pull/4067) improves error message when there are no goals.
* [#3719](https://github.com/leanprover/lean4/pull/3719) upstreams the `rw?` tactic, with fixes and improvements in
  [#3783](https://github.com/leanprover/lean4/pull/3783), [#3794](https://github.com/leanprover/lean4/pull/3794),
  [#3911](https://github.com/leanprover/lean4/pull/3911).
* `conv`
  * [#3659](https://github.com/leanprover/lean4/pull/3659) adds a `conv` version of the `calc` tactic.
  * [#3763](https://github.com/leanprover/lean4/pull/3763) makes `conv` clean up using `try with_reducible rfl` instead of `try rfl`.
* `#guard_msgs`
  * [#3617](https://github.com/leanprover/lean4/pull/3617) introduces whitespace protection using the `⏎` character.
  * [#3883](https://github.com/leanprover/lean4/pull/3883):
    The `#guard_msgs` command now has options to change whitespace normalization and sensitivity to message ordering.
    For example, `#guard_msgs (whitespace := lax) in cmd` collapses whitespace before checking messages,
    and `#guard_msgs (ordering := sorted) in cmd` sorts the messages in lexicographic order before checking.
  * [#3931](https://github.com/leanprover/lean4/pull/3931) adds an unused variables ignore function for `#guard_msgs`.
  * [#3912](https://github.com/leanprover/lean4/pull/3912) adds a diff between the expected and actual outputs. This feature is currently
    disabled by default, but can be enabled with `set_option guard_msgs.diff true`.
    Depending on user feedback, this option may default to `true` in a future version of Lean.
* `do` **notation**
  * [#3820](https://github.com/leanprover/lean4/pull/3820) makes it an error to lift `(<- ...)` out of a pure `if ... then ... else ...`
* **Lazy discrimination trees**
  * [#3610](https://github.com/leanprover/lean4/pull/3610) fixes a name collision for `LazyDiscrTree` that could lead to cache poisoning.
  * [#3677](https://github.com/leanprover/lean4/pull/3677) simplifies and fixes `LazyDiscrTree` handling for `exact?`/`apply?`.
  * [#3685](https://github.com/leanprover/lean4/pull/3685) moves general `exact?`/`apply?` functionality into `LazyDiscrTree`.
  * [#3769](https://github.com/leanprover/lean4/pull/3769) has lemma selection improvements for `rw?` and `LazyDiscrTree`.
  * [#3818](https://github.com/leanprover/lean4/pull/3818) improves ordering of matches.
* [#3590](https://github.com/leanprover/lean4/pull/3590) adds `inductive.autoPromoteIndices` option to be able to disable auto promotion of indices in the `inductive` command.
* **Miscellaneous bug fixes and improvements**
  * [#3606](https://github.com/leanprover/lean4/pull/3606) preserves `cache` and `dischargeDepth` fields in `Lean.Meta.Simp.Result.mkEqSymm`.
  * [#3633](https://github.com/leanprover/lean4/pull/3633) makes `elabTermEnsuringType` respect `errToSorry`, improving error recovery of the `have` tactic.
  * [#3647](https://github.com/leanprover/lean4/pull/3647) enables `noncomputable unsafe` definitions, for deferring implementations until later.
  * [#3672](https://github.com/leanprover/lean4/pull/3672) adjust namespaces of tactics.
  * [#3725](https://github.com/leanprover/lean4/pull/3725) fixes `Ord` derive handler for indexed inductive types with unused alternatives.
  * [#3893](https://github.com/leanprover/lean4/pull/3893) improves performance of derived `Ord` instances.
  * [#3771](https://github.com/leanprover/lean4/pull/3771) changes error reporting for failing tactic macros. Improves `rfl` error message.
  * [#3745](https://github.com/leanprover/lean4/pull/3745) fixes elaboration of generalized field notation if the object of the notation is an optional parameter.
  * [#3799](https://github.com/leanprover/lean4/pull/3799) makes commands such as `universe`, `variable`, `namespace`, etc. require that their argument appear in a later column.
    Commands that can optionally parse an `ident` or parse any number of `ident`s generally should require
    that the `ident` use `colGt`. This keeps typos in commands from being interpreted as identifiers.
  * [#3815](https://github.com/leanprover/lean4/pull/3815) lets the `split` tactic be used for writing code.
  * [#3822](https://github.com/leanprover/lean4/pull/3822) adds missing info in `induction` tactic for `with` clauses of the form `| cstr a b c => ?_`.
  * [#3806](https://github.com/leanprover/lean4/pull/3806) fixes `withSetOptionIn` combinator.
  * [#3844](https://github.com/leanprover/lean4/pull/3844) removes unused `trace.Elab.syntax` option.
  * [#3896](https://github.com/leanprover/lean4/pull/3896) improves hover and go-to-def for `attribute` command.
  * [#3989](https://github.com/leanprover/lean4/pull/3989) makes linter options more discoverable.
  * [#3916](https://github.com/leanprover/lean4/pull/3916) fixes go-to-def for syntax defined with `@[builtin_term_parser]`.
  * [#3962](https://github.com/leanprover/lean4/pull/3962) fixes how `solveByElim` handles `symm` lemmas, making `exact?`/`apply?` usable again.
  * [#3968](https://github.com/leanprover/lean4/pull/3968) improves the `@[deprecated]` attribute, adding `(since := "<date>")` field.
  * [#3768](https://github.com/leanprover/lean4/pull/3768) makes `#print` command show structure fields.
  * [#3974](https://github.com/leanprover/lean4/pull/3974) makes `exact?%` behave like `by exact?` rather than `by apply?`.
  * [#3994](https://github.com/leanprover/lean4/pull/3994) makes elaboration of `he ▸ h` notation more predictable.
  * [#3991](https://github.com/leanprover/lean4/pull/3991) adjusts transparency for `decreasing_trivial` macros.
  * [#4092](https://github.com/leanprover/lean4/pull/4092) improves performance of `binop%` and `binrel%` expression tree elaborators.
* **Docs:** [#3748](https://github.com/leanprover/lean4/pull/3748), [#3796](https://github.com/leanprover/lean4/pull/3796),
[#3800](https://github.com/leanprover/lean4/pull/3800), [#3874](https://github.com/leanprover/lean4/pull/3874),
[#3863](https://github.com/leanprover/lean4/pull/3863), [#3862](https://github.com/leanprover/lean4/pull/3862),
[#3891](https://github.com/leanprover/lean4/pull/3891), [#3873](https://github.com/leanprover/lean4/pull/3873),
[#3908](https://github.com/leanprover/lean4/pull/3908), [#3872](https://github.com/leanprover/lean4/pull/3872).

### Language server and IDE extensions

* [#3432](https://github.com/leanprover/lean4/pull/3432) enables `import` auto-completions.
* [#3608](https://github.com/leanprover/lean4/pull/3608) fixes issue [leanprover/vscode-lean4#392](https://github.com/leanprover/vscode-lean4/issues/392).
  Diagnostic ranges had an off-by-one error that would misplace goal states for example.
* [#3014](https://github.com/leanprover/lean4/pull/3014) introduces snapshot trees, foundational work for incremental tactics and parallelism.
  [#3849](https://github.com/leanprover/lean4/pull/3849) adds basic incrementality API.
* [#3271](https://github.com/leanprover/lean4/pull/3271) adds support for server-to-client requests.
* [#3656](https://github.com/leanprover/lean4/pull/3656) fixes jump to definition when there are conflicting names from different files.
  Fixes issue [#1170](https://github.com/leanprover/lean4/issues/1170).
* [#3691](https://github.com/leanprover/lean4/pull/3691), [#3925](https://github.com/leanprover/lean4/pull/3925),
  [#3932](https://github.com/leanprover/lean4/pull/3932) keep semantic tokens synchronized (used for semantic highlighting), with performance improvements.
* [#3247](https://github.com/leanprover/lean4/pull/3247) and [#3730](https://github.com/leanprover/lean4/pull/3730)
  add diagnostics to run "Restart File" when a file dependency is saved.
* [#3722](https://github.com/leanprover/lean4/pull/3722) uses the correct module names when displaying references.
* [#3728](https://github.com/leanprover/lean4/pull/3728) makes errors in header reliably appear and makes the "Import out of date" warning be at "hint" severity.
  [#3739](https://github.com/leanprover/lean4/pull/3739) simplifies the text of this warning.
* [#3778](https://github.com/leanprover/lean4/pull/3778) fixes [#3462](https://github.com/leanprover/lean4/issues/3462),
  where info nodes from before the cursor would be used for computing completions.
* [#3985](https://github.com/leanprover/lean4/pull/3985) makes trace timings appear in Infoview.

### Pretty printing

* [#3797](https://github.com/leanprover/lean4/pull/3797) fixes the hovers over binders so that they show their types.
* [#3640](https://github.com/leanprover/lean4/pull/3640) and [#3735](https://github.com/leanprover/lean4/pull/3735): Adds attribute `@[pp_using_anonymous_constructor]` to make structures pretty print as `⟨x, y, z⟩`
  rather than as `{a := x, b := y, c := z}`.
  This attribute is applied to `Sigma`, `PSigma`, `PProd`, `Subtype`, `And`, and `Fin`.
* [#3749](https://github.com/leanprover/lean4/pull/3749)
  Now structure instances pretty print with parent structures' fields inlined.
  That is, if `B` extends `A`, then `{ toA := { x := 1 }, y := 2 }` now pretty prints as `{ x := 1, y := 2 }`.
  Setting option `pp.structureInstances.flatten` to false turns this off.
* [#3737](https://github.com/leanprover/lean4/pull/3737), [#3744](https://github.com/leanprover/lean4/pull/3744)
  and [#3750](https://github.com/leanprover/lean4/pull/3750):
  Option `pp.structureProjections` is renamed to `pp.fieldNotation`, and there is now a suboption `pp.fieldNotation.generalized`
  to enable pretty printing function applications using generalized field notation (defaults to true).
  Field notation can be disabled on a function-by-function basis using the `@[pp_nodot]` attribute.
  The notation is not used for theorems.
* [#4071](https://github.com/leanprover/lean4/pull/4071) fixes interaction between app unexpanders and `pp.fieldNotation.generalized`
* [#3625](https://github.com/leanprover/lean4/pull/3625) makes `delabConstWithSignature` (used by `#check`) have the ability to put arguments "after the colon"
  to avoid printing inaccessible names.
* [#3798](https://github.com/leanprover/lean4/pull/3798),
  [#3978](https://github.com/leanprover/lean4/pull/3978),
  [#3798](https://github.com/leanprover/lean4/pull/3980):
  Adds options `pp.mvars` (default: true) and `pp.mvars.withType` (default: false).
  When `pp.mvars` is false, expression metavariables pretty print as `?_` and universe metavariables pretty print as `_`.
  When `pp.mvars.withType` is true, expression metavariables pretty print with a type ascription.
  These can be set when using `#guard_msgs` to make tests not depend on the particular names of metavariables.
* [#3917](https://github.com/leanprover/lean4/pull/3917) makes binders hoverable and gives them docstrings.
* [#4034](https://github.com/leanprover/lean4/pull/4034) makes hovers for RHS terms in `match` expressions in the Infoview reliably show the correct term.

### Library

* `Bool`/`Prop`
  * [#3508](https://github.com/leanprover/lean4/pull/3508) improves `simp` confluence for `Bool` and `Prop` terms.
  * Theorems: [#3604](https://github.com/leanprover/lean4/pull/3604)
* `Nat`
  * [#3579](https://github.com/leanprover/lean4/pull/3579) makes `Nat.succ_eq_add_one` be a simp lemma, now that `induction`/`cases` uses `n + 1` instead of `Nat.succ n`.
  * [#3808](https://github.com/leanprover/lean4/pull/3808) replaces `Nat.succ` simp rules with simprocs.
  * [#3876](https://github.com/leanprover/lean4/pull/3876) adds faster `Nat.repr` implementation in C.
* `Int`
  * Theorems: [#3890](https://github.com/leanprover/lean4/pull/3890)
* `UInt`s
  * [#3960](https://github.com/leanprover/lean4/pull/3960) improves performance of upcasting.
* `Array` and `Subarray`
  * [#3676](https://github.com/leanprover/lean4/pull/3676) removes `Array.eraseIdxAux`, `Array.eraseIdxSzAux`, and `Array.eraseIdx'`.
  * [#3648](https://github.com/leanprover/lean4/pull/3648) simplifies `Array.findIdx?`.
  * [#3851](https://github.com/leanprover/lean4/pull/3851) renames fields of `Subarray`.
* `List`
  * [#3785](https://github.com/leanprover/lean4/pull/3785) upstreams tail-recursive List operations and `@[csimp]` lemmas.
* `BitVec`
  * Theorems: [#3593](https://github.com/leanprover/lean4/pull/3593),
  [#3593](https://github.com/leanprover/lean4/pull/3593), [#3597](https://github.com/leanprover/lean4/pull/3597),
  [#3598](https://github.com/leanprover/lean4/pull/3598), [#3721](https://github.com/leanprover/lean4/pull/3721),
  [#3729](https://github.com/leanprover/lean4/pull/3729), [#3880](https://github.com/leanprover/lean4/pull/3880),
  [#4039](https://github.com/leanprover/lean4/pull/4039).
  * [#3884](https://github.com/leanprover/lean4/pull/3884) protects `Std.BitVec`.
* `String`
  * [#3832](https://github.com/leanprover/lean4/pull/3832) fixes `String.splitOn`.
  * [#3959](https://github.com/leanprover/lean4/pull/3959) adds `String.Pos.isValid`.
  * [#3959](https://github.com/leanprover/lean4/pull/3959) UTF-8 string validation.
  * [#3961](https://github.com/leanprover/lean4/pull/3961) adds a model implementation for UTF-8 encoding and decoding.
* `IO`
  * [#4097](https://github.com/leanprover/lean4/pull/4097) adds `IO.getTaskState` which returns whether a task is finished, actively running, or waiting on other Tasks to finish.

* **Refactors**
  * [#3605](https://github.com/leanprover/lean4/pull/3605) reduces imports for `Init.Data.Nat` and `Init.Data.Int`.
  * [#3613](https://github.com/leanprover/lean4/pull/3613) reduces imports for `Init.Omega.Int`.
  * [#3634](https://github.com/leanprover/lean4/pull/3634) upstreams `Std.Data.Nat`
    and [#3635](https://github.com/leanprover/lean4/pull/3635) upstreams `Std.Data.Int`.
  * [#3790](https://github.com/leanprover/lean4/pull/3790) reduces more imports for `omega`.
  * [#3694](https://github.com/leanprover/lean4/pull/3694) extends `GetElem` interface with `getElem!` and `getElem?` to simplify containers like `RBMap`.
  * [#3865](https://github.com/leanprover/lean4/pull/3865) renames `Option.toMonad` (see breaking changes below).
  * [#3882](https://github.com/leanprover/lean4/pull/3882) unifies `lexOrd` with `compareLex`.
* **Other fixes or improvements**
  * [#3765](https://github.com/leanprover/lean4/pull/3765) makes `Quotient.sound` be a `theorem`.
  * [#3645](https://github.com/leanprover/lean4/pull/3645) fixes `System.FilePath.parent` in the case of absolute paths.
  * [#3660](https://github.com/leanprover/lean4/pull/3660) `ByteArray.toUInt64LE!` and `ByteArray.toUInt64BE!` were swapped.
  * [#3881](https://github.com/leanprover/lean4/pull/3881), [#3887](https://github.com/leanprover/lean4/pull/3887) fix linearity issues in `HashMap.insertIfNew`, `HashSet.erase`, and `HashMap.erase`.
    The `HashMap.insertIfNew` fix improves `import` performance.
  * [#3830](https://github.com/leanprover/lean4/pull/3830) ensures linearity in `Parsec.many*Core`.
  * [#3930](https://github.com/leanprover/lean4/pull/3930) adds `FS.Stream.isTty` field.
  * [#3866](https://github.com/leanprover/lean4/pull/3866) deprecates `Option.toBool` in favor of `Option.isSome`.
  * [#3975](https://github.com/leanprover/lean4/pull/3975) upstreams `Data.List.Init` and `Data.Array.Init` material from Std.
  * [#3942](https://github.com/leanprover/lean4/pull/3942) adds instances that make `ac_rfl` work without Mathlib.
  * [#4010](https://github.com/leanprover/lean4/pull/4010) changes `Fin.induction` to use structural induction.
  * [02753f](https://github.com/leanprover/lean4/commit/02753f6e4c510c385efcbf71fa9a6bec50fce9ab)
    fixes bug in `reduceLeDiff` simproc.
  * [#4097](https://github.com/leanprover/lean4/pull/4097)
    adds `IO.TaskState` and `IO.getTaskState` to get the task from the Lean runtime's task manager.
* **Docs:** [#3615](https://github.com/leanprover/lean4/pull/3615), [#3664](https://github.com/leanprover/lean4/pull/3664),
  [#3707](https://github.com/leanprover/lean4/pull/3707), [#3734](https://github.com/leanprover/lean4/pull/3734),
  [#3868](https://github.com/leanprover/lean4/pull/3868), [#3861](https://github.com/leanprover/lean4/pull/3861),
  [#3869](https://github.com/leanprover/lean4/pull/3869), [#3858](https://github.com/leanprover/lean4/pull/3858),
  [#3856](https://github.com/leanprover/lean4/pull/3856), [#3857](https://github.com/leanprover/lean4/pull/3857),
  [#3867](https://github.com/leanprover/lean4/pull/3867), [#3864](https://github.com/leanprover/lean4/pull/3864),
  [#3860](https://github.com/leanprover/lean4/pull/3860), [#3859](https://github.com/leanprover/lean4/pull/3859),
  [#3871](https://github.com/leanprover/lean4/pull/3871), [#3919](https://github.com/leanprover/lean4/pull/3919).

### Lean internals

* **Defeq and WHNF algorithms**
  * [#3616](https://github.com/leanprover/lean4/pull/3616) gives better support for reducing `Nat.rec` expressions.
  * [#3774](https://github.com/leanprover/lean4/pull/3774) add tracing for "non-easy" WHNF cases.
  * [#3807](https://github.com/leanprover/lean4/pull/3807) fixes an `isDefEq` performance issue, now trying structure eta *after* lazy delta reduction.
  * [#3816](https://github.com/leanprover/lean4/pull/3816) fixes `.yesWithDeltaI` behavior to prevent increasing transparency level when reducing projections.
  * [#3837](https://github.com/leanprover/lean4/pull/3837) improves heuristic at `isDefEq`.
  * [#3965](https://github.com/leanprover/lean4/pull/3965) improves `isDefEq` for constraints of the form `t.i =?= s.i`.
  * [#3977](https://github.com/leanprover/lean4/pull/3977) improves `isDefEqProj`.
  * [#3981](https://github.com/leanprover/lean4/pull/3981) adds universe constraint approximations to be able to solve `u =?= max u ?v` using `?v = u`.
    These approximations are only applied when universe constraints cannot be postponed anymore.
  * [#4004](https://github.com/leanprover/lean4/pull/4004) improves `isDefEqProj` during typeclass resolution.
  * [#4012](https://github.com/leanprover/lean4/pull/4012) adds `backward.isDefEq.lazyProjDelta` and `backward.isDefEq.lazyWhnfCore` backwards compatibility flags.
* **Kernel**
  * [#3966](https://github.com/leanprover/lean4/pull/3966) removes dead code.
  * [#4035](https://github.com/leanprover/lean4/pull/4035) fixes mismatch for `TheoremVal` between Lean and C++.
* **Discrimination trees**
  * [423fed](https://github.com/leanprover/lean4/commit/423fed79a9de75705f34b3e8648db7e076c688d7)
    and [3218b2](https://github.com/leanprover/lean4/commit/3218b25974d33e92807af3ce42198911c256ff1d):
    simplify handling of dependent/non-dependent pi types.
* **Typeclass instance synthesis**
  * [#3638](https://github.com/leanprover/lean4/pull/3638) eta-reduces synthesized instances
  * [ce350f](https://github.com/leanprover/lean4/commit/ce350f348161e63fccde6c4a5fe1fd2070e7ce0f) fixes a linearity issue
  * [917a31](https://github.com/leanprover/lean4/commit/917a31f694f0db44d6907cc2b1485459afe74d49)
    improves performance by considering at most one answer for subgoals not containing metavariables.
    [#4008](https://github.com/leanprover/lean4/pull/4008) adds `backward.synthInstance.canonInstances` backward compatibility flag.
* **Definition processing**
  * [#3661](https://github.com/leanprover/lean4/pull/3661), [#3767](https://github.com/leanprover/lean4/pull/3767) changes automatically generated equational theorems to be named
    using suffix `.eq_<idx>` instead of `._eq_<idx>`, and `.eq_def` instead of `._unfold`. (See breaking changes below.)
    [#3675](https://github.com/leanprover/lean4/pull/3675) adds a mechanism to reserve names.
    [#3803](https://github.com/leanprover/lean4/pull/3803) fixes reserved name resolution inside namespaces and fixes handling of `match`er declarations and equation lemmas.
  * [#3662](https://github.com/leanprover/lean4/pull/3662) causes auxiliary definitions nested inside theorems to become `def`s if they are not proofs.
  * [#4006](https://github.com/leanprover/lean4/pull/4006) makes proposition fields of `structure`s be theorems.
  * [#4018](https://github.com/leanprover/lean4/pull/4018) makes it an error for a theorem to be `extern`.
  * [#4047](https://github.com/leanprover/lean4/pull/4047) improves performance making equations for well-founded recursive definitions.
* **Refactors**
  * [#3614](https://github.com/leanprover/lean4/pull/3614) avoids unfolding in `Lean.Meta.evalNat`.
  * [#3621](https://github.com/leanprover/lean4/pull/3621) centralizes functionality for `Fix`/`GuessLex`/`FunInd` in the `ArgsPacker` module.
  * [#3186](https://github.com/leanprover/lean4/pull/3186) rewrites the UnusedVariable linter to be more performant.
  * [#3589](https://github.com/leanprover/lean4/pull/3589) removes coercion from `String` to `Name` (see breaking changes below).
  * [#3237](https://github.com/leanprover/lean4/pull/3237) removes the `lines` field from `FileMap`.
  * [#3951](https://github.com/leanprover/lean4/pull/3951) makes msg parameter to `throwTacticEx` optional.
* **Diagnostics**
  * [#4016](https://github.com/leanprover/lean4/pull/4016), [#4019](https://github.com/leanprover/lean4/pull/4019),
    [#4020](https://github.com/leanprover/lean4/pull/4020), [#4030](https://github.com/leanprover/lean4/pull/4030),
    [#4031](https://github.com/leanprover/lean4/pull/4031),
    [c3714b](https://github.com/leanprover/lean4/commit/c3714bdc6d46845c0428735b283c5b48b23cbcf7),
    [#4049](https://github.com/leanprover/lean4/pull/4049) adds `set_option diagnostics true` for diagnostic counters.
    Tracks number of unfolded declarations, instances, reducible declarations, used instances, recursor reductions,
    `isDefEq` heuristic applications, among others.
    This option is suggested in exceptional situations, such as at deterministic timeout and maximum recursion depth.
  * [283587](https://github.com/leanprover/lean4/commit/283587987ab2eb3b56fbc3a19d5f33ab9e04a2ef)
    adds diagnostic information for `simp`.
  * [#4043](https://github.com/leanprover/lean4/pull/4043) adds diagnostic information for congruence theorems.
  * [#4048](https://github.com/leanprover/lean4/pull/4048) display diagnostic information
    for `set_option diagnostics true in <tactic>` and `set_option diagnostics true in <term>`.
* **Other features**
  * [#3800](https://github.com/leanprover/lean4/pull/3800) adds environment extension to record which definitions use structural or well-founded recursion.
  * [#3801](https://github.com/leanprover/lean4/pull/3801) `trace.profiler` can now export to Firefox Profiler.
  * [#3918](https://github.com/leanprover/lean4/pull/3918), [#3953](https://github.com/leanprover/lean4/pull/3953) adds `@[builtin_doc]` attribute to make docs and location of a declaration available as a builtin.
  * [#3939](https://github.com/leanprover/lean4/pull/3939) adds the `lean --json` CLI option to print messages as JSON.
  * [#3075](https://github.com/leanprover/lean4/pull/3075) improves `test_extern` command.
  * [#3970](https://github.com/leanprover/lean4/pull/3970) gives monadic generalization of `FindExpr`.
* **Docs:** [#3743](https://github.com/leanprover/lean4/pull/3743), [#3921](https://github.com/leanprover/lean4/pull/3921),
  [#3954](https://github.com/leanprover/lean4/pull/3954).
* **Other fixes:** [#3622](https://github.com/leanprover/lean4/pull/3622),
  [#3726](https://github.com/leanprover/lean4/pull/3726), [#3823](https://github.com/leanprover/lean4/pull/3823),
  [#3897](https://github.com/leanprover/lean4/pull/3897), [#3964](https://github.com/leanprover/lean4/pull/3964),
  [#3946](https://github.com/leanprover/lean4/pull/3946), [#4007](https://github.com/leanprover/lean4/pull/4007),
  [#4026](https://github.com/leanprover/lean4/pull/4026).

### Compiler, runtime, and FFI

* [#3632](https://github.com/leanprover/lean4/pull/3632) makes it possible to allocate and free thread-local runtime resources for threads not started by Lean itself.
* [#3627](https://github.com/leanprover/lean4/pull/3627) improves error message about compacting closures.
* [#3692](https://github.com/leanprover/lean4/pull/3692) fixes deadlock in `IO.Promise.resolve`.
* [#3753](https://github.com/leanprover/lean4/pull/3753) catches error code from `MoveFileEx` on Windows.
* [#4028](https://github.com/leanprover/lean4/pull/4028) fixes a double `reset` bug in `ResetReuse` transformation.
* [6e731b](https://github.com/leanprover/lean4/commit/6e731b4370000a8e7a5cfb675a7f3d7635d21f58)
  removes `interpreter` copy constructor to avoid potential memory safety issues.

### Lake

* **TOML Lake configurations**. [#3298](https://github.com/leanprover/lean4/pull/3298), [#4104](https://github.com/leanprover/lean4/pull/4104).

  Lake packages can now use TOML as a alternative configuration file format instead of Lean. If the default `lakefile.lean` is missing, Lake will also look for a `lakefile.toml`. The TOML version of the configuration supports a restricted set of the Lake configuration options, only including those which can easily mapped to a TOML data structure. The TOML syntax itself fully compiles with the TOML v1.0.0 specification.

  As part of the introduction of this new feature, we have been helping maintainers of some major packages within the ecosystem switch to this format. For example, the following is Aesop's new `lakefile.toml`:


  **[leanprover-community/aesop/lakefile.toml](https://raw.githubusercontent.com/leanprover-community/aesop/de11e0ecf372976e6d627c210573146153090d2d/lakefile.toml)**
  ```toml
  name = "aesop"
  defaultTargets = ["Aesop"]
  testRunner = "test"
  precompileModules = false

  [[require]]
  name = "batteries"
  git = "https://github.com/leanprover-community/batteries"
  rev = "main"

  [[lean_lib]]
  name = "Aesop"

  [[lean_lib]]
  name = "AesopTest"
  globs = ["AesopTest.+"]
  leanOptions = {linter.unusedVariables = false}

  [[lean_exe]]
  name = "test"
  srcDir = "scripts"
  ```

  To assist users who wish to transition their packages between configuration file formats, there is also a new `lake translate-config` command for migrating to/from TOML.

  Running `lake translate-config toml` will produce a `lakefile.toml` version of a package's `lakefile.lean`. Any configuration options unsupported by the TOML format will be discarded during translation, but the original `lakefile.lean` will remain so that you can verify the translation looks good before deleting it.

* **Build progress overhaul.** [#3835](https://github.com/leanprover/lean4/pull/3835), [#4115](https://github.com/leanprover/lean4/pull/4115), [#4127](https://github.com/leanprover/lean4/pull/4127), [#4220](https://github.com/leanprover/lean4/pull/4220), [#4232](https://github.com/leanprover/lean4/pull/4232), [#4236](https://github.com/leanprover/lean4/pull/4236).

  Builds are now managed by a top-level Lake build monitor, this makes the output of Lake builds more standardized and enables producing prettier and more configurable progress reports.

  As part of this change, job isolation has improved. Stray I/O and other build related errors in custom targets are now properly isolated and caught as part of their job. Import errors no longer cause Lake to abort the entire build and are instead localized to the build jobs of the modules in question.

  Lake also now uses ANSI escape sequences to add color and produce progress lines that update in-place; this can be toggled on and off using `--ansi` / `--no-ansi`.


  `--wfail` and `--iofail` options have been added that causes a build to fail if any of the jobs log a warning (`--wfail`) or produce any output or log information messages (`--iofail`). Unlike some other build systems, these options do **NOT** convert these logs into errors, and Lake does not abort jobs on such a log (i.e., dependent jobs will still continue unimpeded).

* `lake test`. [#3779](https://github.com/leanprover/lean4/pull/3779).

  Lake now has a built-in `test` command which will run a script or executable labelled `@[test_runner]` (in Lean) or defined as the `testRunner` (in TOML) in the root package.

  Lake also provides a `lake check-test` command which will exit with code `0` if the package has a properly configured test runner or error with `1` otherwise.

* `lake lean`. [#3793](https://github.com/leanprover/lean4/pull/3793).

  The new command `lake lean <file> [-- <args...>]` functions like `lake env lean <file> <args...>`, except that it builds the imports of `file` before running `lean`. This makes it very useful for running test or example code that imports modules that are not guaranteed to have been built beforehand.

* **Miscellaneous bug fixes and improvements**
  * [#3609](https://github.com/leanprover/lean4/pull/3609) `LEAN_GITHASH` environment variable to override the detected Git hash for Lean when computing traces, useful for testing custom builds of Lean.
  * [#3795](https://github.com/leanprover/lean4/pull/3795) improves relative package directory path normalization in the pre-rename check.
  * [#3957](https://github.com/leanprover/lean4/pull/3957) fixes handling of packages that appear multiple times in a dependency tree.
  * [#3999](https://github.com/leanprover/lean4/pull/3999) makes it an error for there to be a mismatch between a package name and what it is required as. Also adds a special message for the `std`-to-`batteries` rename.
  * [#4033](https://github.com/leanprover/lean4/pull/4033) fixes quiet mode.
* **Docs:** [#3704](https://github.com/leanprover/lean4/pull/3704).

### DevOps

* [#3536](https://github.com/leanprover/lean4/pull/3536) and [#3833](https://github.com/leanprover/lean4/pull/3833)
  add a checklist for the release process.
* [#3600](https://github.com/leanprover/lean4/pull/3600) runs nix-ci more uniformly.
* [#3612](https://github.com/leanprover/lean4/pull/3612) avoids argument limits when building on Windows.
* [#3682](https://github.com/leanprover/lean4/pull/3682) builds Lean's `.o` files in parallel to rest of core.
* [#3601](https://github.com/leanprover/lean4/pull/3601)
  changes the way Lean is built on Windows (see breaking changes below).
  As a result, Lake now dynamically links executables with `supportInterpreter := true` on Windows
  to `libleanshared.dll` and `libInit_shared.dll`. Therefore, such executables will not run
  unless those shared libraries are co-located with the executables or part of `PATH`.
  Running the executable via `lake exe` will ensure these libraries are part of `PATH`.

  In a related change, the signature of the `nativeFacets` Lake configuration options has changed
  from a static `Array` to a function `(shouldExport : Bool) → Array`.
  See its docstring or Lake's [README](src/lake/README.md) for further details on the changed option.
* [#3690](https://github.com/leanprover/lean4/pull/3690) marks "Build matrix complete" as canceled if the build is canceled.
* [#3700](https://github.com/leanprover/lean4/pull/3700), [#3702](https://github.com/leanprover/lean4/pull/3702),
  [#3701](https://github.com/leanprover/lean4/pull/3701), [#3834](https://github.com/leanprover/lean4/pull/3834),
  [#3923](https://github.com/leanprover/lean4/pull/3923): fixes and improvements for std and mathlib CI.
* [#3712](https://github.com/leanprover/lean4/pull/3712) fixes `nix build .` on macOS.
* [#3717](https://github.com/leanprover/lean4/pull/3717) replaces `shell.nix` in devShell with `flake.nix`.
* [#3715](https://github.com/leanprover/lean4/pull/3715) and [#3790](https://github.com/leanprover/lean4/pull/3790) add test result summaries.
* [#3971](https://github.com/leanprover/lean4/pull/3971) prevents stage0 changes via the merge queue.
* [#3979](https://github.com/leanprover/lean4/pull/3979) adds handling for `changes-stage0` label.
* [#3952](https://github.com/leanprover/lean4/pull/3952) adds a script to summarize GitHub issues.
* [18a699](https://github.com/leanprover/lean4/commit/18a69914da53dbe37c91bc2b9ce65e1dc01752b6)
  fixes asan linking

### Breaking changes

* Due to the major Lake build refactor, code using the affected parts of the Lake API or relying on the previous output format of Lake builds is likely to have been broken. We have tried to minimize the breakages and, were possible, old definitions have been marked `@[deprecated]` with a reference to the new alternative.

* Executables configured with `supportInterpreter := true` on Windows should now be run via `lake exe` to function properly.

* Automatically generated equational theorems are now named using suffix `.eq_<idx>` instead of `._eq_<idx>`, and `.eq_def` instead of `._unfold`. Example:
```
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

theorem ex : fact 0 = 1 := by unfold fact; decide

#check fact.eq_1
-- fact.eq_1 : fact 0 = 1

#check fact.eq_2
-- fact.eq_2 (n : Nat) : fact (Nat.succ n) = (n + 1) * fact n

#check fact.eq_def
/-
fact.eq_def :
  ∀ (x : Nat),
    fact x =
      match x with
      | 0 => 1
      | Nat.succ n => (n + 1) * fact n
-/
```

* The coercion from `String` to `Name` was removed. Previously, it was `Name.mkSimple`, which does not separate strings at dots, but experience showed that this is not always the desired coercion. For the previous behavior, manually insert a call to `Name.mkSimple`.

* The `Subarray` fields `as`, `h₁` and `h₂` have been renamed to `array`, `start_le_stop`, and `stop_le_array_size`, respectively. This more closely follows standard Lean conventions. Deprecated aliases for the field projections were added; these will be removed in a future release.

* The change to the instance name algorithm (described above) can break projects that made use of the auto-generated names.

* `Option.toMonad` has been renamed to `Option.getM` and the unneeded `[Monad m]` instance argument has been removed.

v4.7.0
---------

* `simp` and `rw` now use instance arguments found by unification,
  rather than always resynthesizing. For backwards compatibility, the original behaviour is
  available via `set_option tactic.skipAssignedInstances false`.
  [#3507](https://github.com/leanprover/lean4/pull/3507) and
  [#3509](https://github.com/leanprover/lean4/pull/3509).

* When the `pp.proofs` is false, now omitted proofs use `⋯` rather than `_`,
  which gives a more helpful error message when copied from the Infoview.
  The `pp.proofs.threshold` option lets small proofs always be pretty printed.
  [#3241](https://github.com/leanprover/lean4/pull/3241).

* `pp.proofs.withType` is now set to false by default to reduce noise in the info view.

* The pretty printer for applications now handles the case of over-application itself when applying app unexpanders.
  In particular, the ``| `($_ $a $b $xs*) => `(($a + $b) $xs*)`` case of an `app_unexpander` is no longer necessary.
  [#3495](https://github.com/leanprover/lean4/pull/3495).

* New `simp` (and `dsimp`) configuration option: `zetaDelta`. It is `false` by default.
  The `zeta` option is still `true` by default, but their meaning has changed.
  - When `zeta := true`, `simp` and `dsimp` reduce terms of the form
    `let x := val; e[x]` into `e[val]`.
  - When `zetaDelta := true`, `simp` and `dsimp` will expand let-variables in
    the context. For example, suppose the context contains `x := val`. Then,
    any occurrence of `x` is replaced with `val`.

  See [issue #2682](https://github.com/leanprover/lean4/pull/2682) for additional details. Here are some examples:
  ```
  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    simp
    /-
    New goal:
    h : z = 9; x := 5 |- x + 4 = z
    -/
    rw [h]

  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    -- Using both `zeta` and `zetaDelta`.
    simp (config := { zetaDelta := true })
    /-
    New goal:
    h : z = 9; x := 5 |- 9 = z
    -/
    rw [h]

  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    simp [x] -- asks `simp` to unfold `x`
    /-
    New goal:
    h : z = 9; x := 5 |- 9 = z
    -/
    rw [h]

  example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
    intro x
    simp (config := { zetaDelta := true, zeta := false })
    /-
    New goal:
    h : z = 9; x := 5 |- let y := 4; 5 + y = z
    -/
    rw [h]
  ```

* When adding new local theorems to `simp`, the system assumes that the function application arguments
  have been annotated with `no_index`. This modification, which addresses [issue #2670](https://github.com/leanprover/lean4/issues/2670),
  restores the Lean 3 behavior that users expect. With this modification, the following examples are now operational:
  ```
  example {α β : Type} {f : α × β → β → β} (h : ∀ p : α × β, f p p.2 = p.2)
    (a : α) (b : β) : f (a, b) b = b := by
    simp [h]

  example {α β : Type} {f : α × β → β → β}
    (a : α) (b : β) (h : f (a,b) (a,b).2 = (a,b).2) : f (a, b) b = b := by
    simp [h]
  ```
  In both cases, `h` is applicable because `simp` does not index f-arguments anymore when adding `h` to the `simp`-set.
  It's important to note, however, that global theorems continue to be indexed in the usual manner.

* Improved the error messages produced by the `decide` tactic. [#3422](https://github.com/leanprover/lean4/pull/3422)

* Improved auto-completion performance. [#3460](https://github.com/leanprover/lean4/pull/3460)

* Improved initial language server startup performance. [#3552](https://github.com/leanprover/lean4/pull/3552)

* Changed call hierarchy to sort entries and strip private header from names displayed in the call hierarchy. [#3482](https://github.com/leanprover/lean4/pull/3482)

* There is now a low-level error recovery combinator in the parsing framework, primarily intended for DSLs. [#3413](https://github.com/leanprover/lean4/pull/3413)

* You can now write `termination_by?` after a declaration to see the automatically inferred
  termination argument, and turn it into a `termination_by …` clause using the “Try this” widget or a code action. [#3514](https://github.com/leanprover/lean4/pull/3514)

* A large fraction of `Std` has been moved into the Lean repository.
  This was motivated by:
  1. Making universally useful tactics such as `ext`, `by_cases`, `change at`,
    `norm_cast`, `rcases`, `simpa`, `simp?`, `omega`, and `exact?`
    available to all users of Lean, without imports.
  2. Minimizing the syntactic changes between plain Lean and Lean with `import Std`.
  3. Simplifying the development process for the basic data types
     `Nat`, `Int`, `Fin` (and variants such as `UInt64`), `List`, `Array`,
     and `BitVec` as we begin making the APIs and simp normal forms for these types
     more complete and consistent.
  4. Laying the groundwork for the Std roadmap, as a library focused on
     essential datatypes not provided by the core langauge (e.g. `RBMap`)
     and utilities such as basic IO.
  While we have achieved most of our initial aims in `v4.7.0-rc1`,
  some upstreaming will continue over the coming months.

* The `/` and `%` notations in `Int` now use `Int.ediv` and `Int.emod`
  (i.e. the rounding conventions have changed).
  Previously `Std` overrode these notations, so this is no change for users of `Std`.
  There is now kernel support for these functions.
  [#3376](https://github.com/leanprover/lean4/pull/3376).

* `omega`, our integer linear arithmetic tactic, is now availabe in the core langauge.
  * It is supplemented by a preprocessing tactic `bv_omega` which can solve goals about `BitVec`
    which naturally translate into linear arithmetic problems.
    [#3435](https://github.com/leanprover/lean4/pull/3435).
  * `omega` now has support for `Fin` [#3427](https://github.com/leanprover/lean4/pull/3427),
    the `<<<` operator [#3433](https://github.com/leanprover/lean4/pull/3433).
  * During the port `omega` was modified to no longer identify atoms up to definitional equality
    (so in particular it can no longer prove `id x ≤ x`). [#3525](https://github.com/leanprover/lean4/pull/3525).
    This may cause some regressions.
    We plan to provide a general purpose preprocessing tactic later, or an `omega!` mode.
  * `omega` is now invoked in Lean's automation for termination proofs
    [#3503](https://github.com/leanprover/lean4/pull/3503) as well as in
    array indexing proofs [#3515](https://github.com/leanprover/lean4/pull/3515).
    This automation will be substantially revised in the medium term,
    and while `omega` does help automate some proofs, we plan to make this much more robust.

* The library search tactics `exact?` and `apply?` that were originally in
  Mathlib are now available in Lean itself.  These use the implementation using
  lazy discrimination trees from `Std`, and thus do not require a disk cache but
  have a slightly longer startup time.  The order used for selection lemmas has
  changed as well to favor goals purely based on how many terms in the head
  pattern match the current goal.

* The `solve_by_elim` tactic has been ported from `Std` to Lean so that library
  search can use it.

* New `#check_tactic` and `#check_simp` commands have been added.  These are
  useful for checking tactics (particularly `simp`) behave as expected in test
  suites.

* Previously, app unexpanders would only be applied to entire applications. However, some notations produce
  functions, and these functions can be given additional arguments. The solution so far has been to write app unexpanders so that they can take an arbitrary number of additional arguments. However this leads to misleading hover information in the Infoview. For example, while `HAdd.hAdd f g 1` pretty prints as `(f + g) 1`, hovering over `f + g` shows `f`. There is no way to fix the situation from within an app unexpander; the expression position for `HAdd.hAdd f g` is absent, and app unexpanders cannot register TermInfo.

  This commit changes the app delaborator to try running app unexpanders on every prefix of an application, from longest to shortest prefix. For efficiency, it is careful to only try this when app delaborators do in fact exist for the head constant, and it also ensures arguments are only delaborated once. Then, in `(f + g) 1`, the `f + g` gets TermInfo registered for that subexpression, making it properly hoverable.

  [#3375](https://github.com/leanprover/lean4/pull/3375)

Breaking changes:
* `Lean.withTraceNode` and variants got a stronger `MonadAlwaysExcept` assumption to
  fix trace trees not being built on elaboration runtime exceptions. Instances for most elaboration
  monads built on `EIO Exception` should be synthesized automatically.
* The `match ... with.` and `fun.` notations previously in Std have been replaced by
  `nomatch ...` and `nofun`. [#3279](https://github.com/leanprover/lean4/pull/3279) and [#3286](https://github.com/leanprover/lean4/pull/3286)


Other improvements:
* several bug fixes for `simp`:
  * we should not crash when `simp` loops [#3269](https://github.com/leanprover/lean4/pull/3269)
  * `simp` gets stuck on `autoParam` [#3315](https://github.com/leanprover/lean4/pull/3315)
  * `simp` fails when custom discharger makes no progress [#3317](https://github.com/leanprover/lean4/pull/3317)
  * `simp` fails to discharge `autoParam` premises even when it can reduce them to `True` [#3314](https://github.com/leanprover/lean4/pull/3314)
  * `simp?` suggests generated equations lemma names, fixes [#3547](https://github.com/leanprover/lean4/pull/3547) [#3573](https://github.com/leanprover/lean4/pull/3573)
* fixes for `match` expressions:
  * fix regression with builtin literals [#3521](https://github.com/leanprover/lean4/pull/3521)
  * accept `match` when patterns cover all cases of a `BitVec` finite type [#3538](https://github.com/leanprover/lean4/pull/3538)
  * fix matching `Int` literals [#3504](https://github.com/leanprover/lean4/pull/3504)
  * patterns containing int values and constructors [#3496](https://github.com/leanprover/lean4/pull/3496)
* improve `termination_by` error messages [#3255](https://github.com/leanprover/lean4/pull/3255)
* fix `rename_i` in macros, fixes [#3553](https://github.com/leanprover/lean4/pull/3553) [#3581](https://github.com/leanprover/lean4/pull/3581)
* fix excessive resource usage in `generalize`, fixes [#3524](https://github.com/leanprover/lean4/pull/3524) [#3575](https://github.com/leanprover/lean4/pull/3575)
* an equation lemma with autoParam arguments fails to rewrite, fixing [#2243](https://github.com/leanprover/lean4/pull/2243) [#3316](https://github.com/leanprover/lean4/pull/3316)
* `add_decl_doc` should check that declarations are local [#3311](https://github.com/leanprover/lean4/pull/3311)
* instantiate the types of inductives with the right parameters, closing [#3242](https://github.com/leanprover/lean4/pull/3242) [#3246](https://github.com/leanprover/lean4/pull/3246)
* New simprocs for many basic types. [#3407](https://github.com/leanprover/lean4/pull/3407)

Lake fixes:
* Warn on fetch cloud release failure [#3401](https://github.com/leanprover/lean4/pull/3401)
* Cloud release trace & `lake build :release` errors [#3248](https://github.com/leanprover/lean4/pull/3248)

v4.6.1
---------
* Backport of [#3552](https://github.com/leanprover/lean4/pull/3552) fixing a performance regression
  in server startup.

v4.6.0
---------

* Add custom simplification procedures (aka `simproc`s) to `simp`. Simprocs can be triggered by the simplifier on a specified term-pattern. Here is an small example:
  ```lean
  import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

  def foo (x : Nat) : Nat :=
    x + 10

  /--
  The `simproc` `reduceFoo` is invoked on terms that match the pattern `foo _`.
  -/
  simproc reduceFoo (foo _) :=
    /- A term of type `Expr → SimpM Step -/
    fun e => do
      /-
      The `Step` type has three constructors: `.done`, `.visit`, `.continue`.
      * The constructor `.done` instructs `simp` that the result does
        not need to be simplied further.
      * The constructor `.visit` instructs `simp` to visit the resulting expression.
      * The constructor `.continue` instructs `simp` to try other simplification procedures.

      All three constructors take a `Result`. The `.continue` contructor may also take `none`.
      `Result` has two fields `expr` (the new expression), and `proof?` (an optional proof).
       If the new expression is definitionally equal to the input one, then `proof?` can be omitted or set to `none`.
      -/
      /- `simp` uses matching modulo reducibility. So, we ensure the term is a `foo`-application. -/
      unless e.isAppOfArity ``foo 1 do
        return .continue
      /- `Nat.fromExpr?` tries to convert an expression into a `Nat` value -/
      let some n ← Nat.fromExpr? e.appArg!
        | return .continue
      return .done { expr := Lean.mkNatLit (n+10) }
  ```
  We disable simprocs support by using the command `set_option simprocs false`. This command is particularly useful when porting files to v4.6.0.
  Simprocs can be scoped, manually added to `simp` commands, and suppressed using `-`. They are also supported by `simp?`. `simp only` does not execute any `simproc`. Here are some examples for the `simproc` defined above.
  ```lean
  example : x + foo 2 = 12 + x := by
    set_option simprocs false in
      /- This `simp` command does not make progress since `simproc`s are disabled. -/
      fail_if_success simp
    simp_arith

  example : x + foo 2 = 12 + x := by
    /- `simp only` must not use the default simproc set. -/
    fail_if_success simp only
    simp_arith

  example : x + foo 2 = 12 + x := by
    /-
    `simp only` does not use the default simproc set,
    but we can provide simprocs as arguments. -/
    simp only [reduceFoo]
    simp_arith

  example : x + foo 2 = 12 + x := by
    /- We can use `-` to disable `simproc`s. -/
    fail_if_success simp [-reduceFoo]
    simp_arith
  ```
  The command `register_simp_attr <id>` now creates a `simp` **and** a `simproc` set with the name `<id>`. The following command instructs Lean to insert the `reduceFoo` simplification procedure into the set `my_simp`. If no set is specified, Lean uses the default `simp` set.
  ```lean
  simproc [my_simp] reduceFoo (foo _) := ...
  ```

* The syntax of the `termination_by` and `decreasing_by` termination hints is overhauled:

  * They are now placed directly after the function they apply to, instead of
    after the whole `mutual` block.
  * Therefore, the function name no longer has to be mentioned in the hint.
  * If the function has a `where` clause, the `termination_by` and
    `decreasing_by` for that function come before the `where`. The
    functions in the `where` clause can have their own termination hints, each
    following the corresponding definition.
  * The `termination_by` clause can only bind “extra parameters”, that are not
    already bound by the function header, but are bound in a lambda (`:= fun x
    y z =>`) or in patterns (`| x, n + 1 => …`). These extra parameters used to
    be understood as a suffix of the function parameters; now it is a prefix.

  Migration guide: In simple cases just remove the function name, and any
  variables already bound at the header.
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by foo a b => a - b
  +termination_by a b => a - b
  ```
  or
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by _ a b => a - b
  +termination_by a b => a - b
  ```

  If the parameters are bound in the function header (before the `:`), remove them as well:
  ```diff
   def foo (a b : Nat) : Nat := …
  -termination_by foo a b => a - b
  +termination_by a - b
  ```

  Else, if there are multiple extra parameters, make sure to refer to the right
  ones; the bound variables are interpreted from left to right, no longer from
  right to left:
  ```diff
   def foo : Nat → Nat → Nat → Nat
     | a, b, c => …
  -termination_by foo b c => b
  +termination_by a b => b
  ```

  In the case of a `mutual` block, place the termination arguments (without the
  function name) next to the function definition:
  ```diff
  -mutual
  -def foo : Nat → Nat → Nat := …
  -def bar : Nat → Nat := …
  -end
  -termination_by
  -  foo a b => a - b
  -  bar a => a
  +mutual
  +def foo : Nat → Nat → Nat := …
  +termination_by a b => a - b
  +def bar : Nat → Nat := …
  +termination_by a => a
  +end
  ```

  Similarly, if you have (mutual) recursion through `where` or `let rec`, the
  termination hints are now placed directly after the function they apply to:
  ```diff
  -def foo (a b : Nat) : Nat := …
  -  where bar (x : Nat) : Nat := …
  -termination_by
  -  foo a b => a - b
  -  bar x => x
  +def foo (a b : Nat) : Nat := …
  +termination_by a - b
  +  where
  +    bar (x : Nat) : Nat := …
  +    termination_by x

  -def foo (a b : Nat) : Nat :=
  -  let rec bar (x : Nat) :  Nat := …
  -  …
  -termination_by
  -  foo a b => a - b
  -  bar x => x
  +def foo (a b : Nat) : Nat :=
  +  let rec bar (x : Nat) : Nat := …
  +    termination_by x
  +  …
  +termination_by a - b
  ```

  In cases where a single `decreasing_by` clause applied to multiple mutually
  recursive functions before, the tactic now has to be duplicated.

* The semantics of `decreasing_by` changed; the tactic is applied to all
  termination proof goals together, not individually.

  This helps when writing termination proofs interactively, as one can focus
  each subgoal individually, for example using `·`. Previously, the given
  tactic script had to work for _all_ goals, and one had to resort to tactic
  combinators like `first`:

  ```diff
   def foo (n : Nat) := … foo e1 … foo e2 …
  -decreasing_by
  -simp_wf
  -first | apply something_about_e1; …
  -      | apply something_about_e2; …
  +decreasing_by
  +all_goals simp_wf
  +· apply something_about_e1; …
  +· apply something_about_e2; …
  ```

  To obtain the old behaviour of applying a tactic to each goal individually,
  use `all_goals`:
  ```diff
   def foo (n : Nat) := …
  -decreasing_by some_tactic
  +decreasing_by all_goals some_tactic
  ```

  In the case of mutual recursion each `decreasing_by` now applies to just its
  function. If some functions in a recursive group do not have their own
  `decreasing_by`, the default `decreasing_tactic` is used. If the same tactic
  ought to be applied to multiple functions, the `decreasing_by` clause has to
  be repeated at each of these functions.

* Modify `InfoTree.context` to facilitate augmenting it with partial contexts while elaborating a command. This breaks backwards compatibility with all downstream projects that traverse the `InfoTree` manually instead of going through the functions in `InfoUtils.lean`, as well as those manually creating and saving `InfoTree`s. See [PR #3159](https://github.com/leanprover/lean4/pull/3159) for how to migrate your code.

* Add language server support for [call hierarchy requests](https://www.youtube.com/watch?v=r5LA7ivUb2c) ([PR #3082](https://github.com/leanprover/lean4/pull/3082)). The change to the .ilean format in this PR means that projects must be fully rebuilt once in order to generate .ilean files with the new format before features like "find references" work correctly again.

* Structure instances with multiple sources (for example `{a, b, c with x := 0}`) now have their fields filled from these sources
  in strict left-to-right order. Furthermore, the structure instance elaborator now aggressively use sources to fill in subobject
  fields, which prevents unnecessary eta expansion of the sources,
  and hence greatly reduces the reliance on costly structure eta reduction. This has a large impact on mathlib,
  reducing total CPU instructions by 3% and enabling impactful refactors like leanprover-community/mathlib4#8386
  which reduces the build time by almost 20%.
  See [PR #2478](https://github.com/leanprover/lean4/pull/2478) and [RFC #2451](https://github.com/leanprover/lean4/issues/2451).

* Add pretty printer settings to omit deeply nested terms (`pp.deepTerms false` and `pp.deepTerms.threshold`) ([PR #3201](https://github.com/leanprover/lean4/pull/3201))

* Add pretty printer options `pp.numeralTypes` and `pp.natLit`.
  When `pp.numeralTypes` is true, then natural number literals, integer literals, and rational number literals
  are pretty printed with type ascriptions, such as `(2 : Rat)`, `(-2 : Rat)`, and `(-2 / 3 : Rat)`.
  When `pp.natLit` is true, then raw natural number literals are pretty printed as `nat_lit 2`.
  [PR #2933](https://github.com/leanprover/lean4/pull/2933) and [RFC #3021](https://github.com/leanprover/lean4/issues/3021).

Lake updates:
* improved platform information & control [#3226](https://github.com/leanprover/lean4/pull/3226)
* `lake update` from unsupported manifest versions [#3149](https://github.com/leanprover/lean4/pull/3149)

Other improvements:
* make `intro` be aware of `let_fun` [#3115](https://github.com/leanprover/lean4/pull/3115)
* produce simpler proof terms in `rw` [#3121](https://github.com/leanprover/lean4/pull/3121)
* fuse nested `mkCongrArg` calls in proofs generated by `simp` [#3203](https://github.com/leanprover/lean4/pull/3203)
* `induction using` followed by a general term [#3188](https://github.com/leanprover/lean4/pull/3188)
* allow generalization in `let` [#3060](https://github.com/leanprover/lean4/pull/3060), fixing [#3065](https://github.com/leanprover/lean4/issues/3065)
* reducing out-of-bounds `swap!` should return `a`, not `default`` [#3197](https://github.com/leanprover/lean4/pull/3197), fixing [#3196](https://github.com/leanprover/lean4/issues/3196)
* derive `BEq` on structure with `Prop`-fields [#3191](https://github.com/leanprover/lean4/pull/3191), fixing [#3140](https://github.com/leanprover/lean4/issues/3140)
* refine through more `casesOnApp`/`matcherApp` [#3176](https://github.com/leanprover/lean4/pull/3176), fixing [#3175](https://github.com/leanprover/lean4/pull/3175)
* do not strip dotted components from lean module names [#2994](https://github.com/leanprover/lean4/pull/2994), fixing [#2999](https://github.com/leanprover/lean4/issues/2999)
* fix `deriving` only deriving the first declaration for some handlers [#3058](https://github.com/leanprover/lean4/pull/3058), fixing [#3057](https://github.com/leanprover/lean4/issues/3057)
* do not instantiate metavariables in kabstract/rw for disallowed occurrences [#2539](https://github.com/leanprover/lean4/pull/2539), fixing [#2538](https://github.com/leanprover/lean4/issues/2538)
* hover info for `cases h : ...` [#3084](https://github.com/leanprover/lean4/pull/3084)

v4.5.0
---------

* Modify the lexical syntax of string literals to have string gaps, which are escape sequences of the form `"\" newline whitespace*`.
  These have the interpetation of an empty string and allow a string to flow across multiple lines without introducing additional whitespace.
  The following is equivalent to `"this is a string"`.
  ```lean
  "this is \
     a string"
  ```
  [PR #2821](https://github.com/leanprover/lean4/pull/2821) and [RFC #2838](https://github.com/leanprover/lean4/issues/2838).

* Add raw string literal syntax. For example, `r"\n"` is equivalent to `"\\n"`, with no escape processing.
  To include double quote characters in a raw string one can add sufficiently many `#` characters before and after
  the bounding `"`s, as in `r#"the "the" is in quotes"#` for `"the \"the\" is in quotes"`.
  [PR #2929](https://github.com/leanprover/lean4/pull/2929) and [issue #1422](https://github.com/leanprover/lean4/issues/1422).

* The low-level `termination_by'` clause is no longer supported.

  Migration guide: Use `termination_by` instead, e.g.:
  ```diff
  -termination_by' measure (fun ⟨i, _⟩ => as.size - i)
  +termination_by i _ => as.size - i
  ```

  If the well-founded relation you want to use is not the one that the
  `WellFoundedRelation` type class would infer for your termination argument,
  you can use `WellFounded.wrap` from the std libarary to explicitly give one:
  ```diff
  -termination_by' ⟨r, hwf⟩
  +termination_by x => hwf.wrap x
  ```

* Support snippet edits in LSP `TextEdit`s. See `Lean.Lsp.SnippetString` for more details.

* Deprecations and changes in the widget API.
  - `Widget.UserWidgetDefinition` is deprecated in favour of `Widget.Module`. The annotation `@[widget]` is deprecated in favour of `@[widget_module]`. To migrate a definition of type `UserWidgetDefinition`, remove the `name` field and replace the type with `Widget.Module`. Removing the `name` results in a title bar no longer being drawn above your panel widget. To add it back, draw it as part of the component using `<details open=true><summary class='mv2 pointer'>{name}</summary>{rest_of_widget}</details>`. See an example migration [here](https://github.com/leanprover/std4/pull/475/files#diff-857376079661a0c28a53b7ff84701afabbdf529836a6944d106c5294f0e68109R43-R83).
  - The new command `show_panel_widgets` allows displaying always-on and locally-on panel widgets.
  - `RpcEncodable` widget props can now be stored in the infotree.
  - See [RFC 2963](https://github.com/leanprover/lean4/issues/2963) for more details and motivation.

* If no usable lexicographic order can be found automatically for a termination proof, explain why.
  See [feat: GuessLex: if no measure is found, explain why](https://github.com/leanprover/lean4/pull/2960).

* Option to print [inferred termination argument](https://github.com/leanprover/lean4/pull/3012).
  With `set_option showInferredTerminationBy true` you will get messages like
  ```
  Inferred termination argument:
  termination_by
  ackermann n m => (sizeOf n, sizeOf m)
  ```
  for automatically generated `termination_by` clauses.

* More detailed error messages for [invalid mutual blocks](https://github.com/leanprover/lean4/pull/2949).

* [Multiple](https://github.com/leanprover/lean4/pull/2923) [improvements](https://github.com/leanprover/lean4/pull/2969) to the output of `simp?` and `simp_all?`.

* Tactics with `withLocation *` [no longer fail](https://github.com/leanprover/lean4/pull/2917) if they close the main goal.

* Implementation of a `test_extern` command for writing tests for `@[extern]` and `@[implemented_by]` functions.
  Usage is
  ```
  import Lean.Util.TestExtern

  test_extern Nat.add 17 37
  ```
  The head symbol must be the constant with the `@[extern]` or `@[implemented_by]` attribute. The return type must have a `DecidableEq` instance.

Bug fixes for
[#2853](https://github.com/leanprover/lean4/issues/2853), [#2953](https://github.com/leanprover/lean4/issues/2953), [#2966](https://github.com/leanprover/lean4/issues/2966),
[#2971](https://github.com/leanprover/lean4/issues/2971), [#2990](https://github.com/leanprover/lean4/issues/2990), [#3094](https://github.com/leanprover/lean4/issues/3094).

Bug fix for [eager evaluation of default value](https://github.com/leanprover/lean4/pull/3043) in `Option.getD`.
Avoid [panic in `leanPosToLspPos`](https://github.com/leanprover/lean4/pull/3071) when file source is unavailable.
Improve [short-circuiting behavior](https://github.com/leanprover/lean4/pull/2972) for `List.all` and `List.any`.

Several Lake bug fixes: [#3036](https://github.com/leanprover/lean4/issues/3036), [#3064](https://github.com/leanprover/lean4/issues/3064), [#3069](https://github.com/leanprover/lean4/issues/3069).

v4.4.0
---------

* Lake and the language server now support per-package server options using the `moreServerOptions` config field, as well as options that apply to both the language server and `lean` using the `leanOptions` config field. Setting either of these fields instead of `moreServerArgs` ensures that viewing files from a dependency uses the options for that dependency. Additionally, `moreServerArgs` is being deprecated in favor of the `moreGlobalServerArgs` field. See PR [#2858](https://github.com/leanprover/lean4/pull/2858).

  A Lakefile with the following deprecated package declaration:
  ```lean
  def moreServerArgs := #[
    "-Dpp.unicode.fun=true"
  ]
  def moreLeanArgs := moreServerArgs

  package SomePackage where
    moreServerArgs := moreServerArgs
    moreLeanArgs := moreLeanArgs
  ```

  ... can be updated to the following package declaration to use per-package options:
  ```lean
  package SomePackage where
    leanOptions := #[⟨`pp.unicode.fun, true⟩]
  ```
* [Rename request handler](https://github.com/leanprover/lean4/pull/2462).
* [Import auto-completion](https://github.com/leanprover/lean4/pull/2904).
* [`pp.beta`` to apply beta reduction when pretty printing](https://github.com/leanprover/lean4/pull/2864).
* [Embed and check githash in .olean](https://github.com/leanprover/lean4/pull/2766).
* [Guess lexicographic order for well-founded recursion](https://github.com/leanprover/lean4/pull/2874).
* [Allow trailing comma in tuples, lists, and tactics](https://github.com/leanprover/lean4/pull/2643).

Bug fixes for [#2628](https://github.com/leanprover/lean4/issues/2628), [#2883](https://github.com/leanprover/lean4/issues/2883),
[#2810](https://github.com/leanprover/lean4/issues/2810), [#2925](https://github.com/leanprover/lean4/issues/2925), and [#2914](https://github.com/leanprover/lean4/issues/2914).

**Lake:**

* `lake init .` and a bare `lake init` and will now use the current directory as the package name. [#2890](https://github.com/leanprover/lean4/pull/2890)
* `lake new` and `lake init` will now produce errors on invalid package names such as `..`, `foo/bar`, `Init`, `Lean`, `Lake`, and `Main`. See issue [#2637](https://github.com/leanprover/lean4/issues/2637) and PR [#2890](https://github.com/leanprover/lean4/pull/2890).
* `lean_lib` no longer converts its name to upper camel case (e.g., `lean_lib bar` will include modules named `bar.*` rather than `Bar.*`). See issue [#2567](https://github.com/leanprover/lean4/issues/2567) and PR [#2889](https://github.com/leanprover/lean4/pull/2889).
* Lean and Lake now properly support non-identifier library names (e.g., `lake new 123-hello` and `import «123Hello»` now work correctly). See issue [#2865](https://github.com/leanprover/lean4/issues/2865) and PR [#2889](https://github.com/leanprover/lean4/pull/2888).
* Lake now filters the environment extensions loaded from a compiled configuration (`lakefile.olean`) to include only those relevant to Lake's workspace loading process. This resolves segmentation faults caused by environment extension type mismatches (e.g., when defining custom elaborators via `elab` in configurations). See issue [#2632](https://github.com/leanprover/lean4/issues/2632) and PR [#2896](https://github.com/leanprover/lean4/pull/2896).
* Cloud releases will now properly be re-unpacked if the build directory is removed. See PR [#2928](https://github.com/leanprover/lean4/pull/2928).
* Lake's `math` template has been simplified. See PR [#2930](https://github.com/leanprover/lean4/pull/2930).
* `lake exe <target>` now parses `target` like a build target (as the help text states it should) rather than as a basic name. For example, `lake exe @mathlib/runLinter` should now work. See PR [#2932](https://github.com/leanprover/lean4/pull/2932).
* `lake new foo.bar [std]` now generates executables named `foo-bar` and `lake new foo.bar exe` properly creates `foo/bar.lean`. See PR [#2932](https://github.com/leanprover/lean4/pull/2932).
* Later packages and libraries in the dependency tree are now preferred over earlier ones. That is, the later ones "shadow" the earlier ones. Such an ordering is more consistent with how declarations generally work in programming languages. This will break any package that relied on the previous ordering. See issue [#2548](https://github.com/leanprover/lean4/issues/2548) and PR [#2937](https://github.com/leanprover/lean4/pull/2937).
* Executable roots are no longer mistakenly treated as importable. They will no longer be picked up by `findModule?`. See PR [#2937](https://github.com/leanprover/lean4/pull/2937).

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
