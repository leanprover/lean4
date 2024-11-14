# Lean 4 releases

We intend to provide regular "minor version" releases of the Lean language at approximately monthly intervals.
There is not yet a strong guarantee of backwards compatibility between versions,
only an expectation that breaking changes will be documented in this file.

This file contains work-in-progress notes for the upcoming release, as well as previous stable releases.
Please check the [releases](https://github.com/leanprover/lean4/releases) page for the current status
of each version.

v4.15.0
----------

Development in progress.

v4.14.0
----------

Release candidate, release notes will be copied from the branch `releases/v4.14.0` once completed.

v4.13.0
----------

**Full Changelog**: https://github.com/leanprover/lean4/compare/v4.12.0...v4.13.0

### Language features, tactics, and metaprograms

* `structure` command
  * [#5511](https://github.com/leanprover/lean4/pull/5511) allows structure parents to be type synonyms.
  * [#5531](https://github.com/leanprover/lean4/pull/5531) allows default values for structure fields to be noncomputable.

* `rfl` and `apply_rfl` tactics
  * [#3714](https://github.com/leanprover/lean4/pull/3714), [#3718](https://github.com/leanprover/lean4/pull/3718) improve the `rfl` tactic and give better error messages.
  * [#3772](https://github.com/leanprover/lean4/pull/3772) makes `rfl` no longer use kernel defeq for ground terms.
  * [#5329](https://github.com/leanprover/lean4/pull/5329) tags `Iff.refl` with `@[refl]` (@Parcly-Taxel)
  * [#5359](https://github.com/leanprover/lean4/pull/5359) ensures that the `rfl` tactic tries `Iff.rfl` (@Parcly-Taxel)

* `unfold` tactic
  * [#4834](https://github.com/leanprover/lean4/pull/4834) let `unfold` do zeta-delta reduction of local definitions, incorporating functionality of the Mathlib `unfold_let` tactic.

* `omega` tactic
  * [#5382](https://github.com/leanprover/lean4/pull/5382) fixes spurious error in [#5315](https://github.com/leanprover/lean4/issues/5315)
  * [#5523](https://github.com/leanprover/lean4/pull/5523) supports `Int.toNat`

* `simp` tactic
  * [#5479](https://github.com/leanprover/lean4/pull/5479) lets `simp` apply rules with higher-order patterns.

* `induction` tactic
  * [#5494](https://github.com/leanprover/lean4/pull/5494) fixes `induction`’s "pre-tactic" block to always be indented, avoiding unintended uses of it.

* `ac_nf` tactic
  * [#5524](https://github.com/leanprover/lean4/pull/5524) adds `ac_nf`, a counterpart to `ac_rfl`, for normalizing expressions with respect to associativity and commutativity. Tests it with `BitVec` expressions.

* `bv_decide`
  * [#5211](https://github.com/leanprover/lean4/pull/5211) makes `extractLsb'` the primitive `bv_decide` understands, rather than `extractLsb` (@alexkeizer)
  * [#5365](https://github.com/leanprover/lean4/pull/5365) adds `bv_decide` diagnoses.
  * [#5375](https://github.com/leanprover/lean4/pull/5375) adds `bv_decide` normalization rules for `ofBool (a.getLsbD i)` and `ofBool a[i]` (@alexkeizer)
  * [#5423](https://github.com/leanprover/lean4/pull/5423) enhances the rewriting rules of `bv_decide`
  * [#5433](https://github.com/leanprover/lean4/pull/5433) presents the `bv_decide` counterexample at the API
  * [#5484](https://github.com/leanprover/lean4/pull/5484) handles `BitVec.ofNat` with `Nat` fvars in `bv_decide`
  * [#5506](https://github.com/leanprover/lean4/pull/5506), [#5507](https://github.com/leanprover/lean4/pull/5507) add `bv_normalize` rules.
  * [#5568](https://github.com/leanprover/lean4/pull/5568) generalize the `bv_normalize` pipeline to support more general preprocessing passes
  * [#5573](https://github.com/leanprover/lean4/pull/5573) gets `bv_normalize` up-to-date with the current `BitVec` rewrites
  * Cleanups: [#5408](https://github.com/leanprover/lean4/pull/5408), [#5493](https://github.com/leanprover/lean4/pull/5493), [#5578](https://github.com/leanprover/lean4/pull/5578)


* Elaboration improvements
  * [#5266](https://github.com/leanprover/lean4/pull/5266) preserve order of overapplied arguments in `elab_as_elim` procedure.
  * [#5510](https://github.com/leanprover/lean4/pull/5510) generalizes `elab_as_elim` to allow arbitrary motive applications.
  * [#5283](https://github.com/leanprover/lean4/pull/5283), [#5512](https://github.com/leanprover/lean4/pull/5512) refine how named arguments suppress explicit arguments. Breaking change: some previously omitted explicit arguments may need explicit `_` arguments now.
  * [#5376](https://github.com/leanprover/lean4/pull/5376) modifies projection instance binder info for instances, making parameters that are instance implicit in the type be implicit.
  * [#5402](https://github.com/leanprover/lean4/pull/5402) localizes universe metavariable errors to `let` bindings and `fun` binders if possible. Makes "cannot synthesize metavariable" errors take precedence over unsolved universe level errors.
  * [#5419](https://github.com/leanprover/lean4/pull/5419) must not reduce `ite` in the discriminant of `match`-expression when reducibility setting is `.reducible`
  * [#5474](https://github.com/leanprover/lean4/pull/5474) have autoparams report parameter/field on failure
  * [#5530](https://github.com/leanprover/lean4/pull/5530) makes automatic instance names about types with hygienic names be hygienic.

* Deriving handlers
  * [#5432](https://github.com/leanprover/lean4/pull/5432) makes `Repr` deriving instance handle explicit type parameters

* Functional induction
  * [#5364](https://github.com/leanprover/lean4/pull/5364) adds more equalities in context, more careful cleanup.

* Linters
  * [#5335](https://github.com/leanprover/lean4/pull/5335) fixes the unused variables linter complaining about match/tactic combinations
  * [#5337](https://github.com/leanprover/lean4/pull/5337) fixes the unused variables linter complaining about some wildcard patterns

* Other fixes
  * [#4768](https://github.com/leanprover/lean4/pull/4768) fixes a parse error when `..` appears with a `.` on the next line

* Metaprogramming
  * [#3090](https://github.com/leanprover/lean4/pull/3090) handles level parameters in `Meta.evalExpr` (@eric-wieser)  
  * [#5401](https://github.com/leanprover/lean4/pull/5401) instance for `Inhabited (TacticM α)` (@alexkeizer)
  * [#5412](https://github.com/leanprover/lean4/pull/5412) expose Kernel.check for debugging purposes
  * [#5556](https://github.com/leanprover/lean4/pull/5556) improves the "invalid projection" type inference error in `inferType`.
  * [#5587](https://github.com/leanprover/lean4/pull/5587) allows `MVarId.assertHypotheses` to set `BinderInfo` and `LocalDeclKind`.
  * [#5588](https://github.com/leanprover/lean4/pull/5588) adds `MVarId.tryClearMany'`, a variant of `MVarId.tryClearMany`.



### Language server, widgets, and IDE extensions

* [#5205](https://github.com/leanprover/lean4/pull/5205) decreases the latency of auto-completion in tactic blocks.
* [#5237](https://github.com/leanprover/lean4/pull/5237) fixes symbol occurrence highlighting in VS Code not highlighting occurrences when moving the text cursor into the identifier from the right.
* [#5257](https://github.com/leanprover/lean4/pull/5257) fixes several instances of incorrect auto-completions being reported.
* [#5299](https://github.com/leanprover/lean4/pull/5299) allows auto-completion to report completions for global identifiers when the elaborator fails to provide context-specific auto-completions.
* [#5312](https://github.com/leanprover/lean4/pull/5312) fixes the server breaking when changing whitespace after the module header.
* [#5322](https://github.com/leanprover/lean4/pull/5322) fixes several instances of auto-completion reporting non-existent namespaces.
* [#5428](https://github.com/leanprover/lean4/pull/5428) makes sure to always report some recent file range as progress when waiting for elaboration.


### Pretty printing

* [#4979](https://github.com/leanprover/lean4/pull/4979) make pretty printer escape identifiers that are tokens.
* [#5389](https://github.com/leanprover/lean4/pull/5389) makes formatter use the current token table.
* [#5513](https://github.com/leanprover/lean4/pull/5513) use breakable instead of unbreakable whitespace when formatting tokens.


### Library

* [#5222](https://github.com/leanprover/lean4/pull/5222) reduces allocations in `Json.compress`.
* [#5231](https://github.com/leanprover/lean4/pull/5231) upstreams `Zero` and `NeZero`
* [#5292](https://github.com/leanprover/lean4/pull/5292) refactors `Lean.Elab.Deriving.FromToJson` (@arthur-adjedj)
* [#5415](https://github.com/leanprover/lean4/pull/5415) implements `Repr Empty` (@TomasPuverle)
* [#5421](https://github.com/leanprover/lean4/pull/5421) implements `To/FromJSON Empty` (@TomasPuverle)

* Logic
  * [#5263](https://github.com/leanprover/lean4/pull/5263) allows simplifying `dite_not`/`decide_not` with only `Decidable (¬p)`.
  * [#5268](https://github.com/leanprover/lean4/pull/5268) fixes binders on `ite_eq_left_iff`
  * [#5284](https://github.com/leanprover/lean4/pull/5284) turns off `Inhabited (Sum α β)` instances
  * [#5355](https://github.com/leanprover/lean4/pull/5355) adds simp lemmas for `LawfulBEq`
  * [#5374](https://github.com/leanprover/lean4/pull/5374) add `Nonempty` instances for products, allowing more `partial` functions to elaborate successfully
  * [#5447](https://github.com/leanprover/lean4/pull/5447) updates Pi instance names
  * [#5454](https://github.com/leanprover/lean4/pull/5454) makes some instance arguments implicit
  * [#5456](https://github.com/leanprover/lean4/pull/5456) adds `heq_comm`
  * [#5529](https://github.com/leanprover/lean4/pull/5529) moves `@[simp]` from `exists_prop'` to `exists_prop`

* `Bool`
  * [#5228](https://github.com/leanprover/lean4/pull/5228) fills gaps in Bool lemmas
  * [#5332](https://github.com/leanprover/lean4/pull/5332) adds notation `^^` for Bool.xor
  * [#5351](https://github.com/leanprover/lean4/pull/5351) removes `_root_.and` (and or/not/xor) and instead exports/uses `Bool.and` (etc.).

* `BitVec`
  * [#5240](https://github.com/leanprover/lean4/pull/5240) removes BitVec simps with complicated RHS
  * [#5247](https://github.com/leanprover/lean4/pull/5247) `BitVec.getElem_zeroExtend`
  * [#5248](https://github.com/leanprover/lean4/pull/5248) simp lemmas for BitVec, improving confluence
  * [#5249](https://github.com/leanprover/lean4/pull/5249) removes `@[simp]` from some BitVec lemmas
  * [#5252](https://github.com/leanprover/lean4/pull/5252) changes `BitVec.intMin/Max` from abbrev to def
  * [#5278](https://github.com/leanprover/lean4/pull/5278) adds `BitVec.getElem_truncate` (@tobiasgrosser)
  * [#5281](https://github.com/leanprover/lean4/pull/5281) adds udiv/umod bitblasting for `bv_decide` (@bollu)
  * [#5297](https://github.com/leanprover/lean4/pull/5297) `BitVec` unsigned order theoretic results
  * [#5313](https://github.com/leanprover/lean4/pull/5313) adds more basic BitVec ordering theory for UInt
  * [#5314](https://github.com/leanprover/lean4/pull/5314) adds `toNat_sub_of_le` (@bollu)
  * [#5357](https://github.com/leanprover/lean4/pull/5357) adds `BitVec.truncate` lemmas
  * [#5358](https://github.com/leanprover/lean4/pull/5358) introduces `BitVec.setWidth` to unify zeroExtend and truncate (@tobiasgrosser)
  * [#5361](https://github.com/leanprover/lean4/pull/5361) some BitVec GetElem lemmas
  * [#5385](https://github.com/leanprover/lean4/pull/5385) adds `BitVec.ofBool_[and|or|xor]_ofBool` theorems (@tobiasgrosser)
  * [#5404](https://github.com/leanprover/lean4/pull/5404) more of `BitVec.getElem_*` (@tobiasgrosser)
  * [#5410](https://github.com/leanprover/lean4/pull/5410) BitVec analogues of `Nat.{mul_two, two_mul, mul_succ, succ_mul}` (@bollu)
  * [#5411](https://github.com/leanprover/lean4/pull/5411) `BitVec.toNat_{add,sub,mul_of_lt}` for BitVector non-overflow reasoning (@bollu)
  * [#5413](https://github.com/leanprover/lean4/pull/5413) adds `_self`, `_zero`, and `_allOnes` for `BitVec.[and|or|xor]` (@tobiasgrosser)
  * [#5416](https://github.com/leanprover/lean4/pull/5416) adds LawCommIdentity + IdempotentOp for `BitVec.[and|or|xor]` (@tobiasgrosser)
  * [#5418](https://github.com/leanprover/lean4/pull/5418) decidable quantifers for BitVec
  * [#5450](https://github.com/leanprover/lean4/pull/5450) adds `BitVec.toInt_[intMin|neg|neg_of_ne_intMin]` (@tobiasgrosser)
  * [#5459](https://github.com/leanprover/lean4/pull/5459) missing BitVec lemmas
  * [#5469](https://github.com/leanprover/lean4/pull/5469) adds `BitVec.[not_not, allOnes_shiftLeft_or_shiftLeft, allOnes_shiftLeft_and_shiftLeft]` (@luisacicolini)
  * [#5478](https://github.com/leanprover/lean4/pull/5478) adds `BitVec.(shiftLeft_add_distrib, shiftLeft_ushiftRight)` (@luisacicolini)
  * [#5487](https://github.com/leanprover/lean4/pull/5487) adds `sdiv_eq`, `smod_eq` to allow `sdiv`/`smod` bitblasting (@bollu)
  * [#5491](https://github.com/leanprover/lean4/pull/5491) adds `BitVec.toNat_[abs|sdiv|smod]` (@tobiasgrosser)
  * [#5492](https://github.com/leanprover/lean4/pull/5492) `BitVec.(not_sshiftRight, not_sshiftRight_not, getMsb_not, msb_not)` (@luisacicolini)
  * [#5499](https://github.com/leanprover/lean4/pull/5499) `BitVec.Lemmas` - drop non-terminal simps (@tobiasgrosser)
  * [#5505](https://github.com/leanprover/lean4/pull/5505) unsimps `BitVec.divRec_succ'`
  * [#5508](https://github.com/leanprover/lean4/pull/5508) adds `BitVec.getElem_[add|add_add_bool|mul|rotateLeft|rotateRight…` (@tobiasgrosser)
  * [#5554](https://github.com/leanprover/lean4/pull/5554) adds `Bitvec.[add, sub, mul]_eq_xor` and `width_one_cases` (@luisacicolini)

* `List`
  * [#5242](https://github.com/leanprover/lean4/pull/5242) improve naming for `List.mergeSort` lemmas
  * [#5302](https://github.com/leanprover/lean4/pull/5302) provide `mergeSort` comparator autoParam
  * [#5373](https://github.com/leanprover/lean4/pull/5373) fix name of `List.length_mergeSort`
  * [#5377](https://github.com/leanprover/lean4/pull/5377) upstream `map_mergeSort`
  * [#5378](https://github.com/leanprover/lean4/pull/5378) modify signature of lemmas about `mergeSort`
  * [#5245](https://github.com/leanprover/lean4/pull/5245) avoid importing `List.Basic` without List.Impl
  * [#5260](https://github.com/leanprover/lean4/pull/5260) review of List API
  * [#5264](https://github.com/leanprover/lean4/pull/5264) review of List API
  * [#5269](https://github.com/leanprover/lean4/pull/5269) remove HashMap's duplicated Pairwise and Sublist
  * [#5271](https://github.com/leanprover/lean4/pull/5271) remove @[simp] from `List.head_mem` and similar
  * [#5273](https://github.com/leanprover/lean4/pull/5273) lemmas about `List.attach`
  * [#5275](https://github.com/leanprover/lean4/pull/5275) reverse direction of `List.tail_map`
  * [#5277](https://github.com/leanprover/lean4/pull/5277) more `List.attach` lemmas
  * [#5285](https://github.com/leanprover/lean4/pull/5285) `List.count` lemmas
  * [#5287](https://github.com/leanprover/lean4/pull/5287) use boolean predicates in `List.filter`
  * [#5289](https://github.com/leanprover/lean4/pull/5289) `List.mem_ite_nil_left` and analogues
  * [#5293](https://github.com/leanprover/lean4/pull/5293) cleanup of `List.findIdx` / `List.take` lemmas
  * [#5294](https://github.com/leanprover/lean4/pull/5294) switch primes on `List.getElem_take`
  * [#5300](https://github.com/leanprover/lean4/pull/5300) more `List.findIdx` theorems
  * [#5310](https://github.com/leanprover/lean4/pull/5310) fix `List.all/any` lemmas
  * [#5311](https://github.com/leanprover/lean4/pull/5311) fix `List.countP` lemmas
  * [#5316](https://github.com/leanprover/lean4/pull/5316) `List.tail` lemma
  * [#5331](https://github.com/leanprover/lean4/pull/5331) fix implicitness of `List.getElem_mem`
  * [#5350](https://github.com/leanprover/lean4/pull/5350) `List.replicate` lemmas
  * [#5352](https://github.com/leanprover/lean4/pull/5352) `List.attachWith` lemmas
  * [#5353](https://github.com/leanprover/lean4/pull/5353) `List.head_mem_head?`
  * [#5360](https://github.com/leanprover/lean4/pull/5360) lemmas about `List.tail`
  * [#5391](https://github.com/leanprover/lean4/pull/5391) review of `List.erase` / `List.find` lemmas
  * [#5392](https://github.com/leanprover/lean4/pull/5392) `List.fold` / `attach` lemmas
  * [#5393](https://github.com/leanprover/lean4/pull/5393) `List.fold` relators
  * [#5394](https://github.com/leanprover/lean4/pull/5394) lemmas about `List.maximum?`
  * [#5403](https://github.com/leanprover/lean4/pull/5403) theorems about `List.toArray`
  * [#5405](https://github.com/leanprover/lean4/pull/5405) reverse direction of `List.set_map`
  * [#5448](https://github.com/leanprover/lean4/pull/5448) add lemmas about `List.IsPrefix` (@Command-Master)
  * [#5460](https://github.com/leanprover/lean4/pull/5460) missing `List.set_replicate_self`
  * [#5518](https://github.com/leanprover/lean4/pull/5518) rename `List.maximum?` to `max?`
  * [#5519](https://github.com/leanprover/lean4/pull/5519) upstream `List.fold` lemmas
  * [#5520](https://github.com/leanprover/lean4/pull/5520) restore `@[simp]` on `List.getElem_mem` etc.
  * [#5521](https://github.com/leanprover/lean4/pull/5521) List simp fixes
  * [#5550](https://github.com/leanprover/lean4/pull/5550) `List.unattach` and simp lemmas
  * [#5594](https://github.com/leanprover/lean4/pull/5594) induction-friendly `List.min?_cons`

* `Array`
  * [#5246](https://github.com/leanprover/lean4/pull/5246) cleanup imports of Array.Lemmas
  * [#5255](https://github.com/leanprover/lean4/pull/5255) split Init.Data.Array.Lemmas for better bootstrapping
  * [#5288](https://github.com/leanprover/lean4/pull/5288) rename `Array.data` to `Array.toList`
  * [#5303](https://github.com/leanprover/lean4/pull/5303) cleanup of `List.getElem_append` variants
  * [#5304](https://github.com/leanprover/lean4/pull/5304) `Array.not_mem_empty`
  * [#5400](https://github.com/leanprover/lean4/pull/5400) reorganization in Array/Basic
  * [#5420](https://github.com/leanprover/lean4/pull/5420) make `Array` functions either semireducible or use structural recursion
  * [#5422](https://github.com/leanprover/lean4/pull/5422) refactor `DecidableEq (Array α)`
  * [#5452](https://github.com/leanprover/lean4/pull/5452) refactor of Array
  * [#5458](https://github.com/leanprover/lean4/pull/5458) cleanup of Array docstrings after refactor
  * [#5461](https://github.com/leanprover/lean4/pull/5461) restore `@[simp]` on `Array.swapAt!_def`
  * [#5465](https://github.com/leanprover/lean4/pull/5465) improve Array GetElem lemmas
  * [#5466](https://github.com/leanprover/lean4/pull/5466) `Array.foldX` lemmas
  * [#5472](https://github.com/leanprover/lean4/pull/5472) @[simp] lemmas about `List.toArray`
  * [#5485](https://github.com/leanprover/lean4/pull/5485) reverse simp direction for `toArray_concat`
  * [#5514](https://github.com/leanprover/lean4/pull/5514) `Array.eraseReps`
  * [#5515](https://github.com/leanprover/lean4/pull/5515) upstream `Array.qsortOrd`
  * [#5516](https://github.com/leanprover/lean4/pull/5516) upstream `Subarray.empty`
  * [#5526](https://github.com/leanprover/lean4/pull/5526) fix name of `Array.length_toList`
  * [#5527](https://github.com/leanprover/lean4/pull/5527) reduce use of deprecated lemmas in Array
  * [#5534](https://github.com/leanprover/lean4/pull/5534) cleanup of Array GetElem lemmas
  * [#5536](https://github.com/leanprover/lean4/pull/5536) fix `Array.modify` lemmas
  * [#5551](https://github.com/leanprover/lean4/pull/5551) upstream `Array.flatten` lemmas
  * [#5552](https://github.com/leanprover/lean4/pull/5552) switch obvious cases of array "bang"`[]!` indexing to rely on hypothesis (@TomasPuverle)
  * [#5577](https://github.com/leanprover/lean4/pull/5577) add missing simp to `Array.size_feraseIdx`
  * [#5586](https://github.com/leanprover/lean4/pull/5586) `Array/Option.unattach`

* `Option`
  * [#5272](https://github.com/leanprover/lean4/pull/5272) remove @[simp] from `Option.pmap/pbind` and add simp lemmas
  * [#5307](https://github.com/leanprover/lean4/pull/5307) restoring Option simp confluence
  * [#5354](https://github.com/leanprover/lean4/pull/5354) remove @[simp] from `Option.bind_map`
  * [#5532](https://github.com/leanprover/lean4/pull/5532) `Option.attach`
  * [#5539](https://github.com/leanprover/lean4/pull/5539) fix explicitness of `Option.mem_toList`

* `Nat`
  * [#5241](https://github.com/leanprover/lean4/pull/5241) add @[simp] to `Nat.add_eq_zero_iff`
  * [#5261](https://github.com/leanprover/lean4/pull/5261) Nat bitwise lemmas
  * [#5262](https://github.com/leanprover/lean4/pull/5262) `Nat.testBit_add_one` should not be a global simp lemma
  * [#5267](https://github.com/leanprover/lean4/pull/5267) protect some Nat bitwise theorems
  * [#5305](https://github.com/leanprover/lean4/pull/5305) rename Nat bitwise lemmas
  * [#5306](https://github.com/leanprover/lean4/pull/5306) add `Nat.self_sub_mod` lemma
  * [#5503](https://github.com/leanprover/lean4/pull/5503) restore @[simp] to upstreamed `Nat.lt_off_iff`

* `Int`
  * [#5301](https://github.com/leanprover/lean4/pull/5301) rename `Int.div/mod` to `Int.tdiv/tmod`
  * [#5320](https://github.com/leanprover/lean4/pull/5320) add `ediv_nonneg_of_nonpos_of_nonpos` to DivModLemmas (@sakehl)

* `Fin`
  * [#5250](https://github.com/leanprover/lean4/pull/5250) missing lemma about `Fin.ofNat'`
  * [#5356](https://github.com/leanprover/lean4/pull/5356) `Fin.ofNat'` uses `NeZero`
  * [#5379](https://github.com/leanprover/lean4/pull/5379) remove some @[simp]s from Fin lemmas
  * [#5380](https://github.com/leanprover/lean4/pull/5380) missing Fin @[simp] lemmas

* `HashMap`
  * [#5244](https://github.com/leanprover/lean4/pull/5244) (`DHashMap`|`HashMap`|`HashSet`).(`getKey?`|`getKey`|`getKey!`|`getKeyD`)
  * [#5362](https://github.com/leanprover/lean4/pull/5362) remove the last use of `Lean.(HashSet|HashMap)`
  * [#5369](https://github.com/leanprover/lean4/pull/5369) `HashSet.ofArray`
  * [#5370](https://github.com/leanprover/lean4/pull/5370) `HashSet.partition`
  * [#5581](https://github.com/leanprover/lean4/pull/5581) `Singleton`/`Insert`/`Union` instances for `HashMap`/`Set`
  * [#5582](https://github.com/leanprover/lean4/pull/5582) `HashSet.all`/`any`
  * [#5590](https://github.com/leanprover/lean4/pull/5590) adding `Insert`/`Singleton`/`Union` instances for `HashMap`/`Set.Raw`
  * [#5591](https://github.com/leanprover/lean4/pull/5591) `HashSet.Raw.all/any`

* `Monads`
  * [#5463](https://github.com/leanprover/lean4/pull/5463) upstream some monad lemmas
  * [#5464](https://github.com/leanprover/lean4/pull/5464) adjust simp attributes on monad lemmas
  * [#5522](https://github.com/leanprover/lean4/pull/5522) more monadic simp lemmas

* Simp lemma cleanup
  * [#5251](https://github.com/leanprover/lean4/pull/5251) remove redundant simp annotations
  * [#5253](https://github.com/leanprover/lean4/pull/5253) remove Int simp lemmas that can't fire
  * [#5254](https://github.com/leanprover/lean4/pull/5254) variables appearing on both sides of an iff should be implicit
  * [#5381](https://github.com/leanprover/lean4/pull/5381) cleaning up redundant simp lemmas


### Compiler, runtime, and FFI

* [#4685](https://github.com/leanprover/lean4/pull/4685) fixes a typo in the C `run_new_frontend` signature
* [#4729](https://github.com/leanprover/lean4/pull/4729) has IR checker suggest using `noncomputable`
* [#5143](https://github.com/leanprover/lean4/pull/5143) adds a shared library for Lake
* [#5437](https://github.com/leanprover/lean4/pull/5437) removes (syntactically) duplicate imports (@euprunin)
* [#5462](https://github.com/leanprover/lean4/pull/5462) updates `src/lake/lakefile.toml` to the adjusted Lake build process
* [#5541](https://github.com/leanprover/lean4/pull/5541) removes new shared libs before build to better support Windows
* [#5558](https://github.com/leanprover/lean4/pull/5558) make `lean.h` compile with MSVC (@kant2002)
* [#5564](https://github.com/leanprover/lean4/pull/5564) removes non-conforming size-0 arrays (@eric-wieser)


### Lake
  * Reservoir build cache. Lake will now attempt to fetch a pre-built copy of the package from Reservoir before building it. This is only enabled for packages in the leanprover or leanprover-community organizations on versions indexed by Reservoir. Users can force Lake to build packages from the source by passing --no-cache on the CLI or by setting the  LAKE_NO_CACHE environment variable to true. [#5486](https://github.com/leanprover/lean4/pull/5486), [#5572](https://github.com/leanprover/lean4/pull/5572), [#5583](https://github.com/leanprover/lean4/pull/5583), [#5600](https://github.com/leanprover/lean4/pull/5600), [#5641](https://github.com/leanprover/lean4/pull/5641), [#5642](https://github.com/leanprover/lean4/pull/5642).
  * [#5504](https://github.com/leanprover/lean4/pull/5504) lake new and lake init now produce TOML configurations by default.
  * [#5878](https://github.com/leanprover/lean4/pull/5878) fixes a serious issue where Lake would delete path dependencies when attempting to cleanup a dependency required with an incorrect name.

  * **Breaking changes**
    * [#5641](https://github.com/leanprover/lean4/pull/5641) A Lake build of target within a package will no longer build a package's dependencies package-level extra target dependencies. At the technical level, a package's extraDep facet no longer transitively builds its dependencies’ extraDep facets (which include their extraDepTargets).

### Documentation fixes

* [#3918](https://github.com/leanprover/lean4/pull/3918) `@[builtin_doc]` attribute (@digama0)
* [#4305](https://github.com/leanprover/lean4/pull/4305) explains the borrow syntax (@eric-wieser)
* [#5349](https://github.com/leanprover/lean4/pull/5349) adds documentation for `groupBy.loop` (@vihdzp)
* [#5473](https://github.com/leanprover/lean4/pull/5473) fixes typo in `BitVec.mul` docstring (@llllvvuu)
* [#5476](https://github.com/leanprover/lean4/pull/5476) fixes typos in `Lean.MetavarContext`
* [#5481](https://github.com/leanprover/lean4/pull/5481) removes mention of `Lean.withSeconds` (@alexkeizer)
* [#5497](https://github.com/leanprover/lean4/pull/5497) updates documentation and tests for `toUIntX` functions (@TomasPuverle)
* [#5087](https://github.com/leanprover/lean4/pull/5087) mentions that `inferType` does not ensure type correctness
* Many fixes to spelling across the doc-strings, (@euprunin): [#5425](https://github.com/leanprover/lean4/pull/5425) [#5426](https://github.com/leanprover/lean4/pull/5426) [#5427](https://github.com/leanprover/lean4/pull/5427) [#5430](https://github.com/leanprover/lean4/pull/5430)  [#5431](https://github.com/leanprover/lean4/pull/5431) [#5434](https://github.com/leanprover/lean4/pull/5434) [#5435](https://github.com/leanprover/lean4/pull/5435) [#5436](https://github.com/leanprover/lean4/pull/5436) [#5438](https://github.com/leanprover/lean4/pull/5438) [#5439](https://github.com/leanprover/lean4/pull/5439) [#5440](https://github.com/leanprover/lean4/pull/5440) [#5599](https://github.com/leanprover/lean4/pull/5599)

### Changes to CI

* [#5343](https://github.com/leanprover/lean4/pull/5343) allows addition of `release-ci` label via comment (@thorimur)
* [#5344](https://github.com/leanprover/lean4/pull/5344) sets check level correctly during workflow (@thorimur)
* [#5444](https://github.com/leanprover/lean4/pull/5444) Mathlib's `lean-pr-testing-NNNN` branches should use Batteries' `lean-pr-testing-NNNN` branches
* [#5489](https://github.com/leanprover/lean4/pull/5489) commit `lake-manifest.json` when updating `lean-pr-testing` branches
* [#5490](https://github.com/leanprover/lean4/pull/5490) use separate secrets for commenting and branching in `pr-release.yml`

v4.12.0
----------

### Language features, tactics, and metaprograms

* `bv_decide` tactic. This release introduces a new tactic for proving goals involving `BitVec` and `Bool`. It reduces the goal to a SAT instance that is refuted by an external solver, and the resulting LRAT proof is checked in Lean. This is used to synthesize a proof of the goal by reflection. As this process uses verified algorithms, proofs generated by this tactic use `Lean.ofReduceBool`, so this tactic includes the Lean compiler as part of the trusted code base. The external solver CaDiCaL is included with Lean and does not need to be installed separately to make use of `bv_decide`.

  For example, we can use `bv_decide` to verify that a bit twiddling formula leaves at most one bit set:
  ```lean
  def popcount (x : BitVec 64) : BitVec 64 :=
    let rec go (x pop : BitVec 64) : Nat → BitVec 64
      | 0 => pop
      | n + 1 => go (x >>> 2) (pop + (x &&& 1)) n
    go x 0 64

  example (x : BitVec 64) : popcount ((x &&& (x - 1)) ^^^ x) ≤ 1 := by
    simp only [popcount, popcount.go]
    bv_decide
  ```
  When the external solver fails to refute the SAT instance generated by `bv_decide`, it can report a counterexample:
  ```lean
  /--
  error: The prover found a counterexample, consider the following assignment:
  x = 0xffffffffffffffff#64
  -/
  #guard_msgs in
  example (x : BitVec 64) : x < x + 1 := by
    bv_decide
  ```

  See `Lean.Elab.Tactic.BVDecide` for a more detailed overview, and look in `tests/lean/run/bv_*` for examples.

  [#5013](https://github.com/leanprover/lean4/pull/5013), [#5074](https://github.com/leanprover/lean4/pull/5074), [#5100](https://github.com/leanprover/lean4/pull/5100), [#5113](https://github.com/leanprover/lean4/pull/5113), [#5137](https://github.com/leanprover/lean4/pull/5137), [#5203](https://github.com/leanprover/lean4/pull/5203), [#5212](https://github.com/leanprover/lean4/pull/5212), [#5220](https://github.com/leanprover/lean4/pull/5220).

* `simp` tactic
  * [#4988](https://github.com/leanprover/lean4/pull/4988) fixes a panic in the `reducePow` simproc.
  * [#5071](https://github.com/leanprover/lean4/pull/5071) exposes the `index` option to the `dsimp` tactic, introduced to `simp` in [#4202](https://github.com/leanprover/lean4/pull/4202).
  * [#5159](https://github.com/leanprover/lean4/pull/5159) fixes a panic at `Fin.isValue` simproc.
  * [#5167](https://github.com/leanprover/lean4/pull/5167) and [#5175](https://github.com/leanprover/lean4/pull/5175) rename the `simpCtorEq` simproc to `reduceCtorEq` and makes it optional. (See breaking changes.)
  * [#5187](https://github.com/leanprover/lean4/pull/5187) ensures `reduceCtorEq` is enabled in the `norm_cast` tactic.
  * [#5073](https://github.com/leanprover/lean4/pull/5073) modifies the simp debug trace messages to tag with "dpre" and "dpost" instead of "pre" and "post" when in definitional rewrite mode. [#5054](https://github.com/leanprover/lean4/pull/5054) explains the `reduce` steps for `trace.Debug.Meta.Tactic.simp` trace messages.
* `ext` tactic
  * [#4996](https://github.com/leanprover/lean4/pull/4996) reduces default maximum iteration depth from 1000000 to 100.
* `induction` tactic
  * [#5117](https://github.com/leanprover/lean4/pull/5117) fixes a bug where `let` bindings in minor premises wouldn't be counted correctly.

* `omega` tactic
  * [#5157](https://github.com/leanprover/lean4/pull/5157) fixes a panic.

* `conv` tactic
  * [#5149](https://github.com/leanprover/lean4/pull/5149) improves `arg n` to handle subsingleton instance arguments.

* [#5044](https://github.com/leanprover/lean4/pull/5044) upstreams the `#time` command.
* [#5079](https://github.com/leanprover/lean4/pull/5079) makes `#check` and `#reduce` typecheck the elaborated terms.

* **Incrementality**
  * [#4974](https://github.com/leanprover/lean4/pull/4974) fixes regression where we would not interrupt elaboration of previous document versions.
  * [#5004](https://github.com/leanprover/lean4/pull/5004) fixes a performance regression.
  * [#5001](https://github.com/leanprover/lean4/pull/5001) disables incremental body elaboration in presence of `where` clauses in declarations.
  * [#5018](https://github.com/leanprover/lean4/pull/5018) enables infotrees on the command line for ilean generation.
  * [#5040](https://github.com/leanprover/lean4/pull/5040) and [#5056](https://github.com/leanprover/lean4/pull/5056) improve performance of info trees.
  * [#5090](https://github.com/leanprover/lean4/pull/5090) disables incrementality in the `case .. | ..` tactic.
  * [#5312](https://github.com/leanprover/lean4/pull/5312) fixes a bug where changing whitespace after the module header could break subsequent commands.

* **Definitions**
  * [#5016](https://github.com/leanprover/lean4/pull/5016) and [#5066](https://github.com/leanprover/lean4/pull/5066) add `clean_wf` tactic to clean up tactic state in `decreasing_by`. This can be disabled with `set_option debug.rawDecreasingByGoal false`.
  * [#5055](https://github.com/leanprover/lean4/pull/5055) unifies equational theorems between structural and well-founded recursion.
  * [#5041](https://github.com/leanprover/lean4/pull/5041) allows mutually recursive functions to use different parameter names among the “fixed parameter prefix”
  * [#4154](https://github.com/leanprover/lean4/pull/4154) and [#5109](https://github.com/leanprover/lean4/pull/5109) add fine-grained equational lemmas for non-recursive functions. See breaking changes.
  * [#5129](https://github.com/leanprover/lean4/pull/5129) unifies equation lemmas for recursive and non-recursive definitions. The `backward.eqns.deepRecursiveSplit` option can be set to `false` to get the old behavior. See breaking changes.
  * [#5141](https://github.com/leanprover/lean4/pull/5141) adds `f.eq_unfold` lemmas. Now Lean produces the following zoo of rewrite rules:
    ```
    Option.map.eq_1      : Option.map f none = none
    Option.map.eq_2      : Option.map f (some x) = some (f x)
    Option.map.eq_def    : Option.map f p = match o with | none => none | (some x) => some (f x)
    Option.map.eq_unfold : Option.map = fun f p => match o with | none => none | (some x) => some (f x)
    ```
    The `f.eq_unfold` variant is especially useful to rewrite with `rw` under binders.
  * [#5136](https://github.com/leanprover/lean4/pull/5136) fixes bugs in recursion over predicates.

* **Variable inclusion**
  * [#5206](https://github.com/leanprover/lean4/pull/5206) documents that `include` currently only applies to theorems.

* **Elaboration**
  * [#4926](https://github.com/leanprover/lean4/pull/4926) fixes a bug where autoparam errors were associated to an incorrect source position.
  * [#4833](https://github.com/leanprover/lean4/pull/4833) fixes an issue where cdot anonymous functions (e.g. `(· + ·)`) would not handle ambiguous notation correctly. Numbers the parameters, making this example expand as `fun x1 x2 => x1 + x2` rather than `fun x x_1 => x + x_1`.
  * [#5037](https://github.com/leanprover/lean4/pull/5037) improves strength of the tactic that proves array indexing is in bounds.
  * [#5119](https://github.com/leanprover/lean4/pull/5119) fixes a bug in the tactic that proves indexing is in bounds where it could loop in the presence of mvars.
  * [#5072](https://github.com/leanprover/lean4/pull/5072) makes the structure type clickable in "not a field of structure" errors for structure instance notation.
  * [#4717](https://github.com/leanprover/lean4/pull/4717) fixes a bug where mutual `inductive` commands could create terms that the kernel rejects.
  * [#5142](https://github.com/leanprover/lean4/pull/5142) fixes a bug where `variable` could fail when mixing binder updates and declarations.

* **Other fixes or improvements**
  * [#5118](https://github.com/leanprover/lean4/pull/5118) changes the definition of the `syntheticHole` parser so that hovering over `_` in `?_` gives the docstring for synthetic holes.
  * [#5173](https://github.com/leanprover/lean4/pull/5173) uses the emoji variant selector for ✅️,❌️,💥️ in messages, improving fonts selection.
  * [#5183](https://github.com/leanprover/lean4/pull/5183) fixes a bug in `rename_i` where implementation detail hypotheses could be renamed.

### Language server, widgets, and IDE extensions

* [#4821](https://github.com/leanprover/lean4/pull/4821) resolves two language server bugs that especially affect Windows users. (1) Editing the header could result in the watchdog not correctly restarting the file worker, which would lead to the file seemingly being processed forever. (2) On an especially slow Windows machine, we found that starting the language server would sometimes not succeed at all. This PR also resolves an issue where we would not correctly emit messages that we received while the file worker is being restarted to the corresponding file worker after the restart.
* [#5006](https://github.com/leanprover/lean4/pull/5006) updates the user widget manual.
* [#5193](https://github.com/leanprover/lean4/pull/5193) updates the quickstart guide with the new display name for the Lean 4 extension ("Lean 4").
* [#5185](https://github.com/leanprover/lean4/pull/5185) fixes a bug where over time "import out of date" messages would accumulate.
* [#4900](https://github.com/leanprover/lean4/pull/4900) improves ilean loading performance by about a factor of two. Optimizes the JSON parser and the conversion from JSON to Lean data structures; see PR description for details.
* **Other fixes or improvements**
  * [#5031](https://github.com/leanprover/lean4/pull/5031) localizes an instance in `Lsp.Diagnostics`.

### Pretty printing

* [#4976](https://github.com/leanprover/lean4/pull/4976) introduces `@[app_delab]`, a macro for creating delaborators for particular constants. The `@[app_delab ident]` syntax resolves `ident` to its constant name `name` and then expands to `@[delab app.name]`.
* [#4982](https://github.com/leanprover/lean4/pull/4982) fixes a bug where the pretty printer assumed structure projections were type correct (such terms can appear in type mismatch errors). Improves hoverability of `#print` output for structures.
* [#5218](https://github.com/leanprover/lean4/pull/5218) and [#5239](https://github.com/leanprover/lean4/pull/5239) add `pp.exprSizes` debugging option. When true, each pretty printed expression is prefixed with `[size a/b/c]`, where `a` is the size without sharing, `b` is the actual size, and `c` is the size with the maximum possible sharing.

### Library

* [#5020](https://github.com/leanprover/lean4/pull/5020) swaps the parameters to `Membership.mem`. A purpose of this change is to make set-like `CoeSort` coercions to refer to the eta-expanded function `fun x => Membership.mem s x`, which can reduce in many computations. Another is that having the `s` argument first leads to better discrimination tree keys. (See breaking changes.)
* `Array`
  * [#4970](https://github.com/leanprover/lean4/pull/4970) adds `@[ext]` attribute to `Array.ext`.
  * [#4957](https://github.com/leanprover/lean4/pull/4957) deprecates `Array.get_modify`.
* `List`
  * [#4995](https://github.com/leanprover/lean4/pull/4995) upstreams `List.findIdx` lemmas.
  * [#5029](https://github.com/leanprover/lean4/pull/5029), [#5048](https://github.com/leanprover/lean4/pull/5048) and [#5132](https://github.com/leanprover/lean4/pull/5132) add `List.Sublist` lemmas, some upstreamed. [#5077](https://github.com/leanprover/lean4/pull/5077) fixes implicitness in refl/rfl lemma binders.  add `List.Sublist` theorems.
  * [#5047](https://github.com/leanprover/lean4/pull/5047) upstreams `List.Pairwise` lemmas.
  * [#5053](https://github.com/leanprover/lean4/pull/5053), [#5124](https://github.com/leanprover/lean4/pull/5124), and [#5161](https://github.com/leanprover/lean4/pull/5161) add `List.find?/findSome?/findIdx?` theorems.
  * [#5039](https://github.com/leanprover/lean4/pull/5039) adds `List.foldlRecOn` and `List.foldrRecOn` recursion principles to prove things about `List.foldl` and `List.foldr`.
  * [#5069](https://github.com/leanprover/lean4/pull/5069) upstreams `List.Perm`.
  * [#5092](https://github.com/leanprover/lean4/pull/5092) and [#5107](https://github.com/leanprover/lean4/pull/5107) add `List.mergeSort` and a fast `@[csimp]` implementation.
  * [#5103](https://github.com/leanprover/lean4/pull/5103) makes the simp lemmas for `List.subset` more aggressive.
  * [#5106](https://github.com/leanprover/lean4/pull/5106) changes the statement of `List.getLast?_cons`.
  * [#5123](https://github.com/leanprover/lean4/pull/5123) and [#5158](https://github.com/leanprover/lean4/pull/5158) add `List.range` and `List.iota` lemmas.
  * [#5130](https://github.com/leanprover/lean4/pull/5130) adds `List.join` lemmas.
  * [#5131](https://github.com/leanprover/lean4/pull/5131) adds `List.append` lemmas.
  * [#5152](https://github.com/leanprover/lean4/pull/5152) adds `List.erase(|P|Idx)` lemmas.
  * [#5127](https://github.com/leanprover/lean4/pull/5127) makes miscellaneous lemma updates.
  * [#5153](https://github.com/leanprover/lean4/pull/5153) and [#5160](https://github.com/leanprover/lean4/pull/5160) add lemmas about `List.attach` and `List.pmap`.
  * [#5164](https://github.com/leanprover/lean4/pull/5164), [#5177](https://github.com/leanprover/lean4/pull/5177), and [#5215](https://github.com/leanprover/lean4/pull/5215) add `List.find?` and `List.range'/range/iota` lemmas.
  * [#5196](https://github.com/leanprover/lean4/pull/5196) adds `List.Pairwise_erase` and related lemmas.
  * [#5151](https://github.com/leanprover/lean4/pull/5151) and [#5163](https://github.com/leanprover/lean4/pull/5163) improve confluence of `List` simp lemmas. [#5105](https://github.com/leanprover/lean4/pull/5105) and [#5102](https://github.com/leanprover/lean4/pull/5102) adjust `List` simp lemmas.
  * [#5178](https://github.com/leanprover/lean4/pull/5178) removes `List.getLast_eq_iff_getLast_eq_some` as a simp lemma.
  * [#5210](https://github.com/leanprover/lean4/pull/5210) reverses the meaning of `List.getElem_drop` and `List.getElem_drop'`.
  * [#5214](https://github.com/leanprover/lean4/pull/5214) moves `@[csimp]` lemmas earlier where possible.
* `Nat` and `Int`
  * [#5104](https://github.com/leanprover/lean4/pull/5104) adds `Nat.add_left_eq_self` and relatives.
  * [#5146](https://github.com/leanprover/lean4/pull/5146) adds missing `Nat.and_xor_distrib_(left|right)`.
  * [#5148](https://github.com/leanprover/lean4/pull/5148) and [#5190](https://github.com/leanprover/lean4/pull/5190) improve `Nat` and `Int` simp lemma confluence.
  * [#5165](https://github.com/leanprover/lean4/pull/5165) adjusts `Int` simp lemmas.
  * [#5166](https://github.com/leanprover/lean4/pull/5166) adds `Int` lemmas relating `neg` and `emod`/`mod`.
  * [#5208](https://github.com/leanprover/lean4/pull/5208) reverses the direction of the `Int.toNat_sub` simp lemma.
  * [#5209](https://github.com/leanprover/lean4/pull/5209) adds `Nat.bitwise` lemmas.
  * [#5230](https://github.com/leanprover/lean4/pull/5230) corrects the docstrings for integer division and modulus.
* `Option`
  * [#5128](https://github.com/leanprover/lean4/pull/5128) and [#5154](https://github.com/leanprover/lean4/pull/5154) add `Option` lemmas.
* `BitVec`
  * [#4889](https://github.com/leanprover/lean4/pull/4889) adds `sshiftRight` bitblasting.
  * [#4981](https://github.com/leanprover/lean4/pull/4981) adds `Std.Associative` and `Std.Commutative` instances for `BitVec.[and|or|xor]`.
  * [#4913](https://github.com/leanprover/lean4/pull/4913) enables `missingDocs` error for `BitVec` modules.
  * [#4930](https://github.com/leanprover/lean4/pull/4930) makes parameter names for `BitVec` more consistent.
  * [#5098](https://github.com/leanprover/lean4/pull/5098) adds `BitVec.intMin`. Introduces `boolToPropSimps` simp set for converting from boolean to propositional expressions.
  * [#5200](https://github.com/leanprover/lean4/pull/5200) and [#5217](https://github.com/leanprover/lean4/pull/5217) rename `BitVec.getLsb` to `BitVec.getLsbD`, etc., to bring naming in line with `List`/`Array`/etc.
  * **Theorems:** [#4977](https://github.com/leanprover/lean4/pull/4977), [#4951](https://github.com/leanprover/lean4/pull/4951), [#4667](https://github.com/leanprover/lean4/pull/4667), [#5007](https://github.com/leanprover/lean4/pull/5007), [#4997](https://github.com/leanprover/lean4/pull/4997), [#5083](https://github.com/leanprover/lean4/pull/5083), [#5081](https://github.com/leanprover/lean4/pull/5081), [#4392](https://github.com/leanprover/lean4/pull/4392)
* `UInt`
  * [#4514](https://github.com/leanprover/lean4/pull/4514) fixes naming convention for `UInt` lemmas.
* `Std.HashMap` and `Std.HashSet`
  * [#4943](https://github.com/leanprover/lean4/pull/4943) deprecates variants of hash map query methods. (See breaking changes.)
  * [#4917](https://github.com/leanprover/lean4/pull/4917) switches the library and Lean to `Std.HashMap` and `Std.HashSet` almost everywhere.
  * [#4954](https://github.com/leanprover/lean4/pull/4954) deprecates `Lean.HashMap` and `Lean.HashSet`.
  * [#5023](https://github.com/leanprover/lean4/pull/5023) cleans up lemma parameters.

* `Std.Sat` (for `bv_decide`)
  * [#4933](https://github.com/leanprover/lean4/pull/4933) adds definitions of SAT and CNF.
  * [#4953](https://github.com/leanprover/lean4/pull/4953) defines "and-inverter graphs" (AIGs) as described in section 3 of [Davis-Swords 2013](https://arxiv.org/pdf/1304.7861.pdf).

* **Parsec**
  * [#4774](https://github.com/leanprover/lean4/pull/4774) generalizes the `Parsec` library, allowing parsing of iterable data beyond `String` such as `ByteArray`. (See breaking changes.)
  * [#5115](https://github.com/leanprover/lean4/pull/5115) moves `Lean.Data.Parsec` to `Std.Internal.Parsec` for bootstrappng reasons.

* `Thunk`
  * [#4969](https://github.com/leanprover/lean4/pull/4969) upstreams `Thunk.ext`.

* **IO**
  * [#4973](https://github.com/leanprover/lean4/pull/4973) modifies `IO.FS.lines` to handle `\r\n` on all operating systems instead of just on Windows.
  * [#5125](https://github.com/leanprover/lean4/pull/5125) adds `createTempFile` and `withTempFile` for creating temporary files that can only be read and written by the current user.

* **Other fixes or improvements**
  * [#4945](https://github.com/leanprover/lean4/pull/4945) adds `Array`, `Bool` and `Prod` utilities from LeanSAT.
  * [#4960](https://github.com/leanprover/lean4/pull/4960) adds `Relation.TransGen.trans`.
  * [#5012](https://github.com/leanprover/lean4/pull/5012) states `WellFoundedRelation Nat` using `<`, not `Nat.lt`.
  * [#5011](https://github.com/leanprover/lean4/pull/5011) uses `≠` instead of `Not (Eq ...)` in `Fin.ne_of_val_ne`.
  * [#5197](https://github.com/leanprover/lean4/pull/5197) upstreams `Fin.le_antisymm`.
  * [#5042](https://github.com/leanprover/lean4/pull/5042) reduces usage of `refine'`.
  * [#5101](https://github.com/leanprover/lean4/pull/5101) adds about `if-then-else` and `Option`.
  * [#5112](https://github.com/leanprover/lean4/pull/5112) adds basic instances for `ULift` and `PLift`.
  * [#5133](https://github.com/leanprover/lean4/pull/5133) and [#5168](https://github.com/leanprover/lean4/pull/5168) make fixes from running the simpNF linter over Lean.
  * [#5156](https://github.com/leanprover/lean4/pull/5156) removes a bad simp lemma in `omega` theory.
  * [#5155](https://github.com/leanprover/lean4/pull/5155) improves confluence of `Bool` simp lemmas.
  * [#5162](https://github.com/leanprover/lean4/pull/5162) improves confluence of `Function.comp` simp lemmas.
  * [#5191](https://github.com/leanprover/lean4/pull/5191) improves confluence of `if-then-else` simp lemmas.
  * [#5147](https://github.com/leanprover/lean4/pull/5147) adds `@[elab_as_elim]` to `Quot.rec`, `Nat.strongInductionOn` and `Nat.casesStrongInductionOn`, and also renames the latter two to `Nat.strongRecOn` and `Nat.casesStrongRecOn` (deprecated in [#5179](https://github.com/leanprover/lean4/pull/5179)).
  * [#5180](https://github.com/leanprover/lean4/pull/5180) disables some simp lemmas with bad discrimination tree keys.
  * [#5189](https://github.com/leanprover/lean4/pull/5189) cleans up internal simp lemmas that had leaked.
  * [#5198](https://github.com/leanprover/lean4/pull/5198) cleans up `allowUnsafeReducibility`.
  * [#5229](https://github.com/leanprover/lean4/pull/5229) removes unused lemmas from some `simp` tactics.
  * [#5199](https://github.com/leanprover/lean4/pull/5199) removes >6 month deprecations.

### Lean internals

* **Performance**
  * Some core algorithms have been rewritten in C++ for performance.
    * [#4910](https://github.com/leanprover/lean4/pull/4910) and [#4912](https://github.com/leanprover/lean4/pull/4912) reimplement `instantiateLevelMVars`.
    * [#4915](https://github.com/leanprover/lean4/pull/4915), [#4922](https://github.com/leanprover/lean4/pull/4922), and [#4931](https://github.com/leanprover/lean4/pull/4931) reimplement `instantiateExprMVars`, 30% faster on a benchmark.
  * [#4934](https://github.com/leanprover/lean4/pull/4934) has optimizations for the kernel's `Expr` equality test.
  * [#4990](https://github.com/leanprover/lean4/pull/4990) fixes bug in hashing for the kernel's `Expr` equality test.
  * [#4935](https://github.com/leanprover/lean4/pull/4935) and [#4936](https://github.com/leanprover/lean4/pull/4936) skip some `PreDefinition` transformations if they are not needed.
  * [#5225](https://github.com/leanprover/lean4/pull/5225) adds caching for visited exprs at `CheckAssignmentQuick` in `ExprDefEq`.
  * [#5226](https://github.com/leanprover/lean4/pull/5226) maximizes term sharing at `instantiateMVarDeclMVars`, used by `runTactic`.
* **Diagnostics and profiling**
  * [#4923](https://github.com/leanprover/lean4/pull/4923) adds profiling for `instantiateMVars` in `Lean.Elab.MutualDef`, which can be a bottleneck there.
  * [#4924](https://github.com/leanprover/lean4/pull/4924) adds diagnostics for large theorems, controlled by the `diagnostics.threshold.proofSize` option.
  * [#4897](https://github.com/leanprover/lean4/pull/4897) improves display of diagnostic results.
* **Other fixes or improvements**
  * [#4921](https://github.com/leanprover/lean4/pull/4921) cleans up `Expr.betaRev`.
  * [#4940](https://github.com/leanprover/lean4/pull/4940) fixes tests by not writing directly to stdout, which is unreliable now that elaboration and reporting are executed in separate threads.
  * [#4955](https://github.com/leanprover/lean4/pull/4955) documents that `stderrAsMessages` is now the default on the command line as well.
  * [#4647](https://github.com/leanprover/lean4/pull/4647) adjusts documentation for building on macOS.
  * [#4987](https://github.com/leanprover/lean4/pull/4987) makes regular mvar assignments take precedence over delayed ones in `instantiateMVars`. Normally delayed assignment metavariables are never directly assigned, but on errors Lean assigns `sorry` to unassigned metavariables.
  * [#4967](https://github.com/leanprover/lean4/pull/4967) adds linter name to errors when a linter crashes.
  * [#5043](https://github.com/leanprover/lean4/pull/5043) cleans up command line snapshots logic.
  * [#5067](https://github.com/leanprover/lean4/pull/5067) minimizes some imports.
  * [#5068](https://github.com/leanprover/lean4/pull/5068) generalizes the monad for `addMatcherInfo`.
  * [f71a1f](https://github.com/leanprover/lean4/commit/f71a1fb4ae958fccb3ad4d48786a8f47ced05c15) adds missing test for [#5126](https://github.com/leanprover/lean4/issues/5126).
  * [#5201](https://github.com/leanprover/lean4/pull/5201) restores a test.
  * [#3698](https://github.com/leanprover/lean4/pull/3698) fixes a bug where label attributes did not pass on the attribute kind.
  * Typos: [#5080](https://github.com/leanprover/lean4/pull/5080), [#5150](https://github.com/leanprover/lean4/pull/5150), [#5202](https://github.com/leanprover/lean4/pull/5202)

### Compiler, runtime, and FFI

* [#3106](https://github.com/leanprover/lean4/pull/3106) moves frontend to new snapshot architecture. Note that `Frontend.processCommand` and `FrontendM` are no longer used by Lean core, but they will be preserved.
* [#4919](https://github.com/leanprover/lean4/pull/4919) adds missing include in runtime for `AUTO_THREAD_FINALIZATION` feature on Windows.
* [#4941](https://github.com/leanprover/lean4/pull/4941) adds more `LEAN_EXPORT`s for Windows.
* [#4911](https://github.com/leanprover/lean4/pull/4911) improves formatting of CLI help text for the frontend.
* [#4950](https://github.com/leanprover/lean4/pull/4950) improves file reading and writing.
  * `readBinFile` and `readFile` now only require two system calls (`stat` + `read`) instead of one `read` per 1024 byte chunk.
  * `Handle.getLine` and `Handle.putStr` no longer get tripped up by NUL characters.
* [#4971](https://github.com/leanprover/lean4/pull/4971) handles the SIGBUS signal when detecting stack overflows.
* [#5062](https://github.com/leanprover/lean4/pull/5062) avoids overwriting existing signal handlers, like in [rust-lang/rust#69685](https://github.com/rust-lang/rust/pull/69685).
* [#4860](https://github.com/leanprover/lean4/pull/4860) improves workarounds for building on Windows. Splits `libleanshared` on Windows to avoid symbol limit, removes the `LEAN_EXPORT` denylist workaround, adds missing `LEAN_EXPORT`s.
* [#4952](https://github.com/leanprover/lean4/pull/4952) output panics into Lean's redirected stderr, ensuring panics ARE visible as regular messages in the language server and properly ordered in relation to other messages on the command line.
* [#4963](https://github.com/leanprover/lean4/pull/4963) links LibUV.

### Lake

* [#5030](https://github.com/leanprover/lean4/pull/5030) removes dead code.
* [#4770](https://github.com/leanprover/lean4/pull/4770) adds additional fields to the package configuration which will be used by Reservoir. See the PR description for details.


### DevOps/CI
* [#4914](https://github.com/leanprover/lean4/pull/4914) and [#4937](https://github.com/leanprover/lean4/pull/4937) improve the release checklist.
* [#4925](https://github.com/leanprover/lean4/pull/4925) ignores stale leanpkg tests.
* [#5003](https://github.com/leanprover/lean4/pull/5003) upgrades `actions/cache` in CI.
* [#5010](https://github.com/leanprover/lean4/pull/5010) sets `save-always` in cache actions in CI.
* [#5008](https://github.com/leanprover/lean4/pull/5008) adds more libuv search patterns for the speedcenter.
* [#5009](https://github.com/leanprover/lean4/pull/5009) reduce number of runs in the speedcenter for "fast" benchmarks from 10 to 3.
* [#5014](https://github.com/leanprover/lean4/pull/5014) adjusts lakefile editing to use new `git` syntax in `pr-release` workflow.
* [#5025](https://github.com/leanprover/lean4/pull/5025) has `pr-release` workflow pass `--retry` to `curl`.
* [#5022](https://github.com/leanprover/lean4/pull/5022) builds MacOS Aarch64 release for PRs by default.
* [#5045](https://github.com/leanprover/lean4/pull/5045) adds libuv to the required packages heading in macos docs.
* [#5034](https://github.com/leanprover/lean4/pull/5034) fixes the install name of `libleanshared_1` on macOS.
* [#5051](https://github.com/leanprover/lean4/pull/5051) fixes Windows stage 0.
* [#5052](https://github.com/leanprover/lean4/pull/5052) fixes 32bit stage 0 builds in CI.
* [#5057](https://github.com/leanprover/lean4/pull/5057) avoids rebuilding `leanmanifest` in each build.
* [#5099](https://github.com/leanprover/lean4/pull/5099) makes `restart-on-label` workflow also filter by commit SHA.
* [#4325](https://github.com/leanprover/lean4/pull/4325) adds CaDiCaL.

### Breaking changes

* [LibUV](https://libuv.org/) is now required to build Lean. This change only affects developers who compile Lean themselves instead of obtaining toolchains via `elan`. We have updated the official build instructions with information on how to obtain LibUV on our supported platforms. ([#4963](https://github.com/leanprover/lean4/pull/4963))

* Recursive definitions with a `decreasing_by` clause that begins with `simp_wf` may break. Try removing `simp_wf` or replacing it with `simp`. ([#5016](https://github.com/leanprover/lean4/pull/5016))

* The behavior of `rw [f]` where `f` is a non-recursive function defined by pattern matching changed.

  For example, preciously, `rw [Option.map]` would rewrite `Option.map f o` to `match o with … `. Now this rewrite fails because it will use the equational lemmas, and these require constructors – just like for `List.map`.

  Remedies:
  * Split on `o` before rewriting.
  * Use `rw [Option.map.eq_def]`, which rewrites any (saturated) application of `Option.map`.
  * Use `set_option backward.eqns.nonrecursive false` when *defining* the function in question.
  ([#4154](https://github.com/leanprover/lean4/pull/4154))

* The unified handling of equation lemmas for recursive and non-recursive functions can break existing code, as there now can be extra equational lemmas:

  * Explicit uses of `f.eq_2` might have to be adjusted if the numbering changed.

  * Uses of `rw [f]` or `simp [f]` may no longer apply if they previously matched (and introduced a `match` statement), when the equational lemmas got more fine-grained.

    In this case either case analysis on the parameters before rewriting helps, or setting the option `backward.eqns.deepRecursiveSplit false` while *defining* the function.

  ([#5129](https://github.com/leanprover/lean4/pull/5129), [#5207](https://github.com/leanprover/lean4/pull/5207))

* The `reduceCtorEq` simproc is now optional, and it might need to be included in lists of simp lemmas, like `simp only [reduceCtorEq]`. This simproc is responsible for reducing equalities of constructors. ([#5167](https://github.com/leanprover/lean4/pull/5167))

* `Nat.strongInductionOn` is now `Nat.strongRecOn` and `Nat.caseStrongInductionOn` to `Nat.caseStrongRecOn`. ([#5147](https://github.com/leanprover/lean4/pull/5147))

* The parameters to `Membership.mem` have been swapped, which affects all `Membership` instances. ([#5020](https://github.com/leanprover/lean4/pull/5020))

* The meanings of `List.getElem_drop` and `List.getElem_drop'` have been reversed and the first is now a simp lemma. ([#5210](https://github.com/leanprover/lean4/pull/5210))

* The `Parsec` library has moved from `Lean.Data.Parsec` to `Std.Internal.Parsec`. The `Parsec` type is now more general with a parameter for an iterable. Users parsing strings can migrate to `Parser` in the `Std.Internal.Parsec.String` namespace, which also includes string-focused parsing combinators. ([#4774](https://github.com/leanprover/lean4/pull/4774))

* The `Lean` module has switched from `Lean.HashMap` and `Lean.HashSet` to `Std.HashMap` and `Std.HashSet` ([#4943](https://github.com/leanprover/lean4/pull/4943)). `Lean.HashMap` and `Lean.HashSet` are now deprecated ([#4954](https://github.com/leanprover/lean4/pull/4954)) and will be removed in a future release. Users of `Lean` APIs that interact with hash maps, for example `Lean.Environment.const2ModIdx`, might encounter minor breakage due to the following changes from `Lean.HashMap` to `Std.HashMap`:
  * query functions use the term `get` instead of `find`, ([#4943](https://github.com/leanprover/lean4/pull/4943))
  * the notation `map[key]` no longer returns an optional value but instead expects a proof that the key is present in the map. The previous behavior is available via the `map[key]?` notation.


v4.11.0
----------

### Language features, tactics, and metaprograms

* The variable inclusion mechanism has been changed. Like before, when a definition mentions a variable, Lean will add it as an argument of the definition, but now in theorem bodies, variables are not included based on usage in order to ensure that changes to the proof cannot change the statement of the overall theorem. Instead, variables are only available to the proof if they have been mentioned in the theorem header or in an **`include` command** or are instance implicit and depend only on such variables. The **`omit` command** can be used to omit included variables.

  See breaking changes below.

  PRs: [#4883](https://github.com/leanprover/lean4/pull/4883), [#4814](https://github.com/leanprover/lean4/pull/4814), [#5000](https://github.com/leanprover/lean4/pull/5000), [#5036](https://github.com/leanprover/lean4/pull/5036), [#5138](https://github.com/leanprover/lean4/pull/5138), [0edf1b](https://github.com/leanprover/lean4/commit/0edf1bac392f7e2fe0266b28b51c498306363a84).

* **Recursive definitions**
  * Structural recursion can now be explicitly requested using
    ```
    termination_by structural x
    ```
    in analogy to the existing `termination_by x` syntax that causes well-founded recursion to be used.
    [#4542](https://github.com/leanprover/lean4/pull/4542)
  * [#4672](https://github.com/leanprover/lean4/pull/4672) fixes a bug that could lead to ill-typed terms.
  * The `termination_by?` syntax no longer forces the use of well-founded recursion, and when structural
    recursion is inferred, it will print the result using the `termination_by structural` syntax.
  * **Mutual structural recursion** is now supported. This feature supports both mutual recursion over a non-mutual
    data type, as well as recursion over mutual or nested data types:

    ```lean
    mutual
    def Even : Nat → Prop
      | 0 => True
      | n+1 => Odd n

    def Odd : Nat → Prop
      | 0 => False
      | n+1 => Even n
    end

    mutual
    inductive A
    | other : B → A
    | empty
    inductive B
    | other : A → B
    | empty
    end

    mutual
    def A.size : A → Nat
    | .other b => b.size + 1
    | .empty => 0

    def B.size : B → Nat
    | .other a => a.size + 1
    | .empty => 0
    end

    inductive Tree where | node : List Tree → Tree

    mutual
    def Tree.size : Tree → Nat
    | node ts => Tree.list_size ts

    def Tree.list_size : List Tree → Nat
    | [] => 0
    | t::ts => Tree.size t + Tree.list_size ts
    end
    ```

    Functional induction principles are generated for these functions as well (`A.size.induct`, `A.size.mutual_induct`).

    Nested structural recursion is still not supported.

    PRs: [#4639](https://github.com/leanprover/lean4/pull/4639), [#4715](https://github.com/leanprover/lean4/pull/4715), [#4642](https://github.com/leanprover/lean4/pull/4642), [#4656](https://github.com/leanprover/lean4/pull/4656), [#4684](https://github.com/leanprover/lean4/pull/4684), [#4715](https://github.com/leanprover/lean4/pull/4715), [#4728](https://github.com/leanprover/lean4/pull/4728), [#4575](https://github.com/leanprover/lean4/pull/4575), [#4731](https://github.com/leanprover/lean4/pull/4731), [#4658](https://github.com/leanprover/lean4/pull/4658), [#4734](https://github.com/leanprover/lean4/pull/4734), [#4738](https://github.com/leanprover/lean4/pull/4738), [#4718](https://github.com/leanprover/lean4/pull/4718), [#4733](https://github.com/leanprover/lean4/pull/4733), [#4787](https://github.com/leanprover/lean4/pull/4787), [#4788](https://github.com/leanprover/lean4/pull/4788), [#4789](https://github.com/leanprover/lean4/pull/4789), [#4807](https://github.com/leanprover/lean4/pull/4807), [#4772](https://github.com/leanprover/lean4/pull/4772)
  * [#4809](https://github.com/leanprover/lean4/pull/4809) makes unnecessary `termination_by` clauses cause warnings, not errors.
  * [#4831](https://github.com/leanprover/lean4/pull/4831) improves handling of nested structural recursion through non-recursive types.
  * [#4839](https://github.com/leanprover/lean4/pull/4839) improves support for structural recursive over inductive predicates when there are reflexive arguments.
* `simp` tactic
  * [#4784](https://github.com/leanprover/lean4/pull/4784) sets configuration `Simp.Config.implicitDefEqProofs` to `true` by default.

* `omega` tactic
  * [#4612](https://github.com/leanprover/lean4/pull/4612) normalizes the order that constraints appear in error messages.
  * [#4695](https://github.com/leanprover/lean4/pull/4695) prevents pushing casts into multiplications unless it produces a non-trivial linear combination.
  * [#4989](https://github.com/leanprover/lean4/pull/4989) fixes a regression.

* `decide` tactic
  * [#4711](https://github.com/leanprover/lean4/pull/4711) switches from using default transparency to *at least* default transparency when reducing the `Decidable` instance.
  * [#4674](https://github.com/leanprover/lean4/pull/4674) adds detailed feedback on `decide` tactic failure. It tells you which `Decidable` instances it unfolded, if it get stuck on `Eq.rec` it gives a hint about avoiding tactics when defining `Decidable` instances, and if it gets stuck on `Classical.choice` it gives hints about classical instances being in scope. During this process, it processes `Decidable.rec`s and matches to pin blame on a non-reducing instance.

* `@[ext]` attribute
  * [#4543](https://github.com/leanprover/lean4/pull/4543) and [#4762](https://github.com/leanprover/lean4/pull/4762) make `@[ext]` realize `ext_iff` theorems from user `ext` theorems. Fixes the attribute so that `@[local ext]` and `@[scoped ext]` are usable. The `@[ext (iff := false)]` option can be used to turn off `ext_iff` realization.
  * [#4694](https://github.com/leanprover/lean4/pull/4694) makes "go to definition" work for the generated lemmas. Also adjusts the core library to make use of `ext_iff` generation.
  * [#4710](https://github.com/leanprover/lean4/pull/4710) makes `ext_iff` theorem preserve inst implicit binder types, rather than making all binder types implicit.

* `#eval` command
  * [#4810](https://github.com/leanprover/lean4/pull/4810) introduces a safer `#eval` command that prevents evaluation of terms that contain `sorry`. The motivation is that failing tactics, in conjunction with operations such as array accesses, can lead to the Lean process crashing. Users can use the new `#eval!` command to use the previous unsafe behavior. ([#4829](https://github.com/leanprover/lean4/pull/4829) adjusts a test.)

* [#4447](https://github.com/leanprover/lean4/pull/4447) adds `#discr_tree_key` and `#discr_tree_simp_key` commands, for helping debug discrimination tree failures. The `#discr_tree_key t` command prints the discrimination tree keys for a term `t` (or, if it is a single identifier, the type of that constant). It uses the default configuration for generating keys. The `#discr_tree_simp_key` command is similar to `#discr_tree_key`, but treats the underlying type as one of a simp lemma, that is it transforms it into an equality and produces the key of the left-hand side.

  For example,
  ```
  #discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
  -- bar _ (@OfNat.ofNat Nat _ _)

  #discr_tree_simp_key Nat.add_assoc
  -- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
  ```

* [#4741](https://github.com/leanprover/lean4/pull/4741) changes option parsing to allow user-defined options from the command line. Initial options are now re-parsed and validated after importing. Command line option assignments prefixed with `weak.` are silently discarded if the option name without the prefix does not exist.

* **Deriving handlers**
  * [7253ef](https://github.com/leanprover/lean4/commit/7253ef8751f76bcbe0e6f46dcfa8069699a2bac7) and [a04f3c](https://github.com/leanprover/lean4/commit/a04f3cab5a9fe2870825af6544ca13c5bb766706) improve the construction of the `BEq` deriving handler.
  * [86af04](https://github.com/leanprover/lean4/commit/86af04cc08c0dbbe0e735ea13d16edea3465f850) makes `BEq` deriving handler work when there are dependently typed fields.
  * [#4826](https://github.com/leanprover/lean4/pull/4826) refactors the `DecidableEq` deriving handle to use `termination_by structural`.

* **Metaprogramming**
  * [#4593](https://github.com/leanprover/lean4/pull/4593) adds `unresolveNameGlobalAvoidingLocals`.
  * [#4618](https://github.com/leanprover/lean4/pull/4618) deletes deprecated functions from 2022.
  * [#4642](https://github.com/leanprover/lean4/pull/4642) adds `Meta.lambdaBoundedTelescope`.
  * [#4731](https://github.com/leanprover/lean4/pull/4731) adds `Meta.withErasedFVars`, to enter a context with some fvars erased from the local context.
  * [#4777](https://github.com/leanprover/lean4/pull/4777) adds assignment validation at `closeMainGoal`, preventing users from circumventing the occurs check for tactics such as `exact`.
  * [#4807](https://github.com/leanprover/lean4/pull/4807) introduces `Lean.Meta.PProdN` module for packing and projecting nested `PProd`s.
  * [#5170](https://github.com/leanprover/lean4/pull/5170) fixes `Syntax.unsetTrailing`. A consequence of this is that "go to definition" now works on the last module name in an `import` block (issue [#4958](https://github.com/leanprover/lean4/issues/4958)).


### Language server, widgets, and IDE extensions

* [#4727](https://github.com/leanprover/lean4/pull/4727) makes it so that responses to info view requests come as soon as the relevant tactic has finished execution.
* [#4580](https://github.com/leanprover/lean4/pull/4580) makes it so that whitespace changes do not invalidate imports, and so starting to type the first declaration after imports should no longer cause them to reload.
* [#4780](https://github.com/leanprover/lean4/pull/4780) fixes an issue where hovering over unimported builtin names could result in a panic.

### Pretty printing

* [#4558](https://github.com/leanprover/lean4/pull/4558) fixes the `pp.instantiateMVars` setting and changes the default value to `true`.
* [#4631](https://github.com/leanprover/lean4/pull/4631) makes sure syntax nodes always run their formatters. Fixes an issue where if `ppSpace` appears in a `macro` or `elab` command then it does not format with a space.
* [#4665](https://github.com/leanprover/lean4/pull/4665) fixes a bug where pretty printed signatures (for example in `#check`) were overly hoverable due to `pp.tagAppFns` being set.
* [#4724](https://github.com/leanprover/lean4/pull/4724) makes `match` pretty printer be sensitive to `pp.explicit`, which makes hovering over a `match` in the Infoview show the underlying term.
* [#4764](https://github.com/leanprover/lean4/pull/4764) documents why anonymous constructor notation isn't pretty printed with flattening.
* [#4786](https://github.com/leanprover/lean4/pull/4786) adjusts the parenthesizer so that only the parentheses are hoverable, implemented by having the parentheses "steal" the term info from the parenthesized expression.
* [#4854](https://github.com/leanprover/lean4/pull/4854) allows arbitrarily long sequences of optional arguments to be omitted from the end of applications, versus the previous conservative behavior of omitting up to one optional argument.

### Library

* `Nat`
  * [#4597](https://github.com/leanprover/lean4/pull/4597) adds bitwise lemmas `Nat.and_le_(left|right)`.
  * [#4874](https://github.com/leanprover/lean4/pull/4874) adds simprocs for simplifying bit expressions.
* `Int`
  * [#4903](https://github.com/leanprover/lean4/pull/4903) fixes performance of `HPow Int Nat Int` synthesis by rewriting it as a `NatPow Int` instance.
* `UInt*` and `Fin`
  * [#4605](https://github.com/leanprover/lean4/pull/4605) adds lemmas.
  * [#4629](https://github.com/leanprover/lean4/pull/4629) adds `*.and_toNat`.
* `Option`
  * [#4599](https://github.com/leanprover/lean4/pull/4599) adds `get` lemmas.
  * [#4600](https://github.com/leanprover/lean4/pull/4600) adds `Option.or`, a version of `Option.orElse` that is strict in the second argument.
* `GetElem`
  * [#4603](https://github.com/leanprover/lean4/pull/4603) adds `getElem_congr` to help with rewriting indices.
* `List` and `Array`
  * Upstreamed from Batteries: [#4586](https://github.com/leanprover/lean4/pull/4586) upstreams `List.attach` and `Array.attach`, [#4697](https://github.com/leanprover/lean4/pull/4697) upstreams `List.Subset` and `List.Sublist` and API, [#4706](https://github.com/leanprover/lean4/pull/4706) upstreams basic material on `List.Pairwise` and `List.Nodup`, [#4720](https://github.com/leanprover/lean4/pull/4720) upstreams more `List.erase` API, [#4836](https://github.com/leanprover/lean4/pull/4836) and [#4837](https://github.com/leanprover/lean4/pull/4837) upstream `List.IsPrefix`/`List.IsSuffix`/`List.IsInfix` and add `Decidable` instances, [#4855](https://github.com/leanprover/lean4/pull/4855) upstreams `List.tail`, `List.findIdx`, `List.indexOf`, `List.countP`, `List.count`, and `List.range'`, [#4856](https://github.com/leanprover/lean4/pull/4856) upstreams more List lemmas, [#4866](https://github.com/leanprover/lean4/pull/4866) upstreams `List.pairwise_iff_getElem`, [#4865](https://github.com/leanprover/lean4/pull/4865) upstreams `List.eraseIdx` lemmas.
  * [#4687](https://github.com/leanprover/lean4/pull/4687) adjusts `List.replicate` simp lemmas and simprocs.
  * [#4704](https://github.com/leanprover/lean4/pull/4704) adds characterizations of `List.Sublist`.
  * [#4707](https://github.com/leanprover/lean4/pull/4707) adds simp normal form tests for `List.Pairwise` and `List.Nodup`.
  * [#4708](https://github.com/leanprover/lean4/pull/4708) and [#4815](https://github.com/leanprover/lean4/pull/4815) reorganize lemmas on list getters.
  * [#4765](https://github.com/leanprover/lean4/pull/4765) adds simprocs for literal array accesses such as `#[1,2,3,4,5][2]`.
  * [#4790](https://github.com/leanprover/lean4/pull/4790) removes typeclass assumptions for `List.Nodup.eraseP`.
  * [#4801](https://github.com/leanprover/lean4/pull/4801) adds efficient `usize` functions for array types.
  * [#4820](https://github.com/leanprover/lean4/pull/4820) changes `List.filterMapM` to run left-to-right.
  * [#4835](https://github.com/leanprover/lean4/pull/4835) fills in and cleans up gaps in List API.
  * [#4843](https://github.com/leanprover/lean4/pull/4843), [#4868](https://github.com/leanprover/lean4/pull/4868), and [#4877](https://github.com/leanprover/lean4/pull/4877) correct `List.Subset` lemmas.
  * [#4863](https://github.com/leanprover/lean4/pull/4863) splits `Init.Data.List.Lemmas` into function-specific files.
  * [#4875](https://github.com/leanprover/lean4/pull/4875) fixes statement of `List.take_takeWhile`.
  * Lemmas: [#4602](https://github.com/leanprover/lean4/pull/4602), [#4627](https://github.com/leanprover/lean4/pull/4627), [#4678](https://github.com/leanprover/lean4/pull/4678) for `List.head` and `list.getLast`, [#4723](https://github.com/leanprover/lean4/pull/4723) for `List.erase`, [#4742](https://github.com/leanprover/lean4/pull/4742)
* `ByteArray`
  * [#4582](https://github.com/leanprover/lean4/pull/4582) eliminates `partial` from `ByteArray.toList` and `ByteArray.findIdx?`.
* `BitVec`
  * [#4568](https://github.com/leanprover/lean4/pull/4568) adds recurrence theorems for bitblasting multiplication.
  * [#4571](https://github.com/leanprover/lean4/pull/4571) adds `shiftLeftRec` lemmas.
  * [#4872](https://github.com/leanprover/lean4/pull/4872) adds `ushiftRightRec` and lemmas.
  * [#4873](https://github.com/leanprover/lean4/pull/4873) adds `getLsb_replicate`.
* `Std.HashMap` added:
  * [#4583](https://github.com/leanprover/lean4/pull/4583) **adds `Std.HashMap`** as a verified replacement for `Lean.HashMap`. See the PR for naming differences, but [#4725](https://github.com/leanprover/lean4/pull/4725) renames `HashMap.remove` to `HashMap.erase`.
  * [#4682](https://github.com/leanprover/lean4/pull/4682) adds `Inhabited` instances.
  * [#4732](https://github.com/leanprover/lean4/pull/4732) improves `BEq` argument order in hash map lemmas.
  * [#4759](https://github.com/leanprover/lean4/pull/4759) makes lemmas resolve instances via unification.
  * [#4771](https://github.com/leanprover/lean4/pull/4771) documents that hash maps should be used linearly to avoid expensive copies.
  * [#4791](https://github.com/leanprover/lean4/pull/4791) removes `bif` from hash map lemmas, which is inconvenient to work with in practice.
  * [#4803](https://github.com/leanprover/lean4/pull/4803) adds more lemmas.
* `SMap`
  * [#4690](https://github.com/leanprover/lean4/pull/4690) upstreams `SMap.foldM`.
* `BEq`
  * [#4607](https://github.com/leanprover/lean4/pull/4607) adds `PartialEquivBEq`, `ReflBEq`, `EquivBEq`, and `LawfulHashable` classes.
* `IO`
  * [#4660](https://github.com/leanprover/lean4/pull/4660) adds `IO.Process.Child.tryWait`.
* [#4747](https://github.com/leanprover/lean4/pull/4747), [#4730](https://github.com/leanprover/lean4/pull/4730), and [#4756](https://github.com/leanprover/lean4/pull/4756) add `×'` syntax for `PProd`. Adds a delaborator for `PProd` and `MProd` values to pretty print as flattened angle bracket tuples.
* **Other fixes or improvements**
  * [#4604](https://github.com/leanprover/lean4/pull/4604) adds lemmas for cond.
  * [#4619](https://github.com/leanprover/lean4/pull/4619) changes some definitions into theorems.
  * [#4616](https://github.com/leanprover/lean4/pull/4616) fixes some names with duplicated namespaces.
  * [#4620](https://github.com/leanprover/lean4/pull/4620) fixes simp lemmas flagged by the simpNF linter.
  * [#4666](https://github.com/leanprover/lean4/pull/4666) makes the `Antisymm` class be a `Prop`.
  * [#4621](https://github.com/leanprover/lean4/pull/4621) cleans up unused arguments flagged by linter.
  * [#4680](https://github.com/leanprover/lean4/pull/4680) adds imports for orphaned `Init` modules.
  * [#4679](https://github.com/leanprover/lean4/pull/4679) adds imports for orphaned `Std.Data` modules.
  * [#4688](https://github.com/leanprover/lean4/pull/4688) adds forward and backward directions of `not_exists`.
  * [#4689](https://github.com/leanprover/lean4/pull/4689) upstreams `eq_iff_true_of_subsingleton`.
  * [#4709](https://github.com/leanprover/lean4/pull/4709) fixes precedence handling for `Repr` instances for negative numbers for `Int` and `Float`.
  * [#4760](https://github.com/leanprover/lean4/pull/4760) renames `TC` ("transitive closure") to `Relation.TransGen`.
  * [#4842](https://github.com/leanprover/lean4/pull/4842) fixes `List` deprecations.
  * [#4852](https://github.com/leanprover/lean4/pull/4852) upstreams some Mathlib attributes applied to lemmas.
  * [93ac63](https://github.com/leanprover/lean4/commit/93ac635a89daa5a8e8ef33ec96b0bcbb5d7ec1ea) improves proof.
  * [#4862](https://github.com/leanprover/lean4/pull/4862) and [#4878](https://github.com/leanprover/lean4/pull/4878) generalize the universe for `PSigma.exists` and rename it to `Exists.of_psigma_prop`.
  * Typos: [#4737](https://github.com/leanprover/lean4/pull/4737), [7d2155](https://github.com/leanprover/lean4/commit/7d2155943c67c743409420b4546d47fadf73af1c)
  * Docs: [#4782](https://github.com/leanprover/lean4/pull/4782), [#4869](https://github.com/leanprover/lean4/pull/4869), [#4648](https://github.com/leanprover/lean4/pull/4648)

### Lean internals
* **Elaboration**
  * [#4596](https://github.com/leanprover/lean4/pull/4596) enforces `isDefEqStuckEx` at `unstuckMVar` procedure, causing isDefEq to throw a stuck defeq exception if the metavariable was created in a previous level. This results in some better error messages, and it helps `rw` succeed in synthesizing instances (see issue [#2736](https://github.com/leanprover/lean4/issues/2736)).
  * [#4713](https://github.com/leanprover/lean4/pull/4713) fixes deprecation warnings when there are overloaded symbols.
  * `elab_as_elim` algorithm:
    * [#4722](https://github.com/leanprover/lean4/pull/4722) adds check that inferred motive is type-correct.
    * [#4800](https://github.com/leanprover/lean4/pull/4800) elaborates arguments for parameters appearing in the types of targets.
    * [#4817](https://github.com/leanprover/lean4/pull/4817) makes the algorithm correctly handle eliminators with explicit motive arguments.
  * [#4792](https://github.com/leanprover/lean4/pull/4792) adds term elaborator for `Lean.Parser.Term.namedPattern` (e.g. `n@(n' + 1)`) to report errors when used in non-pattern-matching contexts.
  * [#4818](https://github.com/leanprover/lean4/pull/4818) makes anonymous dot notation work when the expected type is a pi-type-valued type synonym.
* **Typeclass inference**
  * [#4646](https://github.com/leanprover/lean4/pull/4646) improves `synthAppInstances`, the function responsible for synthesizing instances for the `rw` and `apply` tactics. Adds a synthesis loop to handle functions whose instances need to be synthesized in a complex order.
* **Inductive types**
  * [#4684](https://github.com/leanprover/lean4/pull/4684) (backported as [98ee78](https://github.com/leanprover/lean4/commit/98ee789990f91ff5935627787b537911ef8773c4)) refactors `InductiveVal` to have a `numNested : Nat` field instead of `isNested : Bool`. This modifies the kernel.
* **Definitions**
  * [#4776](https://github.com/leanprover/lean4/pull/4776) improves performance of `Replacement.apply`.
  * [#4712](https://github.com/leanprover/lean4/pull/4712) fixes `.eq_def` theorem generation with messy universes.
  * [#4841](https://github.com/leanprover/lean4/pull/4841) improves success of finding `T.below x` hypothesis when transforming `match` statements for `IndPredBelow`.
* **Diagnostics and profiling**
  * [#4611](https://github.com/leanprover/lean4/pull/4611) makes kernel diagnostics appear when `diagnostics` is enabled even if it is the only section.
  * [#4753](https://github.com/leanprover/lean4/pull/4753) adds missing `profileitM` functions.
  * [#4754](https://github.com/leanprover/lean4/pull/4754) adds `Lean.Expr.numObjs` to compute the number of allocated sub-expressions in a given expression, primarily for diagnosing performance issues.
  * [#4769](https://github.com/leanprover/lean4/pull/4769) adds missing `withTraceNode`s to improve `trace.profiler` output.
  * [#4781](https://github.com/leanprover/lean4/pull/4781) and [#4882](https://github.com/leanprover/lean4/pull/4882) make the "use `set_option diagnostics true`" message be conditional on current setting of `diagnostics`.
* **Performance**
  * [#4767](https://github.com/leanprover/lean4/pull/4767), [#4775](https://github.com/leanprover/lean4/pull/4775), and [#4887](https://github.com/leanprover/lean4/pull/4887) add `ShareCommon.shareCommon'` for sharing common terms. In an example with 16 million subterms, it is 20 times faster than the old `shareCommon` procedure.
  * [#4779](https://github.com/leanprover/lean4/pull/4779) ensures `Expr.replaceExpr` preserves DAG structure in `Expr`s.
  * [#4783](https://github.com/leanprover/lean4/pull/4783) documents performance issue in `Expr.replaceExpr`.
  * [#4794](https://github.com/leanprover/lean4/pull/4794), [#4797](https://github.com/leanprover/lean4/pull/4797), [#4798](https://github.com/leanprover/lean4/pull/4798) make `for_each` use precise cache.
  * [#4795](https://github.com/leanprover/lean4/pull/4795) makes `Expr.find?` and `Expr.findExt?` use the kernel implementations.
  * [#4799](https://github.com/leanprover/lean4/pull/4799) makes `Expr.replace` use the kernel implementation.
  * [#4871](https://github.com/leanprover/lean4/pull/4871) makes `Expr.foldConsts` use a precise cache.
  * [#4890](https://github.com/leanprover/lean4/pull/4890) makes `expr_eq_fn` use a precise cache.
* **Utilities**
  * [#4453](https://github.com/leanprover/lean4/pull/4453) upstreams `ToExpr FilePath` and `compile_time_search_path%`.
* **Module system**
  * [#4652](https://github.com/leanprover/lean4/pull/4652) fixes handling of `const2ModIdx` in `finalizeImport`, making it prefer the original module for a declaration when a declaration is re-declared.
* **Kernel**
  * [#4637](https://github.com/leanprover/lean4/pull/4637) adds a check to prevent large `Nat` exponentiations from evaluating. Elaborator reduction is controlled by the option `exponentiation.threshold`.
  * [#4683](https://github.com/leanprover/lean4/pull/4683) updates comments in `kernel/declaration.h`, making sure they reflect the current Lean 4 types.
  * [#4796](https://github.com/leanprover/lean4/pull/4796) improves performance by using `replace` with a precise cache.
  * [#4700](https://github.com/leanprover/lean4/pull/4700) improves performance by fixing the implementation of move constructors and move assignment operators. Expression copying was taking 10% of total runtime in some workloads. See issue [#4698](https://github.com/leanprover/lean4/issues/4698).
  * [#4702](https://github.com/leanprover/lean4/pull/4702) improves performance in `replace_rec_fn::apply` by avoiding expression copies. These copies represented about 13% of time spent in `save_result` in some workloads. See the same issue.
* **Other fixes or improvements**
  * [#4590](https://github.com/leanprover/lean4/pull/4590) fixes a typo in some constants and `trace.profiler.useHeartbeats`.
  * [#4617](https://github.com/leanprover/lean4/pull/4617) add 'since' dates to `deprecated` attributes.
  * [#4625](https://github.com/leanprover/lean4/pull/4625) improves the robustness of the constructor-as-variable test.
  * [#4740](https://github.com/leanprover/lean4/pull/4740) extends test with nice example reported on Zulip.
  * [#4766](https://github.com/leanprover/lean4/pull/4766) moves `Syntax.hasIdent` to be available earlier and shakes dependencies.
  * [#4881](https://github.com/leanprover/lean4/pull/4881) splits out `Lean.Language.Lean.Types`.
  * [#4893](https://github.com/leanprover/lean4/pull/4893) adds `LEAN_EXPORT` for `sharecommon` functions.
  * Typos: [#4635](https://github.com/leanprover/lean4/pull/4635), [#4719](https://github.com/leanprover/lean4/pull/4719), [af40e6](https://github.com/leanprover/lean4/commit/af40e618111581c82fc44de922368a02208b499f)
  * Docs: [#4748](https://github.com/leanprover/lean4/pull/4748) (`Command.Scope`)

### Compiler, runtime, and FFI
* [#4661](https://github.com/leanprover/lean4/pull/4661) moves `Std` from `libleanshared` to much smaller `libInit_shared`. This fixes the Windows build.
* [#4668](https://github.com/leanprover/lean4/pull/4668) fixes initialization, explicitly initializing `Std` in `lean_initialize`.
* [#4746](https://github.com/leanprover/lean4/pull/4746) adjusts `shouldExport` to exclude more symbols to get below Windows symbol limit. Some exceptions are added by [#4884](https://github.com/leanprover/lean4/pull/4884) and [#4956](https://github.com/leanprover/lean4/pull/4956) to support Verso.
* [#4778](https://github.com/leanprover/lean4/pull/4778) adds `lean_is_exclusive_obj` (`Lean.isExclusiveUnsafe`) and `lean_set_external_data`.
* [#4515](https://github.com/leanprover/lean4/pull/4515) fixes calling programs with spaces on Windows.

### Lake

* [#4735](https://github.com/leanprover/lean4/pull/4735) improves a number of elements related to Git checkouts, cloud releases,
and related error handling.

  * On error, Lake now prints all top-level logs. Top-level logs are those produced by Lake outside of the job monitor (e.g., when cloning dependencies).
  * When fetching a remote for a dependency, Lake now forcibly fetches tags. This prevents potential errors caused by a repository recreating tags already fetched.
  * Git error handling is now more informative.
  * The builtin package facets `release`, `optRelease`, `extraDep` are now captions in the same manner as other facets.
  * `afterReleaseSync` and `afterReleaseAsync` now fetch `optRelease` rather than `release`.
  * Added support for optional jobs, whose failure does not cause the whole build to failure. Now `optRelease` is such a job.

* [#4608](https://github.com/leanprover/lean4/pull/4608) adds draft CI workflow when creating new projects.
* [#4847](https://github.com/leanprover/lean4/pull/4847) adds CLI options to control log levels. The `--log-level=<lv>` controls the minimum log level Lake should output. For instance, `--log-level=error` will only print errors (not warnings or info). Also, adds an analogous `--fail-level` option to control the minimum log level for build failures. The existing `--iofail` and `--wfail` options are respectively equivalent to `--fail-level=info` and `--fail-level=warning`.

* Docs: [#4853](https://github.com/leanprover/lean4/pull/4853)


### DevOps/CI

* **Workflows**
  * [#4531](https://github.com/leanprover/lean4/pull/4531) makes release trigger an update of `release.lean-lang.org`.
  * [#4598](https://github.com/leanprover/lean4/pull/4598) adjusts `pr-release` to the new `lakefile.lean` syntax.
  * [#4632](https://github.com/leanprover/lean4/pull/4632) makes `pr-release` use the correct tag name.
  * [#4638](https://github.com/leanprover/lean4/pull/4638) adds ability to manually trigger nightly release.
  * [#4640](https://github.com/leanprover/lean4/pull/4640) adds more debugging output for `restart-on-label` CI.
  * [#4663](https://github.com/leanprover/lean4/pull/4663) bumps up waiting for 10s to 30s for `restart-on-label`.
  * [#4664](https://github.com/leanprover/lean4/pull/4664) bumps versions for `actions/checkout` and `actions/upload-artifacts`.
  * [582d6e](https://github.com/leanprover/lean4/commit/582d6e7f7168e0dc0819099edaace27d913b893e) bumps version for `actions/download-artifact`.
  * [6d9718](https://github.com/leanprover/lean4/commit/6d971827e253a4dc08cda3cf6524d7f37819eb47) adds back dropped `check-stage3`.
  * [0768ad](https://github.com/leanprover/lean4/commit/0768ad4eb9020af0777587a25a692d181e857c14) adds Jira sync (for FRO).
  * [#4830](https://github.com/leanprover/lean4/pull/4830) adds support to report CI errors on FRO Zulip.
  * [#4838](https://github.com/leanprover/lean4/pull/4838) adds trigger for `nightly_bump_toolchain` on mathlib4 upon nightly release.
  * [abf420](https://github.com/leanprover/lean4/commit/abf4206e9c0fcadf17b6f7933434fd1580175015) fixes msys2.
  * [#4895](https://github.com/leanprover/lean4/pull/4895) deprecates Nix-based builds and removes interactive components. Users who prefer the flake build should maintain it externally.
* [#4693](https://github.com/leanprover/lean4/pull/4693), [#4458](https://github.com/leanprover/lean4/pull/4458), and [#4876](https://github.com/leanprover/lean4/pull/4876) update the **release checklist**.
* [#4669](https://github.com/leanprover/lean4/pull/4669) fixes the "max dynamic symbols" metric per static library.
* [#4691](https://github.com/leanprover/lean4/pull/4691) improves compatibility of `tests/list_simp` for retesting simp normal forms with Mathlib.
* [#4806](https://github.com/leanprover/lean4/pull/4806) updates the quickstart guide.
* [c02aa9](https://github.com/leanprover/lean4/commit/c02aa98c6a08c3a9b05f68039c071085a4ef70d7) documents the **triage team** in the contribution guide.


### Breaking changes

* For `@[ext]`-generated `ext` and `ext_iff` lemmas, the `x` and `y` term arguments are now implicit. Furthermore these two lemmas are now protected ([#4543](https://github.com/leanprover/lean4/pull/4543)).

* Now `trace.profiler.useHearbeats` is `trace.profiler.useHeartbeats` ([#4590](https://github.com/leanprover/lean4/pull/4590)).

* A bugfix in the structural recursion code may in some cases break existing code, when a parameter of the type of the recursive argument is bound behind indices of that type. This can usually be fixed by reordering the parameters of the function ([#4672](https://github.com/leanprover/lean4/pull/4672)).

* Now `List.filterMapM` sequences monadic actions left-to-right ([#4820](https://github.com/leanprover/lean4/pull/4820)).

* The effect of the `variable` command on proofs of `theorem`s has been changed. Whether such section variables are accessible in the proof now depends only on the theorem signature and other top-level commands, not on the proof itself. This change ensures that
  * the statement of a theorem is independent of its proof. In other words, changes in the proof cannot change the theorem statement.
  * tactics such as `induction` cannot accidentally include a section variable.
  * the proof can be elaborated in parallel to subsequent declarations in a future version of Lean.

  The effect of `variable`s on the theorem header as well as on other kinds of declarations is unchanged.

  Specifically, section variables are included if they
  * are directly referenced by the theorem header,
  * are included via the new `include` command in the current section and not subsequently mentioned in an `omit` statement,
  * are directly referenced by any variable included by these rules, OR
  * are instance-implicit variables that reference only variables included by these rules.

  For porting, a new option `deprecated.oldSectionVars` is included to locally switch back to the old behavior.



v4.10.0
----------

### Language features, tactics, and metaprograms

* `split` tactic:
  * [#4401](https://github.com/leanprover/lean4/pull/4401) improves the strategy `split` uses to generalize discriminants of matches and adds `trace.split.failure` trace class for diagnosing issues.

* `rw` tactic:
  * [#4385](https://github.com/leanprover/lean4/pull/4385) prevents the tactic from claiming pre-existing goals are new subgoals.
  * [dac1da](https://github.com/leanprover/lean4/commit/dac1dacc5b39911827af68247d575569d9c399b5) adds configuration for ordering new goals, like for `apply`.

* `simp` tactic:
  * [#4430](https://github.com/leanprover/lean4/pull/4430) adds `dsimproc`s for `if` expressions (`ite` and `dite`).
  * [#4434](https://github.com/leanprover/lean4/pull/4434) improves heuristics for unfolding. Equational lemmas now have priorities where more-specific equationals lemmas are tried first before a possible catch-all.
  * [#4481](https://github.com/leanprover/lean4/pull/4481) fixes an issue where function-valued `OfNat` numeric literals would become denormalized.
  * [#4467](https://github.com/leanprover/lean4/pull/4467) fixes an issue where dsimp theorems might not apply to literals.
  * [#4484](https://github.com/leanprover/lean4/pull/4484) fixes the source position for the warning for deprecated simp arguments.
  * [#4258](https://github.com/leanprover/lean4/pull/4258) adds docstrings for `dsimp` configuration.
  * [#4567](https://github.com/leanprover/lean4/pull/4567) improves the accuracy of used simp lemmas reported by `simp?`.
  * [fb9727](https://github.com/leanprover/lean4/commit/fb97275dcbb683efe6da87ed10a3f0cd064b88fd) adds (but does not implement) the simp configuration option `implicitDefEqProofs`, which will enable including `rfl`-theorems in proof terms.
* `omega` tactic:
  * [#4360](https://github.com/leanprover/lean4/pull/4360) makes the tactic generate error messages lazily, improving its performance when used in tactic combinators.
* `bv_omega` tactic:
  * [#4579](https://github.com/leanprover/lean4/pull/4579) works around changes to the definition of `Fin.sub` in this release.
* [#4490](https://github.com/leanprover/lean4/pull/4490) sets up groundwork for a tactic index in generated documentation, as there was in Lean 3. See PR description for details.

* **Commands**
  * [#4370](https://github.com/leanprover/lean4/pull/4370) makes the `variable` command fully elaborate binders during validation, fixing an issue where some errors would be reported only at the next declaration.
  * [#4408](https://github.com/leanprover/lean4/pull/4408) fixes a discrepancy in universe parameter order between `theorem` and `def` declarations.
  * [#4493](https://github.com/leanprover/lean4/pull/4493) and
    [#4482](https://github.com/leanprover/lean4/pull/4482) fix a discrepancy in the elaborators for `theorem`, `def`, and `example`,
    making `Prop`-valued `example`s and other definition commands elaborate like `theorem`s.
  * [8f023b](https://github.com/leanprover/lean4/commit/8f023b85c554186ae562774b8122322d856c674e), [3c4d6b](https://github.com/leanprover/lean4/commit/3c4d6ba8648eb04d90371eb3fdbd114d16949501) and [0783d0](https://github.com/leanprover/lean4/commit/0783d0fcbe31b626fbd3ed2f29d838e717f09101) change the `#reduce` command to be able to control what gets reduced.
    For example, `#reduce (proofs := true) (types := false) e` reduces both proofs and types in the expression `e`.
    By default, neither proofs or types are reduced.
  * [#4489](https://github.com/leanprover/lean4/pull/4489) fixes an elaboration bug in `#check_tactic`.
  * [#4505](https://github.com/leanprover/lean4/pull/4505) adds support for `open _root_.<namespace>`.

* **Options**
  * [#4576](https://github.com/leanprover/lean4/pull/4576) adds the `debug.byAsSorry` option. Setting `set_option debug.byAsSorry true` causes all `by ...` terms to elaborate as `sorry`.
  * [7b56eb](https://github.com/leanprover/lean4/commit/7b56eb20a03250472f4b145118ae885274d1f8f7) and [d8e719](https://github.com/leanprover/lean4/commit/d8e719f9ab7d049e423473dfc7a32867d32c856f) add the `debug.skipKernelTC` option. Setting `set_option debug.skipKernelTC true` turns off kernel typechecking. This is meant for temporarily working around kernel performance issues, and it compromises soundness since buggy tactics may produce invalid proofs, which will not be caught if this option is set to true.

* [#4301](https://github.com/leanprover/lean4/pull/4301)
  adds a linter to flag situations where a local variable's name is one of
  the argumentless constructors of its type. This can arise when a user either
  doesn't open a namespace or doesn't add a dot or leading qualifier, as
  in the following:

  ```lean
  inductive Tree (α : Type) where
    | leaf
    | branch (left : Tree α) (val : α) (right : Tree α)

  def depth : Tree α → Nat
    | leaf => 0
  ```

  With this linter, the `leaf` pattern is highlighted as a local
  variable whose name overlaps with the constructor `Tree.leaf`.

  The linter can be disabled with `set_option linter.constructorNameAsVariable false`.

  Additionally, the error message that occurs when a name in a pattern that takes arguments isn't valid now suggests similar names that would be valid. This means that the following definition:

  ```lean
  def length (list : List α) : Nat :=
    match list with
    | nil => 0
    | cons x xs => length xs + 1
  ```

  now results in the following warning:

  ```
  warning: Local variable 'nil' resembles constructor 'List.nil' - write '.nil' (with a dot) or 'List.nil' to use the constructor.
  note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
  ```

  and error:

  ```
  invalid pattern, constructor or constant marked with '[match_pattern]' expected

  Suggestion: 'List.cons' is similar
  ```

* **Metaprogramming**
  * [#4454](https://github.com/leanprover/lean4/pull/4454) adds public `Name.isInternalDetail` function for filtering declarations using naming conventions for internal names.

* **Other fixes or improvements**
  * [#4416](https://github.com/leanprover/lean4/pull/4416) sorts the output of `#print axioms` for determinism.
  * [#4528](https://github.com/leanprover/lean4/pull/4528) fixes error message range for the cdot focusing tactic.

### Language server, widgets, and IDE extensions

* [#4443](https://github.com/leanprover/lean4/pull/4443) makes the watchdog be more resilient against badly behaving clients.

### Pretty printing

* [#4433](https://github.com/leanprover/lean4/pull/4433) restores fallback pretty printers when context is not available, and documents `addMessageContext`.
* [#4556](https://github.com/leanprover/lean4/pull/4556) introduces `pp.maxSteps` option and sets the default value of `pp.deepTerms` to `false`. Together, these keep excessively large or deep terms from overwhelming the Infoview.

### Library
* [#4560](https://github.com/leanprover/lean4/pull/4560) splits `GetElem` class into `GetElem` and `GetElem?`.
  This enables removing `Decidable` instance arguments from `GetElem.getElem?` and `GetElem.getElem!`, improving their rewritability.
  See the docstrings for these classes for more information.
* `Array`
  * [#4389](https://github.com/leanprover/lean4/pull/4389) makes `Array.toArrayAux_eq` be a `simp` lemma.
  * [#4399](https://github.com/leanprover/lean4/pull/4399) improves robustness of the proof for `Array.reverse_data`.
* `List`
  * [#4469](https://github.com/leanprover/lean4/pull/4469) and [#4475](https://github.com/leanprover/lean4/pull/4475) improve the organization of the `List` API.
  * [#4470](https://github.com/leanprover/lean4/pull/4470) improves the `List.set` and `List.concat` API.
  * [#4472](https://github.com/leanprover/lean4/pull/4472) upstreams lemmas about `List.filter` from Batteries.
  * [#4473](https://github.com/leanprover/lean4/pull/4473) adjusts `@[simp]` attributes.
  * [#4488](https://github.com/leanprover/lean4/pull/4488) makes `List.getElem?_eq_getElem` be a simp lemma.
  * [#4487](https://github.com/leanprover/lean4/pull/4487) adds missing `List.replicate` API.
  * [#4521](https://github.com/leanprover/lean4/pull/4521) adds lemmas about `List.map`.
  * [#4500](https://github.com/leanprover/lean4/pull/4500) changes `List.length_cons` to use `as.length + 1` instead of `as.length.succ`.
  * [#4524](https://github.com/leanprover/lean4/pull/4524) fixes the statement of `List.filter_congr`.
  * [#4525](https://github.com/leanprover/lean4/pull/4525) changes binder explicitness in `List.bind_map`.
  * [#4550](https://github.com/leanprover/lean4/pull/4550) adds `maximum?_eq_some_iff'` and `minimum?_eq_some_iff?`.
* [#4400](https://github.com/leanprover/lean4/pull/4400) switches the normal forms for indexing `List` and `Array` to `xs[n]` and `xs[n]?`.
* `HashMap`
  * [#4372](https://github.com/leanprover/lean4/pull/4372) fixes linearity in `HashMap.insert` and `HashMap.erase`, leading to a 40% speedup in a replace-heavy workload.
* `Option`
  * [#4403](https://github.com/leanprover/lean4/pull/4403) generalizes type of `Option.forM` from `Unit` to `PUnit`.
  * [#4504](https://github.com/leanprover/lean4/pull/4504) remove simp attribute from `Option.elim` and instead adds it to individual reduction lemmas, making unfolding less aggressive.
* `Nat`
  * [#4242](https://github.com/leanprover/lean4/pull/4242) adds missing theorems for `n + 1` and `n - 1` normal forms.
  * [#4486](https://github.com/leanprover/lean4/pull/4486) makes `Nat.min_assoc` be a simp lemma.
  * [#4522](https://github.com/leanprover/lean4/pull/4522) moves `@[simp]` from `Nat.pred_le` to `Nat.sub_one_le`.
  * [#4532](https://github.com/leanprover/lean4/pull/4532) changes various `Nat.succ n` to `n + 1`.
* `Int`
  * [#3850](https://github.com/leanprover/lean4/pull/3850) adds complete div/mod simprocs for `Int`.
* `String`/`Char`
  * [#4357](https://github.com/leanprover/lean4/pull/4357) make the byte size interface be `Nat`-valued with functions `Char.utf8Size` and `String.utf8ByteSize`.
  * [#4438](https://github.com/leanprover/lean4/pull/4438) upstreams `Char.ext` from Batteries and adds some `Char` documentation to the manual.
* `Fin`
  * [#4421](https://github.com/leanprover/lean4/pull/4421) adjusts `Fin.sub` to be more performant in definitional equality checks.
* `Prod`
  * [#4526](https://github.com/leanprover/lean4/pull/4526) adds missing `Prod.map` lemmas.
  * [#4533](https://github.com/leanprover/lean4/pull/4533) fixes binder explicitness in lemmas.
* `BitVec`
  * [#4428](https://github.com/leanprover/lean4/pull/4428) adds missing `simproc` for `BitVec` equality.
  * [#4417](https://github.com/leanprover/lean4/pull/4417) adds `BitVec.twoPow` and lemmas, toward bitblasting multiplication for LeanSAT.
* `Std` library
  * [#4499](https://github.com/leanprover/lean4/pull/4499) introduces `Std`, a library situated between `Init` and `Lean`, providing functionality not in the prelude both to Lean's implementation and to external users.
* **Other fixes or improvements**
  * [#3056](https://github.com/leanprover/lean4/pull/3056) standardizes on using `(· == a)` over `(a == ·)`.
  * [#4502](https://github.com/leanprover/lean4/pull/4502) fixes errors reported by running the library through the the Batteries linters.

### Lean internals

* [#4391](https://github.com/leanprover/lean4/pull/4391) makes `getBitVecValue?` recognize `BitVec.ofNatLt`.
* [#4410](https://github.com/leanprover/lean4/pull/4410) adjusts `instantiateMVars` algorithm to zeta reduce `let` expressions while beta reducing instantiated metavariables.
* [#4420](https://github.com/leanprover/lean4/pull/4420) fixes occurs check for metavariable assignments to also take metavariable types into account.
* [#4425](https://github.com/leanprover/lean4/pull/4425) fixes `forEachModuleInDir` to iterate over each Lean file exactly once.
* [#3886](https://github.com/leanprover/lean4/pull/3886) adds support to build Lean core oleans using Lake.
* **Defeq and WHNF algorithms**
  * [#4387](https://github.com/leanprover/lean4/pull/4387) improves performance of `isDefEq` by eta reducing lambda-abstracted terms during metavariable assignments, since these are beta reduced during metavariable instantiation anyway.
  * [#4388](https://github.com/leanprover/lean4/pull/4388) removes redundant code in `isDefEqQuickOther`.
* **Typeclass inference**
  * [#4530](https://github.com/leanprover/lean4/pull/4530) fixes handling of metavariables when caching results at `synthInstance?`.
* **Elaboration**
  * [#4426](https://github.com/leanprover/lean4/pull/4426) makes feature where the "don't know how to synthesize implicit argument" error reports the name of the argument more reliable.
  * [#4497](https://github.com/leanprover/lean4/pull/4497) fixes a name resolution bug for generalized field notation (dot notation).
  * [#4536](https://github.com/leanprover/lean4/pull/4536) blocks the implicit lambda feature for `(e :)` notation.
  * [#4562](https://github.com/leanprover/lean4/pull/4562) makes it be an error for there to be two functions with the same name in a `where`/`let rec` block.
* Recursion principles
  * [#4549](https://github.com/leanprover/lean4/pull/4549) refactors `findRecArg`, extracting `withRecArgInfo`.
    Errors are now reported in parameter order rather than the order they are tried (non-indices are tried first).
    For every argument, it will say why it wasn't tried, even if the reason is obvious (e.g. a fixed prefix or is `Prop`-typed, etc.).
* Porting core C++ to Lean
  * [#4474](https://github.com/leanprover/lean4/pull/4474) takes a step to refactor `constructions` toward a future port to Lean.
  * [#4498](https://github.com/leanprover/lean4/pull/4498) ports `mk_definition_inferring_unsafe` to Lean.
  * [#4516](https://github.com/leanprover/lean4/pull/4516) ports `recOn` construction to Lean.
  * [#4517](https://github.com/leanprover/lean4/pull/4517), [#4653](https://github.com/leanprover/lean4/pull/4653), and [#4651](https://github.com/leanprover/lean4/pull/4651) port `below` and `brecOn` construction to Lean.
* Documentation
  * [#4501](https://github.com/leanprover/lean4/pull/4501) adds a more-detailed docstring for `PersistentEnvExtension`.
* **Other fixes or improvements**
  * [#4382](https://github.com/leanprover/lean4/pull/4382) removes `@[inline]` attribute from `NameMap.find?`, which caused respecialization at each call site.
  * [5f9ded](https://github.com/leanprover/lean4/commit/5f9dedfe5ee9972acdebd669f228f487844a6156) improves output of `trace.Elab.snapshotTree`.
  * [#4424](https://github.com/leanprover/lean4/pull/4424) removes "you might need to open '{dir}' in your editor" message that is now handled by Lake and the VS Code extension.
  * [#4451](https://github.com/leanprover/lean4/pull/4451) improves the performance of `CollectMVars` and `FindMVar`.
  * [#4479](https://github.com/leanprover/lean4/pull/4479) adds missing `DecidableEq` and `Repr` instances for intermediate structures used by the `BitVec` and `Fin` simprocs.
  * [#4492](https://github.com/leanprover/lean4/pull/4492) adds tests for a previous `isDefEq` issue.
  * [9096d6](https://github.com/leanprover/lean4/commit/9096d6fc7180fe533c504f662bcb61550e4a2492) removes `PersistentHashMap.size`.
  * [#4508](https://github.com/leanprover/lean4/pull/4508) fixes `@[implemented_by]` for functions defined by well-founded recursion.
  * [#4509](https://github.com/leanprover/lean4/pull/4509) adds additional tests for `apply?` tactic.
  * [d6eab3](https://github.com/leanprover/lean4/commit/d6eab393f4df9d473b5736d636b178eb26d197e6) fixes a benchmark.
  * [#4563](https://github.com/leanprover/lean4/pull/4563) adds a workaround for a bug in `IndPredBelow.mkBelowMatcher`.
* **Cleanup:** [#4380](https://github.com/leanprover/lean4/pull/4380), [#4431](https://github.com/leanprover/lean4/pull/4431), [#4494](https://github.com/leanprover/lean4/pull/4494), [e8f768](https://github.com/leanprover/lean4/commit/e8f768f9fd8cefc758533bc76e3a12b398ed4a39), [de2690](https://github.com/leanprover/lean4/commit/de269060d17a581ed87f40378dbec74032633b27), [d3a756](https://github.com/leanprover/lean4/commit/d3a7569c97123d022828106468d54e9224ed8207), [#4404](https://github.com/leanprover/lean4/pull/4404), [#4537](https://github.com/leanprover/lean4/pull/4537).

### Compiler, runtime, and FFI

* [d85d3d](https://github.com/leanprover/lean4/commit/d85d3d5f3a09ff95b2ee47c6f89ef50b7e339126) fixes criterion for tail-calls in ownership calculation.
* [#3963](https://github.com/leanprover/lean4/pull/3963) adds validation of UTF-8 at the C++-to-Lean boundary in the runtime.
* [#4512](https://github.com/leanprover/lean4/pull/4512) fixes missing unboxing in interpreter when loading initialized value.
* [#4477](https://github.com/leanprover/lean4/pull/4477) exposes the compiler flags for the bundled C compiler (clang).

### Lake

* [#4384](https://github.com/leanprover/lean4/pull/4384) deprecates `inputFile` and replaces it with `inputBinFile` and `inputTextFile`. Unlike `inputBinFile` (and `inputFile`), `inputTextFile` normalizes line endings, which helps ensure text file traces are platform-independent.
* [#4371](https://github.com/leanprover/lean4/pull/4371) simplifies dependency resolution code.
* [#4439](https://github.com/leanprover/lean4/pull/4439) touches up the Lake configuration DSL and makes other improvements:
  string literals can now be used instead of identifiers for names,
  avoids using French quotes in `lake new` and `lake init` templates,
  changes the `exe` template to use `Main` for the main module,
  improves the `math` template error if `lean-toolchain` fails to download,
  and downgrades unknown configuration fields from an error to a warning to improve cross-version compatibility.
* [#4496](https://github.com/leanprover/lean4/pull/4496) tweaks `require` syntax and updates docs. Now `require` in TOML for a package name such as `doc-gen4` does not need French quotes.
* [#4485](https://github.com/leanprover/lean4/pull/4485) fixes a bug where package versions in indirect dependencies would take precedence over direct dependencies.
* [#4478](https://github.com/leanprover/lean4/pull/4478) fixes a bug where Lake incorrectly included the module dynamic library in a platform-independent trace.
* [#4529](https://github.com/leanprover/lean4/pull/4529) fixes some issues with bad import errors.
  A bad import in an executable no longer prevents the executable's root
  module from being built. This also fixes a problem where the location
  of a transitive bad import would not been shown.
  The root module of the executable now respects `nativeFacets`.
* [#4564](https://github.com/leanprover/lean4/pull/4564) fixes a bug where non-identifier script names could not be entered on the CLI without French quotes.
* [#4566](https://github.com/leanprover/lean4/pull/4566) addresses a few issues with precompiled libraries.
  * Fixes a bug where Lake would always precompile the package of a module.
  * If a module is precompiled, it now precompiles its imports. Previously, it would only do this if imported.
* [#4495](https://github.com/leanprover/lean4/pull/4495), [#4692](https://github.com/leanprover/lean4/pull/4692), [#4849](https://github.com/leanprover/lean4/pull/4849)
  add a new type of `require` that fetches package metadata from a
  registry API endpoint (e.g. Reservoir) and then clones a Git package
  using the information provided. To require such a dependency, the new
  syntax is:

  ```lean
  require <scope> / <pkg-name> [@ git <rev>]
  -- Examples:
  require "leanprover" / "doc-gen4"
  require "leanprover-community" / "proofwidgets" @ git "v0.0.39"
  ```

  Or in TOML:
  ```toml
  [[require]]
  name = "<pkg-name>"
  scope = "<scope>"
  rev = "<rev>"
  ```

  Unlike with Git dependencies, Lake can make use of the richer
  information provided by the registry to determine the default branch of
  the package. This means for repositories of packages like `doc-gen4`
  which have a default branch that is not `master`, Lake will now use said
  default branch (e.g., in `doc-gen4`'s case, `main`).

  Lake also supports configuring the registry endpoint via an environment
  variable: `RESERVIOR_API_URL`. Thus, any server providing a similar
  interface to Reservoir can be used as the registry. Further
  configuration options paralleling those of Cargo's [Alternative Registries](https://doc.rust-lang.org/cargo/reference/registries.html)
  and [Source Replacement](https://doc.rust-lang.org/cargo/reference/source-replacement.html)
  will come in the future.

### DevOps/CI
* [#4427](https://github.com/leanprover/lean4/pull/4427) uses Namespace runners for CI for `leanprover/lean4`.
* [#4440](https://github.com/leanprover/lean4/pull/4440) fixes speedcenter tests in CI.
* [#4441](https://github.com/leanprover/lean4/pull/4441) fixes that workflow change would break CI for unrebased PRs.
* [#4442](https://github.com/leanprover/lean4/pull/4442) fixes Wasm release-ci.
* [6d265b](https://github.com/leanprover/lean4/commit/6d265b42b117eef78089f479790587a399da7690) fixes for `github.event.pull_request.merge_commit_sha` sometimes not being available.
* [16cad2](https://github.com/leanprover/lean4/commit/16cad2b45c6a77efe4dce850dcdbaafaa7c91fc3) adds optimization for CI to not fetch complete history.
* [#4544](https://github.com/leanprover/lean4/pull/4544) causes releases to be marked as prerelease on GitHub.
* [#4446](https://github.com/leanprover/lean4/pull/4446) switches Lake to using `src/lake/lakefile.toml` to avoid needing to load a version of Lake to build Lake.
* Nix
  * [5eb5fa](https://github.com/leanprover/lean4/commit/5eb5fa49cf9862e99a5bccff8d4ca1a062f81900) fixes `update-stage0-commit` for Nix.
  * [#4476](https://github.com/leanprover/lean4/pull/4476) adds gdb to Nix shell.
  * [e665a0](https://github.com/leanprover/lean4/commit/e665a0d716dc42ba79b339b95e01eb99fe932cb3) fixes `update-stage0` for Nix.
  * [4808eb](https://github.com/leanprover/lean4/commit/4808eb7c4bfb98f212b865f06a97d46c44978a61) fixes `cacheRoots` for Nix.
  * [#3811](https://github.com/leanprover/lean4/pull/3811) adds platform-dependent flag to lib target.
  * [#4587](https://github.com/leanprover/lean4/pull/4587) adds linking of `-lStd` back into nix build flags on darwin.

### Breaking changes

* `Char.csize` is replaced by `Char.utf8Size` ([#4357](https://github.com/leanprover/lean4/pull/4357)).
* Library lemmas now are in terms of `(· == a)` over `(a == ·)` ([#3056](https://github.com/leanprover/lean4/pull/3056)).
* Now the normal forms for indexing into `List` and `Array` is `xs[n]` and `xs[n]?` rather than using functions like `List.get` ([#4400](https://github.com/leanprover/lean4/pull/4400)).
* Sometimes terms created via a sequence of unifications will be more eta reduced than before and proofs will require adaptation ([#4387](https://github.com/leanprover/lean4/pull/4387)).
* The `GetElem` class has been split into two; see the docstrings for `GetElem` and `GetElem?` for more information ([#4560](https://github.com/leanprover/lean4/pull/4560)).


v4.9.0
----------

### Language features, tactics, and metaprograms

* **Definition transparency**
  * [#4053](https://github.com/leanprover/lean4/pull/4053) adds the `seal` and `unseal` commands, which make definitions locally be irreducible or semireducible.
  * [#4061](https://github.com/leanprover/lean4/pull/4061) marks functions defined by well-founded recursion with `@[irreducible]` by default,
    which should prevent the expensive and often unfruitful unfolding of such definitions (see breaking changes below).
* **Incrementality**
  * [#3940](https://github.com/leanprover/lean4/pull/3940) extends incremental elaboration into various steps inside of declarations:
    definition headers, bodies, and tactics.
    ![Recording 2024-05-10](https://github.com/leanprover/lean4/assets/109126/c9d67b6f-c131-4bc3-a0de-7d63eaf1bfc9).
  * [250994](https://github.com/leanprover/lean4/commit/250994166ce036ab8644e459129f51ea79c1c2d2)
    and [67338b](https://github.com/leanprover/lean4/commit/67338bac2333fa39a8656e8f90574784e4c23d3d)
    add `@[incremental]` attribute to mark an elaborator as supporting incremental elaboration.
  * [#4259](https://github.com/leanprover/lean4/pull/4259) improves resilience by ensuring incremental commands and tactics are reached only in supported ways.
  * [#4268](https://github.com/leanprover/lean4/pull/4268) adds special handling for `:= by` so that stray tokens in tactic blocks do not inhibit incrementality.
  * [#4308](https://github.com/leanprover/lean4/pull/4308) adds incremental `have` tactic.
  * [#4340](https://github.com/leanprover/lean4/pull/4340) fixes incorrect info tree reuse.
  * [#4364](https://github.com/leanprover/lean4/pull/4364) adds incrementality for careful command macros such as `set_option in theorem`, `theorem foo.bar`, and `lemma`.
  * [#4395](https://github.com/leanprover/lean4/pull/4395) adds conservative fix for whitespace handling to avoid incremental reuse leading to goals in front of the text cursor being shown.
  * [#4407](https://github.com/leanprover/lean4/pull/4407) fixes non-incremental commands in macros blocking further incremental reporting.
  * [#4436](https://github.com/leanprover/lean4/pull/4436) fixes incremental reporting when there are nested tactics in terms.
  * [#4459](https://github.com/leanprover/lean4/pull/4459) adds incrementality support for `next` and `if` tactics.
  * [#4554](https://github.com/leanprover/lean4/pull/4554) disables incrementality for tactics in terms in tactics.
* **Functional induction**
  * [#4135](https://github.com/leanprover/lean4/pull/4135) ensures that the names used for functional induction are reserved.
  * [#4327](https://github.com/leanprover/lean4/pull/4327) adds support for structural recursion on reflexive types.
    For example,
    ```lean4
    inductive Many (α : Type u) where
      | none : Many α
      | more : α → (Unit → Many α) → Many α

    def Many.map {α β : Type u} (f : α → β) : Many α → Many β
      | .none => .none
      | .more x xs => .more (f x) (fun _ => (xs ()).map f)

    #check Many.map.induct
    /-
    Many.map.induct {α β : Type u} (f : α → β) (motive : Many α → Prop)
      (case1 : motive Many.none)
      (case2 : ∀ (x : α) (xs : Unit → Many α), motive (xs ()) → motive (Many.more x xs)) :
      ∀ (a : Many α), motive a
    -/
    ```
* [#3903](https://github.com/leanprover/lean4/pull/3903) makes the Lean frontend normalize all line endings to LF before processing.
  This lets Lean be insensitive to CRLF vs LF line endings, improving the cross-platform experience and making Lake hashes be faithful to what Lean processes.
* [#4130](https://github.com/leanprover/lean4/pull/4130) makes the tactic framework be able to recover from runtime errors (for example, deterministic timeouts or maximum recursion depth errors).
* `split` tactic
  * [#4211](https://github.com/leanprover/lean4/pull/4211) fixes `split at h` when `h` has forward dependencies.
  * [#4349](https://github.com/leanprover/lean4/pull/4349) allows `split` for `if`-expressions to work on non-propositional goals.
* `apply` tactic
  * [#3929](https://github.com/leanprover/lean4/pull/3929) makes error message for `apply` show implicit arguments in unification errors as needed.
    Modifies `MessageData` type (see breaking changes below).
* `cases` tactic
  * [#4224](https://github.com/leanprover/lean4/pull/4224) adds support for unification of offsets such as `x + 20000 = 20001` in `cases` tactic.
* `omega` tactic
  * [#4073](https://github.com/leanprover/lean4/pull/4073) lets `omega` fall back to using classical `Decidable` instances when setting up contradiction proofs.
  * [#4141](https://github.com/leanprover/lean4/pull/4141) and [#4184](https://github.com/leanprover/lean4/pull/4184) fix bugs.
  * [#4264](https://github.com/leanprover/lean4/pull/4264) improves `omega` error message if no facts found in local context.
  * [#4358](https://github.com/leanprover/lean4/pull/4358) improves expression matching in `omega` by using `match_expr`.
* `simp` tactic
  * [#4176](https://github.com/leanprover/lean4/pull/4176) makes names of erased lemmas clickable.
  * [#4208](https://github.com/leanprover/lean4/pull/4208) adds a pretty printer for discrimination tree keys.
  * [#4202](https://github.com/leanprover/lean4/pull/4202) adds `Simp.Config.index` configuration option,
    which controls whether to use the full discrimination tree when selecting candidate simp lemmas.
    When `index := false`, only the head function is taken into account, like in Lean 3.
    This feature can help users diagnose tricky simp failures or issues in code from libraries
    developed using Lean 3 and then ported to Lean 4.

    In the following example, it will report that `foo` is a problematic theorem.
    ```lean
    opaque f : Nat → Nat → Nat

    @[simp] theorem foo : f x (x, y).2 = y := by sorry

    example : f a b ≤ b := by
      set_option diagnostics true in
      simp (config := { index := false })
    /-
    [simp] theorems with bad keys
      foo, key: f _ (@Prod.mk ℕ ℕ _ _).2
    -/
    ```
    With the information above, users can annotate theorems such as `foo` using `no_index` for problematic subterms. Example:
    ```lean
    opaque f : Nat → Nat → Nat

    @[simp] theorem foo : f x (no_index (x, y).2) = y := by sorry

    example : f a b ≤ b := by
      simp -- `foo` is still applied with `index := true`
    ```
  * [#4274](https://github.com/leanprover/lean4/pull/4274) prevents internal `match` equational theorems from appearing in simp trace.
  * [#4177](https://github.com/leanprover/lean4/pull/4177) and [#4359](https://github.com/leanprover/lean4/pull/4359) make `simp` continue even if a simp lemma does not elaborate, if the tactic state is in recovery mode.
  * [#4341](https://github.com/leanprover/lean4/pull/4341) fixes panic when applying `@[simp]` to malformed theorem syntax.
  * [#4345](https://github.com/leanprover/lean4/pull/4345) fixes `simp` so that it does not use the forward version of a user-specified backward theorem.
  * [#4352](https://github.com/leanprover/lean4/pull/4352) adds missing `dsimp` simplifications for fixed parameters of generated congruence theorems.
  * [#4362](https://github.com/leanprover/lean4/pull/4362) improves trace messages for `simp` so that constants are hoverable.
* **Elaboration**
  * [#4046](https://github.com/leanprover/lean4/pull/4046) makes subst notation (`he ▸ h`) try rewriting in both directions even when there is no expected type available.
  * [#3328](https://github.com/leanprover/lean4/pull/3328) adds support for identifiers in autoparams (for example, `rfl` in `(h : x = y := by exact rfl)`).
  * [#4096](https://github.com/leanprover/lean4/pull/4096) changes how the type in `let` and `have` is elaborated, requiring that any tactics in the type be evaluated before proceeding, improving performance.
  * [#4215](https://github.com/leanprover/lean4/pull/4215) ensures the expression tree elaborator commits to the computed "max type" for the entire arithmetic expression.
  * [#4267](https://github.com/leanprover/lean4/pull/4267) cases signature elaboration errors to show even if there are parse errors in the body.
  * [#4368](https://github.com/leanprover/lean4/pull/4368) improves error messages when numeric literals fail to synthesize an `OfNat` instance,
    including special messages warning when the expected type of the numeral can be a proposition.
  * [#4643](https://github.com/leanprover/lean4/pull/4643) fixes issue leading to nested error messages and info trees vanishing, where snapshot subtrees were not restored on reuse.
  * [#4657](https://github.com/leanprover/lean4/pull/4657) calculates error suppression per snapshot, letting elaboration errors appear even when there are later parse errors ([RFC #3556](https://github.com/leanprover/lean4/issues/3556)).
* **Metaprogramming**
  * [#4167](https://github.com/leanprover/lean4/pull/4167) adds `Lean.MVarId.revertAll` to revert all free variables.
  * [#4169](https://github.com/leanprover/lean4/pull/4169) adds `Lean.MVarId.ensureNoMVar` to ensure the goal's target contains no expression metavariables.
  * [#4180](https://github.com/leanprover/lean4/pull/4180) adds `cleanupAnnotations` parameter to `forallTelescope` methods.
  * [#4307](https://github.com/leanprover/lean4/pull/4307) adds support for parser aliases in syntax quotations.
* Work toward implementing `grind` tactic
  * [0a515e](https://github.com/leanprover/lean4/commit/0a515e2ec939519dafb4b99daa81d6bf3c411404)
    and [#4164](https://github.com/leanprover/lean4/pull/4164)
    add `grind_norm` and `grind_norm_proc` attributes and `@[grind_norm]` theorems.
  * [#4170](https://github.com/leanprover/lean4/pull/4170), [#4221](https://github.com/leanprover/lean4/pull/4221),
    and [#4249](https://github.com/leanprover/lean4/pull/4249) create `grind` preprocessor and core module.
  * [#4235](https://github.com/leanprover/lean4/pull/4235) and [d6709e](https://github.com/leanprover/lean4/commit/d6709eb1576c5d40fc80462637dc041f970e4d9f)
    add special `cases` tactic to `grind` along with `@[grind_cases]` attribute to mark types that this `cases` tactic should automatically apply to.
  * [#4243](https://github.com/leanprover/lean4/pull/4243) adds special `injection?` tactic to `grind`.
* **Other fixes or improvements**
  * [#4065](https://github.com/leanprover/lean4/pull/4065) fixes a bug in the `Nat.reduceLeDiff` simproc.
  * [#3969](https://github.com/leanprover/lean4/pull/3969) makes deprecation warnings activate even for generalized field notation ("dot notation").
  * [#4132](https://github.com/leanprover/lean4/pull/4132) fixes the `sorry` term so that it does not activate the implicit lambda feature
  * [9803c5](https://github.com/leanprover/lean4/commit/9803c5dd63dc993628287d5f998525e74af03839)
    and [47c8e3](https://github.com/leanprover/lean4/commit/47c8e340d65b01f4d9f011686e3dda0d4bb30a20)
    move `cdot` and `calc` parsers to `Lean` namespace.
  * [#4252](https://github.com/leanprover/lean4/pull/4252) fixes the `case` tactic so that it is usable in macros by having it erase macro scopes from the tag.
  * [26b671](https://github.com/leanprover/lean4/commit/26b67184222e75529e1b166db050aaebee323d2d)
    and [cc33c3](https://github.com/leanprover/lean4/commit/cc33c39cb022d8a3166b1e89677c78835ead1fc7)
    extract `haveId` syntax.
  * [#4335](https://github.com/leanprover/lean4/pull/4335) fixes bugs in partial `calc` tactic when there is mdata or metavariables.
  * [#4329](https://github.com/leanprover/lean4/pull/4329) makes `termination_by?` report unused each unused parameter as `_`.
* **Docs:** [#4238](https://github.com/leanprover/lean4/pull/4238), [#4294](https://github.com/leanprover/lean4/pull/4294),
  [#4338](https://github.com/leanprover/lean4/pull/4338).

### Language server, widgets, and IDE extensions
* [#4066](https://github.com/leanprover/lean4/pull/4066) fixes features like "Find References" when browsing core Lean sources.
* [#4254](https://github.com/leanprover/lean4/pull/4254) allows embedding user widgets in structured messages.
  Companion PR is [vscode-lean4#449](https://github.com/leanprover/vscode-lean4/pull/449).
* [#4445](https://github.com/leanprover/lean4/pull/4445) makes watchdog more resilient against badly behaving clients.

### Library
* [#4059](https://github.com/leanprover/lean4/pull/4059) upstreams many `List` and `Array` operations and theorems from Batteries.
* [#4055](https://github.com/leanprover/lean4/pull/4055) removes the unused `Inhabited` instance for `Subtype`.
* [#3967](https://github.com/leanprover/lean4/pull/3967) adds dates in existing `@[deprecated]` attributes.
* [#4231](https://github.com/leanprover/lean4/pull/4231) adds boilerplate `Char`, `UInt`, and `Fin` theorems.
* [#4205](https://github.com/leanprover/lean4/pull/4205) fixes the `MonadStore` type classes to use `semiOutParam`.
* [#4350](https://github.com/leanprover/lean4/pull/4350) renames `IsLawfulSingleton` to `LawfulSingleton`.
* `Nat`
  * [#4094](https://github.com/leanprover/lean4/pull/4094) swaps `Nat.zero_or` and `Nat.or_zero`.
  * [#4098](https://github.com/leanprover/lean4/pull/4098) and [#4145](https://github.com/leanprover/lean4/pull/4145)
    change the definition of `Nat.mod` so that `n % (m + n)` reduces when `n` is literal without relying on well-founded recursion,
    which becomes irreducible by default in [#4061](https://github.com/leanprover/lean4/pull/4061).
  * [#4188](https://github.com/leanprover/lean4/pull/4188) redefines `Nat.testBit` to be more performant.
  * Theorems: [#4199](https://github.com/leanprover/lean4/pull/4199).
* `Array`
  * [#4074](https://github.com/leanprover/lean4/pull/4074) improves the functional induction principle `Array.feraseIdx.induct`.
* `List`
  * [#4172](https://github.com/leanprover/lean4/pull/4172) removes `@[simp]` from `List.length_pos`.
* `Option`
  * [#4037](https://github.com/leanprover/lean4/pull/4037) adds theorems to simplify `Option`-valued dependent if-then-else.
  * [#4314](https://github.com/leanprover/lean4/pull/4314) removes `@[simp]` from `Option.bind_eq_some`.
* `BitVec`
  * Theorems: [#3920](https://github.com/leanprover/lean4/pull/3920), [#4095](https://github.com/leanprover/lean4/pull/4095),
    [#4075](https://github.com/leanprover/lean4/pull/4075), [#4148](https://github.com/leanprover/lean4/pull/4148),
    [#4165](https://github.com/leanprover/lean4/pull/4165), [#4178](https://github.com/leanprover/lean4/pull/4178),
    [#4200](https://github.com/leanprover/lean4/pull/4200), [#4201](https://github.com/leanprover/lean4/pull/4201),
    [#4298](https://github.com/leanprover/lean4/pull/4298), [#4299](https://github.com/leanprover/lean4/pull/4299),
    [#4257](https://github.com/leanprover/lean4/pull/4257), [#4179](https://github.com/leanprover/lean4/pull/4179),
    [#4321](https://github.com/leanprover/lean4/pull/4321), [#4187](https://github.com/leanprover/lean4/pull/4187).
  * [#4193](https://github.com/leanprover/lean4/pull/4193) adds simprocs for reducing `x >>> i` and `x <<< i` where `i` is a bitvector literal.
  * [#4194](https://github.com/leanprover/lean4/pull/4194) adds simprocs for reducing `(x <<< i) <<< j` and `(x >>> i) >>> j` where `i` and `j` are natural number literals.
  * [#4229](https://github.com/leanprover/lean4/pull/4229) redefines `rotateLeft`/`rotateRight` to use modulo reduction of shift offset.
  * [0d3051](https://github.com/leanprover/lean4/commit/0d30517dca094a07bcb462252f718e713b93ffba) makes `<num>#<term>` bitvector literal notation global.
* `Char`/`String`
  * [#4143](https://github.com/leanprover/lean4/pull/4143) modifies `String.substrEq` to avoid linter warnings in downstream code.
  * [#4233](https://github.com/leanprover/lean4/pull/4233) adds simprocs for `Char` and `String` inequalities.
  * [#4348](https://github.com/leanprover/lean4/pull/4348) upstreams Mathlib lemmas.
  * [#4354](https://github.com/leanprover/lean4/pull/4354) upstreams basic `String` lemmas.
* `HashMap`
  * [#4248](https://github.com/leanprover/lean4/pull/4248) fixes implicitness of typeclass arguments in `HashMap.ofList`.
* `IO`
  * [#4036](https://github.com/leanprover/lean4/pull/4036) adds `IO.Process.getCurrentDir` and `IO.Process.setCurrentDir` for adjusting the current process's working directory.
* **Cleanup:** [#4077](https://github.com/leanprover/lean4/pull/4077), [#4189](https://github.com/leanprover/lean4/pull/4189),
  [#4304](https://github.com/leanprover/lean4/pull/4304).
* **Docs:** [#4001](https://github.com/leanprover/lean4/pull/4001), [#4166](https://github.com/leanprover/lean4/pull/4166),
  [#4332](https://github.com/leanprover/lean4/pull/4332).

### Lean internals
* **Defeq and WHNF algorithms**
  * [#4029](https://github.com/leanprover/lean4/pull/4029) remove unnecessary `checkpointDefEq`
  * [#4206](https://github.com/leanprover/lean4/pull/4206) fixes `isReadOnlyOrSyntheticOpaque` to respect metavariable depth.
  * [#4217](https://github.com/leanprover/lean4/pull/4217) fixes missing occurs check for delayed assignments.
* **Definition transparency**
  * [#4052](https://github.com/leanprover/lean4/pull/4052) adds validation to application of `@[reducible]`/`@[semireducible]`/`@[irreducible]` attributes (with `local`/`scoped` modifiers as well).
    Setting `set_option allowUnsafeReductibility true` turns this validation off.
* **Inductive types**
  * [#3591](https://github.com/leanprover/lean4/pull/3591) fixes a bug where indices could be incorrectly promoted to parameters.
  * [#3398](https://github.com/leanprover/lean4/pull/3398) fixes a bug in the injectivity theorem generator.
  * [#4342](https://github.com/leanprover/lean4/pull/4342) fixes elaboration of mutual inductives with instance parameters.
* **Diagnostics and profiling**
  * [#3986](https://github.com/leanprover/lean4/pull/3986) adds option `trace.profiler.useHeartbeats` to switch `trace.profiler.threshold` to being in terms of heartbeats instead of milliseconds.
  * [#4082](https://github.com/leanprover/lean4/pull/4082) makes `set_option diagnostics true` report kernel diagnostic information.
* **Typeclass resolution**
  * [#4119](https://github.com/leanprover/lean4/pull/4119) fixes multiple issues with TC caching interacting with `synthPendingDepth`, adds `maxSynthPendingDepth` option with default value `1`.
  * [#4210](https://github.com/leanprover/lean4/pull/4210) ensures local instance cache does not contain multiple copies of the same instance.
  * [#4216](https://github.com/leanprover/lean4/pull/4216) fix handling of metavariables, to avoid needing to set the option `backward.synthInstance.canonInstances` to `false`.
* **Other fixes or improvements**
  * [#4080](https://github.com/leanprover/lean4/pull/4080) fixes propagation of state for `Lean.Elab.Command.liftCoreM` and `Lean.Elab.Command.liftTermElabM`.
  * [#3944](https://github.com/leanprover/lean4/pull/3944) makes the `Repr` deriving handler be consistent between `structure` and `inductive` for how types and proofs are erased.
  * [#4113](https://github.com/leanprover/lean4/pull/4113) propagates `maxHeartbeats` to kernel to control "(kernel) deterministic timeout" error.
  * [#4125](https://github.com/leanprover/lean4/pull/4125) reverts [#3970](https://github.com/leanprover/lean4/pull/3970) (monadic generalization of `FindExpr`).
  * [#4128](https://github.com/leanprover/lean4/pull/4128) catches stack overflow in auto-bound implicits feature.
  * [#4129](https://github.com/leanprover/lean4/pull/4129) adds `tryCatchRuntimeEx` combinator to replace `catchRuntimeEx` reader state.
  * [#4155](https://github.com/leanprover/lean4/pull/4155) simplifies the expression canonicalizer.
  * [#4151](https://github.com/leanprover/lean4/pull/4151) and [#4369](https://github.com/leanprover/lean4/pull/4369)
    add many missing trace classes.
  * [#4185](https://github.com/leanprover/lean4/pull/4185) makes congruence theorem generators clean up type annotations of argument types.
  * [#4192](https://github.com/leanprover/lean4/pull/4192) fixes restoration of infotrees when auto-bound implicit feature is activated,
    fixing a pretty printing error in hovers and strengthening the unused variable linter.
  * [dfb496](https://github.com/leanprover/lean4/commit/dfb496a27123c3864571aec72f6278e2dad1cecf) fixes `declareBuiltin` to allow it to be called multiple times per declaration.
  * [#4569](https://github.com/leanprover/lean4/pull/4569) fixes an issue introduced in a merge conflict, where the interrupt exception was swallowed by some `tryCatchRuntimeEx` uses.
  * [#4584](https://github.com/leanprover/lean4/pull/4584) (backported as [b056a0](https://github.com/leanprover/lean4/commit/b056a0b395bb728512a3f3e83bf9a093059d4301)) adapts kernel interruption to the new cancellation system.
  * Cleanup: [#4112](https://github.com/leanprover/lean4/pull/4112), [#4126](https://github.com/leanprover/lean4/pull/4126), [#4091](https://github.com/leanprover/lean4/pull/4091), [#4139](https://github.com/leanprover/lean4/pull/4139), [#4153](https://github.com/leanprover/lean4/pull/4153).
  * Tests: [030406](https://github.com/leanprover/lean4/commit/03040618b8f9b35b7b757858483e57340900cdc4), [#4133](https://github.com/leanprover/lean4/pull/4133).

### Compiler, runtime, and FFI
* [#4100](https://github.com/leanprover/lean4/pull/4100) improves reset/reuse algorithm; it now runs a second pass relaxing the constraint that reused memory cells must only be for the exact same constructor.
* [#2903](https://github.com/leanprover/lean4/pull/2903) fixes segfault in old compiler from mishandling `noConfusion` applications.
* [#4311](https://github.com/leanprover/lean4/pull/4311) fixes bug in constant folding.
* [#3915](https://github.com/leanprover/lean4/pull/3915) documents the runtime memory layout for inductive types.

### Lake
* [#4518](https://github.com/leanprover/lean4/pull/4518) makes trace reading more robust. Lake now rebuilds if trace files are invalid or unreadable and is backwards compatible with previous pure numeric traces.
* [#4057](https://github.com/leanprover/lean4/pull/4057) adds support for docstrings on `require` commands.
* [#4088](https://github.com/leanprover/lean4/pull/4088) improves hovers for `family_def` and `library_data` commands.
* [#4147](https://github.com/leanprover/lean4/pull/4147) adds default `README.md` to package templates
* [#4261](https://github.com/leanprover/lean4/pull/4261) extends `lake test` help page, adds help page for `lake check-test`,
  adds `lake lint` and tag `@[lint_driver]`, adds support for specifying test and lint drivers from dependencies,
  adds `testDriverArgs` and `lintDriverArgs` options, adds support for library test drivers,
  makes `lake check-test` and `lake check-lint` only load the package without dependencies.
* [#4270](https://github.com/leanprover/lean4/pull/4270) adds `lake pack` and `lake unpack` for packing and unpacking Lake build artifacts from an archive.
* [#4083](https://github.com/leanprover/lean4/pull/4083)
  Switches the manifest format to use `major.minor.patch` semantic
  versions. Major version increments indicate breaking changes (e.g., new
  required fields and semantic changes to existing fields). Minor version
  increments (after `0.x`) indicate backwards-compatible extensions (e.g.,
  adding optional fields, removing fields). This change is backwards
  compatible. Lake will still successfully read old manifests with numeric
  versions. It will treat the numeric version `N` as semantic version
  `0.N.0`. Lake will also accept manifest versions with `-` suffixes
  (e.g., `x.y.z-foo`) and then ignore the suffix.
* [#4273](https://github.com/leanprover/lean4/pull/4273) adds a lift from `JobM` to `FetchM` for backwards compatibility reasons.
* [#4351](https://github.com/leanprover/lean4/pull/4351) fixes `LogIO`-to-`CliM`-lifting performance issues.
* [#4343](https://github.com/leanprover/lean4/pull/4343) make Lake store the dependency trace for a build in
  the cached build long and then verifies that it matches the trace of the current build before replaying the log.
* [#4402](https://github.com/leanprover/lean4/pull/4402) moves the cached log into the trace file (no more `.log.json`).
  This means logs are no longer cached on fatal errors and this ensures that an out-of-date log is not associated with an up-to-date trace.
  Separately, `.hash` file generation was changed to be more reliable as well.
  The `.hash` files are deleted as part of the build and always regenerate with `--rehash`.
* **Other fixes or improvements**
  * [#4056](https://github.com/leanprover/lean4/pull/4056) cleans up tests
  * [#4244](https://github.com/leanprover/lean4/pull/4244) fixes `noRelease` test when Lean repo is tagged
  * [#4346](https://github.com/leanprover/lean4/pull/4346) improves `tests/serve`
  * [#4356](https://github.com/leanprover/lean4/pull/4356) adds build log path to the warning for a missing or invalid build log.

### DevOps
* [#3984](https://github.com/leanprover/lean4/pull/3984) adds a script (`script/rebase-stage0.sh`) for `git rebase -i` that automatically updates each stage0.
* [#4108](https://github.com/leanprover/lean4/pull/4108) finishes renamings from transition to Std to Batteries.
* [#4109](https://github.com/leanprover/lean4/pull/4109) adjusts the Github bug template to mention testing using [live.lean-lang.org](https://live.lean-lang.org).
* [#4136](https://github.com/leanprover/lean4/pull/4136) makes CI rerun only when `full-ci` label is added or removed.
* [#4175](https://github.com/leanprover/lean4/pull/4175) and [72b345](https://github.com/leanprover/lean4/commit/72b345c621a9a06d3a5a656da2b793a5eea5f168)
  switch to using `#guard_msgs` to run tests as much as possible.
* [#3125](https://github.com/leanprover/lean4/pull/3125) explains the Lean4 `pygments` lexer.
* [#4247](https://github.com/leanprover/lean4/pull/4247) sets up a procedure for preparing release notes.
* [#4032](https://github.com/leanprover/lean4/pull/4032) modernizes build instructions and workflows.
* [#4255](https://github.com/leanprover/lean4/pull/4255) moves some expensive checks from merge queue to releases.
* [#4265](https://github.com/leanprover/lean4/pull/4265) adds aarch64 macOS as native compilation target for CI.
* [f05a82](https://github.com/leanprover/lean4/commit/f05a82799a01569edeb5e2594cd7d56282320f9e) restores macOS aarch64 install suffix in CI
* [#4317](https://github.com/leanprover/lean4/pull/4317) updates build instructions for macOS.
* [#4333](https://github.com/leanprover/lean4/pull/4333) adjusts workflow to update Batteries in manifest when creating `lean-pr-testing-NNNN` Mathlib branches.
* [#4355](https://github.com/leanprover/lean4/pull/4355) simplifies `lean4checker` step of release checklist.
* [#4361](https://github.com/leanprover/lean4/pull/4361) adds installing elan to `pr-release` CI step.
* [#4628](https://github.com/leanprover/lean4/pull/4628) fixes the Windows build, which was missing an exported symbol.

### Breaking changes
While most changes could be considered to be a breaking change, this section makes special note of API changes.

* `Nat.zero_or` and `Nat.or_zero` have been swapped ([#4094](https://github.com/leanprover/lean4/pull/4094)).
* `IsLawfulSingleton` is now `LawfulSingleton` ([#4350](https://github.com/leanprover/lean4/pull/4350)).
* The `BitVec` literal notation is now `<num>#<term>` rather than `<term>#<term>`, and it is global rather than scoped. Use `BitVec.ofNat w x` rather than `x#w` when `x` is a not a numeric literal ([0d3051](https://github.com/leanprover/lean4/commit/0d30517dca094a07bcb462252f718e713b93ffba)).
* `BitVec.rotateLeft` and `BitVec.rotateRight` now take the shift modulo the bitwidth ([#4229](https://github.com/leanprover/lean4/pull/4229)).
* These are no longer simp lemmas:
  `List.length_pos` ([#4172](https://github.com/leanprover/lean4/pull/4172)),
  `Option.bind_eq_some` ([#4314](https://github.com/leanprover/lean4/pull/4314)).
* Types in `let` and `have` (both the expressions and tactics) may fail to elaborate due to new restrictions on what sorts of elaboration problems may be postponed ([#4096](https://github.com/leanprover/lean4/pull/4096)).
  In particular, tactics embedded in the type will no longer make use of the type of `value` in expressions such as `let x : type := value; body`.
* Now functions defined by well-founded recursion are marked with `@[irreducible]` by default ([#4061](https://github.com/leanprover/lean4/pull/4061)).
  Existing proofs that hold by definitional equality (e.g. `rfl`) can be
  rewritten to explicitly unfold the function definition (using `simp`,
  `unfold`, `rw`), or the recursive function can be temporarily made
  semireducible (using `unseal f in` before the command), or the function
  definition itself can be marked as `@[semireducible]` to get the previous
  behavior.
* Due to [#3929](https://github.com/leanprover/lean4/pull/3929):
  * The `MessageData.ofPPFormat` constructor has been removed.
    Its functionality has been split into two:

    - for lazy structured messages, please use `MessageData.lazy`;
    - for embedding `Format` or `FormatWithInfos`, use `MessageData.ofFormatWithInfos`.

    An example migration can be found in [#3929](https://github.com/leanprover/lean4/pull/3929/files#diff-5910592ab7452a0e1b2616c62d22202d2291a9ebb463145f198685aed6299867L109).

  * The `MessageData.ofFormat` constructor has been turned into a function.
    If you need to inspect `MessageData`, you can pattern-match on `MessageData.ofFormatWithInfos`.

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

* [#3602](https://github.com/leanprover/lean4/pull/3602) enables `import` auto-completions.
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

* Due to the major Lake build refactor, code using the affected parts of the Lake API or relying on the previous output format of Lake builds is likely to have been broken. We have tried to minimize the breakages and, where possible, old definitions have been marked `@[deprecated]` with a reference to the new alternative.

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
     essential datatypes not provided by the core language (e.g. `RBMap`)
     and utilities such as basic IO.
  While we have achieved most of our initial aims in `v4.7.0-rc1`,
  some upstreaming will continue over the coming months.

* The `/` and `%` notations in `Int` now use `Int.ediv` and `Int.emod`
  (i.e. the rounding conventions have changed).
  Previously `Std` overrode these notations, so this is no change for users of `Std`.
  There is now kernel support for these functions.
  [#3376](https://github.com/leanprover/lean4/pull/3376).

* `omega`, our integer linear arithmetic tactic, is now available in the core language.
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
        not need to be simplified further.
      * The constructor `.visit` instructs `simp` to visit the resulting expression.
      * The constructor `.continue` instructs `simp` to try other simplification procedures.

      All three constructors take a `Result`. The `.continue` constructor may also take `none`.
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
  These have the interpretation of an empty string and allow a string to flow across multiple lines without introducing additional whitespace.
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
  you can use `WellFounded.wrap` from the std library to explicitly give one:
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
