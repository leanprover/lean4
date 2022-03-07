v4.0.0-m4 (WIP)
---------

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

* Auto generated congruence lemmas with support for casts on proofs and `Decidable` instances (see [whishlist](https://github.com/leanprover/lean4/issues/988)).

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
Before:
```lean
match x, rfl : (y : Nat) → x = y → Nat with
| 0,   h => ...
| x+1, h => ...
```
Now:
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

* Auto implicit behavior changed for inductive families. An auto implicit argument occurring in inductive family index is also treated as an index. For example
```lean
inductive HasType : Index n → Vector Ty n → Ty → Type where
```
is now interpreted as
```lean
inductive HasType : {n : Nat} → Index n → Vector Ty n → Ty → Type where
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
