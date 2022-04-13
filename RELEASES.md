Unreleased
---------

* Remove support for `{}` annotation from inductive datatype contructors. This annotation was barely used, and we can control the binder information for parameter bindings using the new inductive family indices to parameter promotion. Example: the following declaration using `{}`
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
Before:
```lean
#check @Member.head
-- @Member.head : {x : Type u_1} → {a : x} → {as : List x} → Member a (a :: as)
```
Now:
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
If you don't neet to acces `my_ext`, you can also use the macro
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
