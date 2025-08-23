
import Lean

open Lean Doc Elab Term

set_option doc.verso true

attribute [doc_role] Lean.Doc.name
attribute [doc_code_block] Lean.Doc.lean
attribute [doc_command] Lean.Doc.«open»
attribute [doc_role] Lean.Doc.given
attribute [doc_role lean] Lean.Doc.leanTerm
attribute [doc_role] Lean.Doc.manual

@[doc_code_block]
def c (s : StrLit) : DocM (Block ElabInline ElabBlock) := pure (Block.code (s.getString.toList.reverse |> String.mk))

@[doc_directive]
def d (s : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  .concat <$> s.reverse.mapM elabBlock

structure ResolvedName where
  name : Name

instance : Lean.Doc.FromDocArg ResolvedName where
  fromDocArg
    | .ident x => .mk <$> realizeGlobalConstNoOverloadWithInfo x
    | other => throwError "Expected name, got {other}"

/--
x
yz

[W][wikipedia]

[wikipedia]: https://en.wikipedia.org

{name}`Nat`

{given}`n : Nat`

{given}`k`

{lean}`k = n`

{name}`n`

{open Nat}

{name}`succ`

{name}`x`

{name}`y`

# foo

blah

# bar

## baz

:::d

```c
blah
```

:::

```lean
#check x
```
-/
def x (y : Nat) : Nat := y * 5

#eval show TermElabM Unit from do (← findDocString? (← getEnv) ``x).forM (IO.println ·.quote)



/--
Rotates an array {name}`xs` by {name}`n` places.

If {lean}`xs.size ≤ n`, then {lean}`rot n xs = rot (n % xs.size) xs`.

Read more about {manual section "Array"}[arrays] in the Lean language reference.
-/
def rot (n : Nat) (xs : Array α) : Array α :=
  xs[n:] ++ xs[:n]

#eval rot 2 #[1, 2, 3]

#eval rot 5 #[1, 2, 3]


/--
Given {given}`xs : List α`, finds lists {given}`ys` and {given}`zs` such that {lean}`xs = ys ++ zs`
and {lean}`∀x ∈ xs, p x` and {lean}`zs.head?.all (¬p ·)`.
-/
def splitSuchThat (p : α → Prop) [DecidablePred p] : List α → (List α × List α)
  | [] => ([], [])
  | x :: xs =>
    if p x then
      let (pre, post) := splitSuchThat p xs
      (x :: pre, post)
    else
      ([], x :: xs)

/--
An induction principle for {name}`Nat.gcd`'s reference implementation via Euclid's algorithm.

{open Nat}

To prove that a relation {name}`P` holds universally for the natural numbers (that is, for any
{name}`Nat`s {given}`j` and {given}`k`, we have {lean}`P j k`), it suffices to show:

: Base case

  {lean}`P` relates {lean}`0` to all {lean}`Nat`s.

: Inductive step

  {lean}`P` relates non-zero {given}`m` to {given}`n` if it relates {lean}`n % m` to {lean}`m`.

This follows the computational behavior of {name}`gcd`.
-/
@[elab_as_elim] theorem Nat.gcd.induction' {P : Nat → Nat → Prop} (m n : Nat)
    (H0 : ∀n, P 0 n) (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) : P m n :=
  Nat.strongRecOn (motive := fun m => ∀ n, P m n) m
    (fun
    | 0, _ => H0
    | _+1, IH => fun _ => H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _) )
    n

#check Nat.gcd.induction'


/-
TODO test:

* given
* section variables
* Scope rules for all operators
* open command, and open +scoped, and open only
* inherit_doc for verso and non-verso docs


-/
