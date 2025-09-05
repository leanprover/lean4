
import Lean


open Lean Doc Elab Term

set_option doc.verso true



attribute [doc_role] Lean.Doc.name
attribute [doc_role] Lean.Doc.kw
attribute [doc_role] Lean.Doc.kw?
attribute [doc_role] Lean.Doc.syntaxCat
attribute [doc_role] Lean.Doc.option
attribute [doc_role] Lean.Doc.attr
attribute [doc_role] Lean.Doc.tactic
attribute [doc_role] Lean.Doc.conv
attribute [doc_code_block] Lean.Doc.lean
attribute [doc_code_block] Lean.Doc.output
attribute [doc_command] Lean.Doc.«open»
attribute [doc_command] Lean.Doc.«set_option»
attribute [doc_role] Lean.Doc.given
attribute [doc_role lean] Lean.Doc.leanTerm
attribute [doc_role] Lean.Doc.manual
attribute [doc_role] Lean.Doc.syntax
attribute [doc_code_suggestions] Lean.Doc.suggestName
attribute [doc_code_suggestions] Lean.Doc.suggestLean
attribute [doc_code_suggestions] Lean.Doc.suggestTactic
attribute [doc_code_suggestions] Lean.Doc.suggestAttr
attribute [doc_code_suggestions] Lean.Doc.suggestOption
attribute [doc_code_suggestions] Lean.Doc.suggestKw
attribute [doc_code_suggestions] Lean.Doc.suggestCat
attribute [doc_code_suggestions] Lean.Doc.suggestSyntax



@[doc_code_block]
def c (s : StrLit) : DocM (Block ElabInline ElabBlock) := pure (Block.code (s.getString.toList.reverse |> String.mk))

@[doc_directive]
def d (s : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  .concat <$> s.reverse.mapM elabBlock


/--
A resolved name. The internal thing is a {name}`Name`.

Functions are `induction`
-/
declare_syntax_cat foo

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
{name}`inst`
-/
def blah [inst : ToString α] (x : α) : String := inst.toString x

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

open MessageSeverity in
/--
Prints {name}`s` twice.

```lean +error (name := twice)
#eval printTwice A
```
```output twice (severity := error)
Unknown identifier `A`
```

```lean +error (name := blah)
def blah2 : Nat := "glah"
```
```output blah
Type mismatch
  "glah"
has type
  String
but is expected to have type
  Nat
```
-/
def printTwice (s : String) : IO Unit := do
  IO.print s
  IO.print s

section
/-!
This section tests that section variables work as expected. They should be in scope for docstrings,
but they should not be added as parameters only due to being mentioned in the docstring.
-/
variable (howMany : Nat)

/--
Returns how many there are (that is, {name}`howMany`)
-/
def f := howMany

/--
Returns its argument (but not {name}`howMany`)
-/
def g (x : Nat) := x

/--
{name}`f` and {name}`g` are the same function (there's no extra parameter on {name}`g`)
-/
theorem f_eq_g : f = g := rfl

end

section
/-!
This tests the rules for {name}`open`.
-/

namespace A
def a := "a"
def b := "b"
end A

/-- error: Unknown constant `a` -/
#guard_msgs in
/--
{name}`a`
-/
def testDef := 15

#guard_msgs in
/--
{open A}

{name}`a` and {name}`b`
-/
def testDef' := 15

#guard_msgs in
/--
{open A only:=a}

{name}`a`
-/
def testDef'' := 15

/-- error: Unknown constant `b` -/
#guard_msgs in
/--
{open A only:=a}

{name}`b`
-/
def testDef''' := 15

#guard_msgs in
/--
{open A (only:=a) (only := b)}

{name}`b`
-/
def testDef'''' := 15


end

section
/-!
This section tests tactic references.
-/

namespace W
/--
Completely unlike {tactic}`grind`
-/
syntax (name := wiggleTac) "wiggle" (term)? term,*: tactic
end W

/--
The {tactic}`wiggle` tactic is not very powerful.

It can be referred to as {tactic}`W.wiggleTac`.

It can take a parameter! {tactic}`wiggle $t` where {name}`t` is some term.
Or even more: {tactic}`wiggle $t $[$t2],*`.

Conv tactics can be used similarly:
 * {conv}`arg`
 * {conv}`arg 1`
 * {conv}`ext $x`
-/
def something := ()

#check something

end


/--
Attributes are great!
Examples:
 * {attr}`grind`
 * {attr}`@[grind ←, simp]`
 * {attr}`init`
-/
def somethingElse := ()

/--
Options control Lean.
Examples:
 * Use the {option}`pp.all` to control showing all the details
 * {option}`set_option pp.all true` to set it
-/
def somethingElseAgain := ()


/--
error: Unknown option `pp.alll`
---
error: set_option value type mismatch: The value
  "true"
has type
  String
but the option `pp.all` expects a value of type
  Bool
-/
#guard_msgs in
/--
Options control Lean.
Examples:
 * Use the {option}`pp.alll` to control showing all the details
 * {option}`set_option pp.all "true"` to set it
-/
def somethingElseAgain' := ()


/--
{kw (cat := term)}`Type` {kw (of := termIfLet)}`if`
-/
def somethingElseAgain'' := ()

/--
info:

Hint: Specify the syntax kind:
  kw?̵ ̲(̲o̲f̲ ̲:̲=̲ ̲P̲a̲r̲s̲e̲r̲.̲T̲e̲r̲m̲.̲t̲y̲p̲e̲)̲
-/
#guard_msgs in
/--
{kw?}`Type`
-/
def somethingElseAgain''' := ()


/--
{syntaxCat}`term`
-/
def stxDoc := ()

/--
{syntaxCat}`thing`
-/
declare_syntax_cat thing

-- Parsing in docstrings should be in a context just after the decl is elaborated
/--
This is a thing: {syntax thing}`here{$n}` where {name}`n` is a numeral
-/
syntax "here " "{" num "}" : thing


/--
{syntax thing}`here{$n}`
-/
def yetMore := ()

@[inherit_doc yetMore]
def yetMore' := ()

#check yetMore'

/-
TODO test:
* Scope rules for all operators

-/
