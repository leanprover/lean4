import Lean

set_option doc.verso true

/-!
This test checks that the basic features of Verso docstrings work.
-/

open Lean Doc Elab Term


@[doc_code_block]
def c (s : StrLit) : DocM (Block ElabInline ElabBlock) := pure (Block.code (s.getString.toList.reverse |> String.mk))

@[doc_directive]
def d (s : TSyntaxArray `block) : DocM (Block ElabInline ElabBlock) := do
  .concat <$> s.reverse.mapM elabBlock

 /--
 one line, with a blank one

 -/
def oneLine := "one line"

set_option doc.verso false
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


set_option doc.verso true

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

  {lean}`P` relates non-zero {given (type :="Nat")}`m` to {given}`n` if it relates {lean}`n % m` to
  {lean}`m`.

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

/--
error: Unknown constant `a`

Hint: Insert a fully-qualified name:
  {name ̲(̲f̲u̲l̲l̲ ̲:̲=̲ ̲A̲.̲a̲)̲}`a`
-/
#guard_msgs in
/--
role {name}`a` here
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

/--
error: Unknown constant `b`

Hint: Insert a fully-qualified name:
  • {name ̲(̲f̲u̲l̲l̲ ̲:̲=̲ ̲A̲.̲b̲)̲}`b`
  • {name ̲(̲f̲u̲l̲l̲ ̲:̲=̲ ̲M̲e̲t̲a̲.̲G̲r̲i̲n̲d̲.̲A̲r̲i̲t̲h̲.̲C̲u̲t̲s̲a̲t̲.̲D̲v̲d̲S̲o̲l̲u̲t̲i̲o̲n̲.̲b̲)̲}`b`
-/
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
error: Unknown attribute `int`

Hint: Use a known attribute:
  • ini̲t
  • i̵n̵e̲x̲t
---
error: Unknown attribute `samp`

Hint: Use a known attribute:
  • s̵a̵m̵p̵s̲i̲m̲p̲
  • s̵a̵m̵p̵s̲y̲m̲m̲
  • s̵a̵m̵p̵c̲s̲i̲m̲p̲
---
error: Unknown attribute `inlone`

Hint: Use a known attribute:
  • i̵n̵l̵o̵n̵e̵i̲n̲l̲i̲n̲e̲
  • inl̵o̵n̵e̵i̲t̲
-/
#guard_msgs in
/--
Suggestions are as well.
 * {attr}`int`
 * {attr}`@[samp, inlone]`
-/
def otherAttr := ()

/--
error: Unknown constant `Constraint.add`

Hint: Insert a fully-qualified name:
  {name ̲(̲f̲u̲l̲l̲ ̲:̲=̲ ̲O̲m̲e̲g̲a̲.̲C̲o̲n̲s̲t̲r̲a̲i̲n̲t̲.̲a̲d̲d̲)̲}`Constraint.add`
-/
#guard_msgs in
/--
{name}`Constraint.add`
-/
def nameErrSuggestions := ()

/--
Options control Lean.
Examples:
 * Use the {option}`pp.all` to control showing all the details
 * {option}`set_option pp.all true` to set it
-/
def somethingElseAgain := ()

/- Commented out for bootstrapping
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
-/

/--
{kw (cat := term)}`Type` {kw (of := termIfLet)}`if`
-/
def somethingElseAgain'' := ()

/- Commented out for bootstrapping
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
-/

/--
{syntaxCat}`term`
-/
def stxDoc := ()

/--
{syntaxCat}`thing`
-/
declare_syntax_cat thing


syntax (name := here) "here " "{" num "}" : thing

/--
This is a thing: {syntax thing}`here{$n}` where {name}`n` is a numeral
-/
add_decl_doc «here»

/--
{syntax thing}`here{$n}`
-/
def yetMore := ()

@[inherit_doc yetMore]
def yetMore' := ()

#check yetMore'

-- Test that only actual attributes lead to suggestions
/--
warning: Code element could be more specific.

Hint: Insert a role to document it:
  • {̲a̲t̲t̲r̲}̲`instance`
  • {̲k̲w̲ ̲(̲o̲f̲ ̲:̲=̲ ̲L̲e̲a̲n̲.̲P̲a̲r̲s̲e̲r̲.̲A̲t̲t̲r̲.̲i̲n̲s̲t̲a̲n̲c̲e̲)̲}̲`instance` (in `attr`)
  • {̲s̲y̲n̲t̲a̲x̲ ̲a̲t̲t̲r̲}̲`instance`
  • Use the `lit` role:
    {̲l̲i̲t̲}̲`instance`
    to mark the code as literal text and disable suggestions
---
warning: Code element could be more specific.

Hint: Insert a role to document it:
  • {̲a̲t̲t̲r̲}̲`term_elab`
  • {̲g̲i̲v̲e̲n̲}̲`term_elab`
  • Use the `lit` role:
    {̲l̲i̲t̲}̲`term_elab`
    to mark the code as literal text and disable suggestions
---
warning: Code element could be more specific.

Hint: Insert a role to document it:
  • {̲g̲i̲v̲e̲n̲}̲`instantiation`
  • Use the `lit` role:
    {̲l̲i̲t̲}̲`instantiation`
    to mark the code as literal text and disable suggestions
-/
#guard_msgs in
/--
This one has its own parser: `instance`
This one is an identifier: `term_elab`
This is not an attribute: `instantiation`
-/
def attrSuggestionTest := ()

/--
error: Module is not transitively imported by the current module.

Hint: Either disable the existence check or use an imported module:
  {module ̲-̲c̲h̲e̲c̲k̲e̲d̲}`NonExistent`
---
error: Module is not transitively imported by the current module.

Hint: Either disable the existence check or use an imported module:
  • {module ̲-̲c̲h̲e̲c̲k̲e̲d̲}`Laen.Data.Jsn`
  • {module}`L̵a̵e̵n̵.̵D̵a̵t̵a̵.̵J̵s̵n̵L̲e̲a̲n̲.̲D̲a̲t̲a̲.̲J̲s̲o̲n̲`
---
error: Module is not transitively imported by the current module.

Hint: Either disable the existence check or use an imported module:
  • {module ̲-̲c̲h̲e̲c̲k̲e̲d̲}`Lean.Data.jso`
  • {module}`L̵e̵a̵n̵.̵D̵a̵t̵a̵.̵j̵s̵o̵L̲e̲a̲n̲.̲D̲a̲t̲a̲.̲J̲s̲o̲n̲`
  • {module}`L̵e̵a̵n̵.̵D̵a̵t̵a̵.̵j̵s̵o̵L̲e̲a̲n̲.̲D̲a̲t̲a̲.̲L̲s̲p̲`
-/
#guard_msgs in
/--
Error, no suggestions:
{module}`NonExistent`

Error, one suggestions:
{module}`Laen.Data.Jsn`

No error:
{module -checked}`NonExistent`

Error, two suggestions:
{module}`Lean.Data.jso`

No error:
{module}`Lean.Data.Json`
-/
def talksAboutModules := ()

/--
warning: Code element could be more specific.

Hint: Insert a role to document it:
  • {̲m̲o̲d̲u̲l̲e̲}̲`Lean.Data.Json.Basic`
  • Use the `lit` role:
    {̲l̲i̲t̲}̲`Lean.Data.Json.Basic`
    to mark the code as literal text and disable suggestions
-/
#guard_msgs in
/--
`Lean.Data.Json.Basic`
-/
def moduleSuggestionTest := ()

/-!
These are tests for the current workarounds for intra-module forward references.
-/

-- Saves the docs as text, then causes them to be elaborated later:
set_option doc.verso false
/--
Less than {name}`seven`.
-/
def five : Nat := 5
set_option doc.verso true

-- For this one, the docs are just added later.
def four : Nat := 4

/--
More than {name}`five`.
-/
def seven : Nat := 7

docs_to_verso five

/--
Less than {name}`seven`.
-/
add_decl_doc four

/-
TODO test:
* Scope rules for all operators

-/
