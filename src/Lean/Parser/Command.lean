/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Term
import Lean.Parser.Do

namespace Lean
namespace Parser

/-- Syntax quotation for terms. -/
@[builtin_term_parser] def Term.quot := leading_parser
  "`(" >> withoutPosition (incQuotDepth termParser) >> ")"
@[builtin_term_parser] def Term.precheckedQuot := leading_parser
  "`" >> Term.quot

namespace Command

/-- Skip input until the next character that satisfies the predicate, then skip whitespace -/
private def skipUntil (pred : Char → Bool) : Parser where
  fn :=
    andthenFn
      (takeUntilFn pred)
      (takeWhileFn Char.isWhitespace)

/-- Skip input until the next whitespace character (used for error recovery for certain tokens) -/
private def skipUntilWs : Parser := skipUntil Char.isWhitespace

/-- Skip input until the next whitespace character or delimiter (used for error recovery for certain
    tokens, especially names that occur in signatures) -/
private def skipUntilWsOrDelim : Parser := skipUntil fun c =>
  c.isWhitespace || c == '(' || c == ')' || c == ':' || c == '{' || c == '}' || c == '|'

/--
Syntax quotation for (sequences of) commands.
The identical syntax for term quotations takes priority,
so ambiguous quotations like `` `($x $y) `` will be parsed as an application,
not two commands. Use `` `($x:command $y:command) `` instead.
Multiple commands will be put in a `` `null `` node,
but a single command will not (so that you can directly
match against a quotation in a command kind's elaborator). -/
@[builtin_term_parser low] def quot := leading_parser
  "`(" >> withoutPosition (incQuotDepth (many1Unbox commandParser)) >> ")"

/--
`/-! <text> -/` defines a *module docstring* that can be displayed by documentation generation
tools. The string is associated with the corresponding position in the file. It can be used
multiple times in the same file.
-/
@[builtin_command_parser]
def moduleDoc := leading_parser ppDedent <|
  "/-!" >> commentBody >> ppLine

def namedPrio := leading_parser
  atomic (" (" >> nonReservedSymbol "priority") >> " := " >> withoutPosition priorityParser >> ")"
def optNamedPrio := optional namedPrio

def «private»        := leading_parser "private "
def «protected»      := leading_parser "protected "
def visibility       := «private» <|> «protected»
def «noncomputable»  := leading_parser "noncomputable "
def «unsafe»         := leading_parser "unsafe "
def «partial»        := leading_parser "partial "
def «nonrec»         := leading_parser "nonrec "

/-- `declModifiers` is the collection of modifiers on a declaration:
* a doc comment `/-- ... -/`
* a list of attributes `@[attr1, attr2]`
* a visibility specifier, `private` or `protected`
* `noncomputable`
* `unsafe`
* `partial` or `nonrec`

All modifiers are optional, and have to come in the listed order.

`nestedDeclModifiers` is the same as `declModifiers`, but attributes are printed
on the same line as the declaration. It is used for declarations nested inside other syntax,
such as inductive constructors, structure projections, and `let rec` / `where` definitions. -/
@[builtin_doc] def declModifiers (inline : Bool) := leading_parser
  optional docComment >>
  optional (Term.«attributes» >> if inline then skip else ppDedent ppLine) >>
  optional visibility >>
  optional «noncomputable» >>
  optional «unsafe» >>
  optional («partial» <|> «nonrec»)
/-- `declId` matches `foo` or `foo.{u,v}`: an identifier possibly followed by a list of universe names -/
-- @[builtin_doc] -- FIXME: suppress the hover
def declId := leading_parser
  ident >> optional (".{" >> sepBy1 (recover ident (skipUntil (fun c => c.isWhitespace || c ∈ [',', '}']))) ", " >> "}")
/-- `declSig` matches the signature of a declaration with required type: a list of binders and then `: type` -/
-- @[builtin_doc] -- FIXME: suppress the hover
def declSig := leading_parser
  many (ppSpace >> (Term.binderIdent <|> Term.bracketedBinder)) >> Term.typeSpec
/-- `optDeclSig` matches the signature of a declaration with optional type: a list of binders and then possibly `: type` -/
-- @[builtin_doc] -- FIXME: suppress the hover
def optDeclSig := leading_parser
  many (ppSpace >> (Term.binderIdent <|> Term.bracketedBinder)) >> Term.optType
/-- Right-hand side of a `:=` in a declaration, a term. -/
def declBody : Parser :=
  /-
  We want to make sure that bodies starting with `by` in fact create a single `by` node instead of
  accidentally parsing some remnants after it as well. This can especially happen when starting to
  type comments inside tactic blocks where
  ```
  by
    sleep 2000
    unfold f
    -starting comment here
  ```
  is parsed as
  ```
  (by
    sleep 2000
    unfold f
    ) - (starting comment here)
  ```
  where the new nesting will discard incrementality data. By using `byTactic`'s precedence, the
  stray `-` will be flagged as an unexpected token and will not disturb the syntax tree up to it. We
  do not call `byTactic` directly to avoid differences in pretty printing or behavior or error
  reporting between the two branches.
  -/
  lookahead (setExpected [] "by") >> termParser leadPrec <|>
  termParser

-- As the pretty printer ignores `lookahead`, we need a custom parenthesizer to choose the correct
-- precedence
open PrettyPrinter in
@[combinator_parenthesizer declBody] def declBody.parenthesizer : Parenthesizer :=
  Parenthesizer.categoryParser.parenthesizer `term 0

def declValSimple    := leading_parser
  " :=" >> ppHardLineUnlessUngrouped >> declBody >> Termination.suffix >> optional Term.whereDecls
def declValEqns      := leading_parser
  Term.matchAltsWhereDecls
def whereStructField := leading_parser
  Term.letDecl
def whereStructInst  := leading_parser
  ppIndent ppSpace >> "where" >> Term.structInstFields (sepByIndent (ppGroup whereStructField) "; " (allowTrailingSep := true)) >>
  optional Term.whereDecls
/-- `declVal` matches the right-hand side of a declaration, one of:
* `:= expr` (a "simple declaration")
* a sequence of `| pat => expr` (a declaration by equations), shorthand for a `match`
* `where` and then a sequence of `field := value` initializers, shorthand for a structure constructor
-/
@[builtin_doc] def declVal :=
  -- Remark: we should not use `Term.whereDecls` at `declVal`
  -- because `Term.whereDecls` is defined using `Term.letRecDecl` which may contain attributes.
  -- Issue #753 shows an example that fails to be parsed when we used `Term.whereDecls`.
  withAntiquot (mkAntiquot "declVal" decl_name% (isPseudoKind := true)) <|
    declValSimple <|> declValEqns <|> whereStructInst
def «abbrev»         := leading_parser
  "abbrev " >> declId >> ppIndent optDeclSig >> declVal
def optDefDeriving   :=
  optional (ppDedent ppLine >> atomic ("deriving " >> notSymbol "instance") >> sepBy1 ident ", ")
def definition     := leading_parser
  "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> declVal >> optDefDeriving
def «theorem»        := leading_parser
  "theorem " >> recover declId skipUntilWsOrDelim >> ppIndent declSig >> declVal
def «opaque»         := leading_parser
  "opaque " >> recover declId skipUntilWsOrDelim >> ppIndent declSig >> optional declValSimple
/- As `declSig` starts with a space, "instance" does not need a trailing space
  if we put `ppSpace` in the optional fragments. -/
def «instance»       := leading_parser
  Term.attrKind >> "instance" >> optNamedPrio >>
  optional (ppSpace >> declId) >> ppIndent declSig >> declVal
def «axiom»          := leading_parser
  "axiom " >> recover declId skipUntilWsOrDelim >> ppIndent declSig
/- As `declSig` starts with a space, "example" does not need a trailing space. -/
def «example»        := leading_parser
  "example" >> ppIndent optDeclSig >> declVal
def ctor             := leading_parser
  atomic (optional docComment >> "\n| ") >>
  ppGroup (declModifiers true >> rawIdent >> optDeclSig)
def derivingClasses  := sepBy1 ident ", "
def optDeriving      := leading_parser
  optional (ppLine >> atomic ("deriving " >> notSymbol "instance") >> derivingClasses)
def computedField    := leading_parser
  declModifiers true >> ident >> " : " >> termParser >> Term.matchAlts
def computedFields   := leading_parser
  "with" >> manyIndent (ppLine >> ppGroup computedField)
/--
In Lean, every concrete type other than the universes
and every type constructor other than dependent arrows
is an instance of a general family of type constructions known as inductive types.
It is remarkable that it is possible to construct a substantial edifice of mathematics
based on nothing more than the type universes, dependent arrow types, and inductive types;
everything else follows from those.
Intuitively, an inductive type is built up from a specified list of constructors.
For example, `List α` is the list of elements of type `α`, and is defined as follows:
```
inductive List (α : Type u) where
| nil
| cons (head : α) (tail : List α)
```
A list of elements of type `α` is either the empty list, `nil`,
or an element `head : α` followed by a list `tail : List α`.
See [Inductive types](https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html)
for more information.
-/
@[builtin_doc] def «inductive» := leading_parser
  "inductive " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> optional (symbol " :=" <|> " where") >>
  many ctor >> optional (ppDedent ppLine >> computedFields) >> optDeriving
def classInductive   := leading_parser
  atomic (group (symbol "class " >> "inductive ")) >>
  recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >>
  optional (symbol " :=" <|> " where") >> many ctor >> optDeriving
def structExplicitBinder := leading_parser
  atomic (declModifiers true >> "(") >>
  withoutPosition (many1 ident >> ppIndent optDeclSig >>
    optional (Term.binderTactic <|> Term.binderDefault)) >> ")"
def structImplicitBinder := leading_parser
  atomic (declModifiers true >> "{") >> withoutPosition (many1 ident >> declSig) >> "}"
def structInstBinder     := leading_parser
  atomic (declModifiers true >> "[") >> withoutPosition (many1 ident >> declSig) >> "]"
def structSimpleBinder   := leading_parser
  atomic (declModifiers true >> ident) >> optDeclSig >>
  optional (Term.binderTactic <|> Term.binderDefault)
def structFields         := leading_parser
  manyIndent <|
    ppLine >> checkColGe >> ppGroup (
      structExplicitBinder <|> structImplicitBinder <|>
      structInstBinder <|> structSimpleBinder)
def structCtor           := leading_parser
  atomic (ppIndent (declModifiers true >> ident >> " :: "))
def structureTk          := leading_parser
  "structure "
def classTk              := leading_parser
  "class "
def «extends»            := leading_parser
  " extends " >> sepBy1 termParser ", "
def «structure»          := leading_parser
    (structureTk <|> classTk) >>
    -- Note: no error recovery here due to clashing with the `class abbrev` syntax
    declId >>
    ppIndent (many (ppSpace >> Term.bracketedBinder) >> optional «extends» >> Term.optType) >>
    optional ((symbol " := " <|> " where ") >> optional structCtor >> structFields) >>
    optDeriving
@[builtin_command_parser] def declaration := leading_parser
  declModifiers false >>
  («abbrev» <|> definition <|> «theorem» <|> «opaque» <|> «instance» <|> «axiom» <|> «example» <|>
   «inductive» <|> classInductive <|> «structure»)
@[builtin_command_parser] def «deriving»     := leading_parser
  "deriving " >> "instance " >> derivingClasses >> " for " >> sepBy1 (recover ident skip) ", "
@[builtin_command_parser] def noncomputableSection := leading_parser
  "noncomputable " >> "section" >> optional (ppSpace >> checkColGt >> ident)
/--
A `section`/`end` pair delimits the scope of `variable`, `include, `open`, `set_option`, and `local`
commands. Sections can be nested. `section <id>` provides a label to the section that has to appear
with the matching `end`. In either case, the `end` can be omitted, in which case the section is
closed at the end of the file.
-/
@[builtin_command_parser] def «section»      := leading_parser
  "section" >> optional (ppSpace >> checkColGt >> ident)
/--
`namespace <id>` opens a section with label `<id>` that influences naming and name resolution inside
the section:
* Declarations names are prefixed: `def seventeen : ℕ := 17` inside a namespace `Nat` is given the
  full name `Nat.seventeen`.
* Names introduced by `export` declarations are also prefixed by the identifier.
* All names starting with `<id>.` become available in the namespace without the prefix. These names
  are preferred over names introduced by outer namespaces or `open`.
* Within a namespace, declarations can be `protected`, which excludes them from the effects of
  opening the namespace.

As with `section`, namespaces can be nested and the scope of a namespace is terminated by a
corresponding `end <id>` or the end of the file.

`namespace` also acts like `section` in delimiting the scope of `variable`, `open`, and other scoped commands.
-/
@[builtin_command_parser] def «namespace»    := leading_parser
  "namespace " >> checkColGt >> ident
/--
`end` closes a `section` or `namespace` scope. If the scope is named `<id>`, it has to be closed
with `end <id>`. The `end` command is optional at the end of a file.
-/
@[builtin_command_parser] def «end»          := leading_parser
  "end" >> optional (ppSpace >> checkColGt >> ident)
/-- Declares one or more typed variables, or modifies whether already-declared variables are
  implicit.

Introduces variables that can be used in definitions within the same `namespace` or `section` block.
When a definition mentions a variable, Lean will add it as an argument of the definition. This is
useful in particular when writing many definitions that have parameters in common (see below for an
example).

Variable declarations have the same flexibility as regular function parameters. In particular they
can be [explicit, implicit][binder docs], or [instance implicit][tpil classes] (in which case they
can be anonymous). This can be changed, for instance one can turn explicit variable `x` into an
implicit one with `variable {x}`. Note that currently, you should avoid changing how variables are
bound and declare new variables at the same time; see [issue 2789] for more on this topic.

In *theorem bodies* (i.e. proofs), variables are not included based on usage in order to ensure that
changes to the proof cannot change the statement of the overall theorem. Instead, variables are only
available to the proof if they have been mentioned in the theorem header or in an `include` command
or are instance implicit and depend only on such variables.

See [*Variables and Sections* from Theorem Proving in Lean][tpil vars] for a more detailed
discussion.

[tpil vars]:
https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#variables-and-sections
(Variables and Sections on Theorem Proving in Lean) [tpil classes]:
https://lean-lang.org/theorem_proving_in_lean4/type_classes.html (Type classes on Theorem Proving in
Lean) [binder docs]:
https://leanprover-community.github.io/mathlib4_docs/Lean/Expr.html#Lean.BinderInfo (Documentation
for the BinderInfo type) [issue 2789]: https://github.com/leanprover/lean4/issues/2789 (Issue 2789
on github)

## Examples

```lean
section
  variable
    {α : Type u}      -- implicit
    (a : α)           -- explicit
    [instBEq : BEq α] -- instance implicit, named
    [Hashable α]      -- instance implicit, anonymous

  def isEqual (b : α) : Bool :=
    a == b

  #check isEqual
  -- isEqual.{u} {α : Type u} (a : α) [instBEq : BEq α] (b : α) : Bool

  variable
    {a} -- `a` is implicit now

  def eqComm {b : α} := a == b ↔ b == a

  #check eqComm
  -- eqComm.{u} {α : Type u} {a : α} [instBEq : BEq α] {b : α} : Prop
end
```

The following shows a typical use of `variable` to factor out definition arguments:

```lean
variable (Src : Type)

structure Logger where
  trace : List (Src × String)
#check Logger
-- Logger (Src : Type) : Type

namespace Logger
  -- switch `Src : Type` to be implicit until the `end Logger`
  variable {Src}

  def empty : Logger Src where
    trace := []
  #check empty
  -- Logger.empty {Src : Type} : Logger Src

  variable (log : Logger Src)

  def len :=
    log.trace.length
  #check len
  -- Logger.len {Src : Type} (log : Logger Src) : Nat

  variable (src : Src) [BEq Src]

  -- at this point all of `log`, `src`, `Src` and the `BEq` instance can all become arguments

  def filterSrc :=
    log.trace.filterMap
      fun (src', str') => if src' == src then some str' else none
  #check filterSrc
  -- Logger.filterSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : List String

  def lenSrc :=
    log.filterSrc src |>.length
  #check lenSrc
  -- Logger.lenSrc {Src : Type} (log : Logger Src) (src : Src) [inst✝ : BEq Src] : Nat
end Logger
```

The following example demonstrates availability of variables in proofs:
```lean
variable
  {α : Type}    -- available in the proof as indirectly mentioned through `a`
  [ToString α]  -- available in the proof as `α` is included
  (a : α)       -- available in the proof as mentioned in the header
  {β : Type}    -- not available in the proof
  [ToString β]  -- not available in the proof

theorem ex : a = a := rfl
```
After elaboration of the proof, the following warning will be generated to highlight the unused
hypothesis:
```
included section variable '[ToString α]' is not used in 'ex', consider excluding it
```
In such cases, the offending variable declaration should be moved down or into a section so that
only theorems that do depend on it follow it until the end of the section.
-/
@[builtin_command_parser] def «variable»     := leading_parser
  "variable" >> many1 (ppSpace >> checkColGt >> Term.bracketedBinder)
/-- Declares one or more universe variables.

`universe u v`

`Prop`, `Type`, `Type u` and `Sort u` are types that classify other types, also known as
*universes*. In `Type u` and `Sort u`, the variable `u` stands for the universe's *level*, and a
universe at level `u` can only classify universes that are at levels lower than `u`. For more
details on type universes, please refer to [the relevant chapter of Theorem Proving in Lean][tpil
universes].

Just as type arguments allow polymorphic definitions to be used at many different types, universe
parameters, represented by universe variables, allow a definition to be used at any required level.
While Lean mostly handles universe levels automatically, declaring them explicitly can provide more
control when writing signatures. The `universe` keyword allows the declared universe variables to be
used in a collection of definitions, and Lean will ensure that these definitions use them
consistently.

[tpil universes]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#types-as-objects
(Type universes on Theorem Proving in Lean)

```lean
/- Explicit type-universe parameter. -/
def id₁.{u} (α : Type u) (a : α) := a

/- Implicit type-universe parameter, equivalent to `id₁`.
  Requires option `autoImplicit true`, which is the default. -/
def id₂ (α : Type u) (a : α) := a

/- Explicit standalone universe variable declaration, equivalent to `id₁` and `id₂`. -/
universe u
def id₃ (α : Type u) (a : α) := a
```

On a more technical note, using a universe variable only in the right-hand side of a definition
causes an error if the universe has not been declared previously.

```lean
def L₁.{u} := List (Type u)

-- def L₂ := List (Type u) -- error: `unknown universe level 'u'`

universe u
def L₃ := List (Type u)
```

## Examples

```lean
universe u v w

structure Pair (α : Type u) (β : Type v) : Type (max u v) where
  a : α
  b : β

#check Pair.{v, w}
-- Pair : Type v → Type w → Type (max v w)
```
-/
@[builtin_command_parser] def «universe»     := leading_parser
  "universe" >> many1 (ppSpace >> checkColGt >> ident)
@[builtin_command_parser] def check          := leading_parser
  "#check " >> termParser
@[builtin_command_parser] def check_failure  := leading_parser
  "#check_failure " >> termParser -- Like `#check`, but succeeds only if term does not type check
/--
`#eval e` evaluates the expression `e` by compiling and evaluating it.

* The command attempts to use `ToExpr`, `Repr`, or `ToString` instances to print the result.
* If `e` is a monadic value of type `m ty`, then the command tries to adapt the monad `m`
  to one of the monads that `#eval` supports, which include `IO`, `CoreM`, `MetaM`, `TermElabM`, and `CommandElabM`.
  Users can define `MonadEval` instances to extend the list of supported monads.

The `#eval` command gracefully degrades in capability depending on what is imported.
Importing the `Lean.Elab.Command` module provides full capabilities.

Due to unsoundness, `#eval` refuses to evaluate expressions that depend on `sorry`, even indirectly,
since the presence of `sorry` can lead to runtime instability and crashes.
This check can be overridden with the `#eval! e` command.

Options:
* If `eval.pp` is true (default: true) then tries to use `ToExpr` instances to make use of the
  usual pretty printer. Otherwise, only tries using `Repr` and `ToString` instances.
* If `eval.type` is true (default: false) then pretty prints the type of the evaluated value.
* If `eval.derive.repr` is true (default: true) then attempts to auto-derive a `Repr` instance
  when there is no other way to print the result.

See also: `#reduce e` for evaluation by term reduction.
-/
@[builtin_command_parser, builtin_doc] def eval := leading_parser
  "#eval " >> termParser
@[builtin_command_parser, inherit_doc eval] def evalBang := leading_parser
  "#eval! " >> termParser
@[builtin_command_parser] def synth          := leading_parser
  "#synth " >> termParser
@[builtin_command_parser] def exit           := leading_parser
  "#exit"
@[builtin_command_parser] def print          := leading_parser
  "#print " >> (ident <|> strLit)
@[builtin_command_parser] def printAxioms    := leading_parser
  "#print " >> nonReservedSymbol "axioms " >> ident
@[builtin_command_parser] def printEqns      := leading_parser
  "#print " >> (nonReservedSymbol "equations " <|> nonReservedSymbol "eqns ") >> ident
/--
Displays all available tactic tags, with documentation.
-/
@[builtin_command_parser] def printTacTags   := leading_parser
  "#print " >> nonReservedSymbol "tactic " >> nonReservedSymbol "tags"
/--
`#where` gives a description of the state of the current scope scope.
This includes the current namespace, `open` namespaces, `universe` and `variable` commands,
and options set with `set_option`.
-/
@[builtin_command_parser] def «where»        := leading_parser
  "#where"
/-- Shows the current Lean version. Prints `Lean.versionString`. -/
@[builtin_command_parser] def version        := leading_parser
  "#version"
@[builtin_command_parser] def «init_quot»    := leading_parser
  "init_quot"
def optionValue := nonReservedSymbol "true" <|> nonReservedSymbol "false" <|> strLit <|> numLit
/--
`set_option <id> <value>` sets the option `<id>` to `<value>`. Depending on the type of the option,
the value can be `true`, `false`, a string, or a numeral. Options are used to configure behavior of
Lean as well as user-defined extensions. The setting is active until the end of the current `section`
or `namespace` or the end of the file.
Auto-completion is available for `<id>` to list available options.

`set_option <id> <value> in <command>` sets the option for just a single command:
```
set_option pp.all true in
#check 1 + 1
```
Similarly, `set_option <id> <value> in` can also be used inside terms and tactics to set an option
only in a single term or tactic.
-/
@[builtin_command_parser] def «set_option»   := leading_parser
  "set_option " >> identWithPartialTrailingDot >> ppSpace >> optionValue
def eraseAttr := leading_parser
  "-" >> rawIdent
@[builtin_command_parser] def «attribute»    := leading_parser
  "attribute " >> "[" >>
    withoutPosition (sepBy1 (eraseAttr <|> Term.attrInstance) ", ") >>
  "]" >> many1 (ppSpace >> ident)
/-- Adds names from other namespaces to the current namespace.

The command `export Some.Namespace (name₁ name₂)` makes `name₁` and `name₂`:

- visible in the current namespace without prefix `Some.Namespace`, like `open`, and
- visible from outside the current namespace `N` as `N.name₁` and `N.name₂`.

## Examples

```lean
namespace Morning.Sky
  def star := "venus"
end Morning.Sky

namespace Evening.Sky
  export Morning.Sky (star)
  -- `star` is now in scope
  #check star
end Evening.Sky

-- `star` is visible in `Evening.Sky`
#check Evening.Sky.star
```
-/
@[builtin_command_parser] def «export»       := leading_parser
  "export " >> ident >> " (" >> many1 ident >> ")"
@[builtin_command_parser] def «import»       := leading_parser
  "import" -- not a real command, only for error messages
def openHiding       := leading_parser
  ppSpace >> atomic (ident >> " hiding") >> many1 (ppSpace >> checkColGt >> ident)
def openRenamingItem := leading_parser
  ident >> unicodeSymbol " → " " -> " >> checkColGt >> ident
def openRenaming     := leading_parser
  ppSpace >> atomic (ident >> " renaming ") >> sepBy1 openRenamingItem ", "
def openOnly         := leading_parser
  ppSpace >> atomic (ident >> " (") >> many1 ident >> ")"
def openSimple       := leading_parser
  many1 (ppSpace >> checkColGt >> ident)
def openScoped       := leading_parser
  " scoped" >> many1 (ppSpace >> checkColGt >> ident)
/-- `openDecl` is the body of an `open` declaration (see `open`) -/
@[builtin_doc] def openDecl :=
  withAntiquot (mkAntiquot "openDecl" `Lean.Parser.Command.openDecl (isPseudoKind := true)) <|
    openHiding <|> openRenaming <|> openOnly <|> openSimple <|> openScoped
/-- Makes names from other namespaces visible without writing the namespace prefix.

Names that are made available with `open` are visible within the current `section` or `namespace`
block. This makes referring to (type) definitions and theorems easier, but note that it can also
make [scoped instances], notations, and attributes from a different namespace available.

The `open` command can be used in a few different ways:

* `open Some.Namespace.Path1 Some.Namespace.Path2` makes all non-protected names in
  `Some.Namespace.Path1` and `Some.Namespace.Path2` available without the prefix, so that
  `Some.Namespace.Path1.x` and `Some.Namespace.Path2.y` can be referred to by writing only `x` and
  `y`.

* `open Some.Namespace.Path hiding def1 def2` opens all non-protected names in `Some.Namespace.Path`
  except `def1` and `def2`.

* `open Some.Namespace.Path (def1 def2)` only makes `Some.Namespace.Path.def1` and
  `Some.Namespace.Path.def2` available without the full prefix, so `Some.Namespace.Path.def3` would
  be unaffected.

  This works even if `def1` and `def2` are `protected`.

* `open Some.Namespace.Path renaming def1 → def1', def2 → def2'` same as `open Some.Namespace.Path
  (def1 def2)` but `def1`/`def2`'s names are changed to `def1'`/`def2'`.

  This works even if `def1` and `def2` are `protected`.

* `open scoped Some.Namespace.Path1 Some.Namespace.Path2` **only** opens [scoped instances],
  notations, and attributes from `Namespace1` and `Namespace2`; it does **not** make any other name
  available.

* `open <any of the open shapes above> in` makes the names `open`-ed visible only in the next
  command or expression.

[scoped instance]: https://lean-lang.org/theorem_proving_in_lean4/type_classes.html#scoped-instances
(Scoped instances in Theorem Proving in Lean)


## Examples

```lean
/-- SKI combinators https://en.wikipedia.org/wiki/SKI_combinator_calculus -/
namespace Combinator.Calculus
  def I (a : α) : α := a
  def K (a : α) : β → α := fun _ => a
  def S (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
end Combinator.Calculus

section
  -- open everything under `Combinator.Calculus`, *i.e.* `I`, `K` and `S`,
  -- until the section ends
  open Combinator.Calculus

  theorem SKx_eq_K : S K x = I := rfl
end

-- open everything under `Combinator.Calculus` only for the next command (the next `theorem`, here)
open Combinator.Calculus in
theorem SKx_eq_K' : S K x = I := rfl

section
  -- open only `S` and `K` under `Combinator.Calculus`
  open Combinator.Calculus (S K)

  theorem SKxy_eq_y : S K x y = y := rfl

  -- `I` is not in scope, we have to use its full path
  theorem SKxy_eq_Iy : S K x y = Combinator.Calculus.I y := rfl
end

section
  open Combinator.Calculus
    renaming
      I → identity,
      K → konstant

  #check identity
  #check konstant
end

section
  open Combinator.Calculus
    hiding S

  #check I
  #check K
end

section
  namespace Demo
    inductive MyType
    | val

    namespace N1
      scoped infix:68 " ≋ " => BEq.beq

      scoped instance : BEq MyType where
        beq _ _ := true

      def Alias := MyType
    end N1
  end Demo

  -- bring `≋` and the instance in scope, but not `Alias`
  open scoped Demo.N1

  #check Demo.MyType.val == Demo.MyType.val
  #check Demo.MyType.val ≋ Demo.MyType.val
  -- #check Alias -- unknown identifier 'Alias'
end
```
-/
@[builtin_command_parser] def «open»    := leading_parser
  withPosition ("open" >> openDecl)

@[builtin_command_parser] def «mutual» := leading_parser
  "mutual" >> many1 (ppLine >> notSymbol "end" >> commandParser) >>
  ppDedent (ppLine >> "end")
def initializeKeyword := leading_parser
  "initialize " <|> "builtin_initialize "
@[builtin_command_parser] def «initialize» := leading_parser
  declModifiers false >> initializeKeyword >>
  optional (atomic (ident >> Term.typeSpec >> ppSpace >> Term.leftArrow)) >> Term.doSeq

@[builtin_command_parser] def «in»  := trailing_parser
  withOpen (ppDedent (" in " >> commandParser))

/--
Adds a docstring to an existing declaration, replacing any existing docstring.
The provided docstring should be written as a docstring for the `add_decl_doc` command, as in
```
/-- My new docstring -/
add_decl_doc oldDeclaration
```

This is useful for auto-generated declarations
for which there is no place to write a docstring in the source code.

Parent projections in structures are an example of this:
```
structure Triple (α β γ : Type) extends Prod α β where
  thrd : γ

/-- Extracts the first two projections of a triple. -/
add_decl_doc Triple.toProd
```

Documentation can only be added to declarations in the same module.
-/
@[builtin_command_parser] def addDocString := leading_parser
  docComment >> "add_decl_doc " >> ident

/--
Register a tactic tag, saving its user-facing name and docstring.

Tactic tags can be used by documentation generation tools to classify related tactics.
-/
@[builtin_command_parser] def «register_tactic_tag» := leading_parser
  optional (docComment >> ppLine) >>
  "register_tactic_tag " >> ident >> strLit

/--
Add more documentation as an extension of the documentation for a given tactic.

The extended documentation is placed in the command's docstring. It is shown as part of a bulleted
list, so it should be brief.
-/
@[builtin_command_parser] def «tactic_extension» := leading_parser
  optional (docComment >> ppLine) >>
  "tactic_extension " >> ident


/--
  This is an auxiliary command for generation constructor injectivity theorems for
  inductive types defined at `Prelude.lean`.
  It is meant for bootstrapping purposes only. -/
@[builtin_command_parser] def genInjectiveTheorems := leading_parser
  "gen_injective_theorems% " >> ident

/--
`include eeny meeny` instructs Lean to include the section `variable`s `eeny` and `meeny` in all
theorems in the remainder of the current section, differing from the default behavior of
conditionally including variables based on use in the theorem header. Other commands are
not affected. `include` is usually followed by `in theorem ...` to limit the inclusion
to the subsequent declaration.
-/
@[builtin_command_parser] def «include» := leading_parser "include " >> many1 ident

/--
`omit` instructs Lean to not include a variable previously `include`d. Apart from variable names, it
can also refer to typeclass instance variables by type using the syntax `omit [TypeOfInst]`, in
which case all instance variables that unify with the given type are omitted. `omit` should usually
only be used in conjunction with `in` in order to keep the section structure simple.
-/
@[builtin_command_parser] def «omit» := leading_parser "omit " >>
  many1 (ident <|> Term.instBinder)

/-- No-op parser used as syntax kind for attaching remaining whitespace at the end of the input. -/
@[run_builtin_parser_attribute_hooks] def eoi : Parser := leading_parser ""

builtin_initialize
  registerBuiltinNodeKind ``eoi

@[run_builtin_parser_attribute_hooks, inherit_doc declModifiers]
abbrev declModifiersF := declModifiers false
@[run_builtin_parser_attribute_hooks, inherit_doc declModifiers]
abbrev declModifiersT := declModifiers true

builtin_initialize
  register_parser_alias (kind := ``declModifiers) "declModifiers"       declModifiersF
  register_parser_alias (kind := ``declModifiers) "nestedDeclModifiers" declModifiersT
  register_parser_alias                                                 declId
  register_parser_alias                                                 declSig
  register_parser_alias                                                 declVal
  register_parser_alias                                                 optDeclSig
  register_parser_alias                                                 openDecl
  register_parser_alias                                                 docComment

end Command

namespace Term
/--
`open Foo in e` is like `open Foo` but scoped to a single term.
It makes the given namespaces available in the term `e`.
-/
@[builtin_term_parser] def «open» := leading_parser:leadPrec
  "open" >> Command.openDecl >> withOpenDecl (" in " >> termParser)

/--
`set_option opt val in e` is like `set_option opt val` but scoped to a single term.
It sets the option `opt` to the value `val` in the term `e`.
-/
@[builtin_term_parser] def «set_option» := leading_parser:leadPrec
  "set_option " >> identWithPartialTrailingDot >> ppSpace >> Command.optionValue >> " in " >> termParser
end Term

namespace Tactic
/-- `open Foo in tacs` (the tactic) acts like `open Foo` at command level,
but it opens a namespace only within the tactics `tacs`. -/
@[builtin_tactic_parser] def «open» := leading_parser:leadPrec
  "open " >> Command.openDecl >> withOpenDecl (" in " >> tacticSeq)

/-- `set_option opt val in tacs` (the tactic) acts like `set_option opt val` at the command level,
but it sets the option only within the tactics `tacs`. -/
@[builtin_tactic_parser] def «set_option» := leading_parser:leadPrec
  "set_option " >> identWithPartialTrailingDot >> ppSpace >> Command.optionValue >> " in " >> tacticSeq
end Tactic

end Parser
end Lean
