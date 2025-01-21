/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude
import Init.Coe
set_option linter.missingDocs true -- keep it documented

namespace Lean

/--
Auxiliary type used to represent syntax categories. We mainly use auxiliary
definitions with this type to attach doc strings to syntax categories.
-/
structure Parser.Category

namespace Parser.Category

/-- `command` is the syntax category for things that appear at the top level
of a lean file. For example, `def foo := 1` is a `command`, as is
`namespace Foo` and `end Foo`. Commands generally have an effect on the state of
adding something to the environment (like a new definition), as well as
commands like `variable` which modify future commands within a scope. -/
def command : Category := {}

/-- `term` is the builtin syntax category for terms. A term denotes an expression
in lean's type theory, for example `2 + 2` is a term. The difference between
`Term` and `Expr` is that the former is a kind of syntax, while the latter is
the result of elaboration. For example `by simp` is also a `Term`, but it elaborates
to different `Expr`s depending on the context. -/
def term : Category := {}

/-- `tactic` is the builtin syntax category for tactics. These appear after
`by` in proofs, and they are programs that take in the proof context
(the hypotheses in scope plus the type of the term to synthesize) and construct
a term of the expected type. For example, `simp` is a tactic, used in:
```
example : 2 + 2 = 4 := by simp
```
-/
def tactic : Category := {}

/-- `doElem` is a builtin syntax category for elements that can appear in the `do` notation.
For example, `let x ← e` is a `doElem`, and a `do` block consists of a list of `doElem`s. -/
def doElem : Category := {}

/-- `structInstFieldDecl` is the syntax category for value declarations for fields in structure instance notation.
For example, the `:= 1` and `| 0 => 0 | n + 1 => n` in `{ x := 1, f | 0 => 0 | n + 1 => n }` are in the `structInstFieldDecl` class. -/
def structInstFieldDecl : Category := {}

/-- `level` is a builtin syntax category for universe levels.
This is the `u` in `Sort u`: it can contain `max` and `imax`, addition with
constants, and variables. -/
def level : Category := {}

/-- `attr` is a builtin syntax category for attributes.
Declarations can be annotated with attributes using the `@[...]` notation. -/
def attr : Category := {}

/-- `stx` is a builtin syntax category for syntax. This is the abbreviated
parser notation used inside `syntax` and `macro` declarations. -/
def stx : Category := {}

/-- `prio` is a builtin syntax category for priorities.
Priorities are used in many different attributes.
Higher numbers denote higher priority, and for example typeclass search will
try high priority instances before low priority.
In addition to literals like `37`, you can also use `low`, `mid`, `high`, as well as
add and subtract priorities. -/
def prio : Category := {}

/-- `prec` is a builtin syntax category for precedences. A precedence is a value
that expresses how tightly a piece of syntax binds: for example `1 + 2 * 3` is
parsed as `1 + (2 * 3)` because `*` has a higher precedence than `+`.
Higher numbers denote higher precedence.
In addition to literals like `37`, there are some special named precedence levels:
* `arg` for the precedence of function arguments
* `max` for the highest precedence used in term parsers (not actually the maximum possible value)
* `lead` for the precedence of terms not supposed to be used as arguments
and you can also add and subtract precedences. -/
def prec : Category := {}

end Parser.Category

namespace Parser.Syntax

/-! DSL for specifying parser precedences and priorities -/

/-- Addition of precedences. This is normally used only for offsetting, e.g. `max + 1`. -/
syntax:65 (name := addPrec) prec " + " prec:66 : prec
/-- Subtraction of precedences. This is normally used only for offsetting, e.g. `max - 1`. -/
syntax:65 (name := subPrec) prec " - " prec:66 : prec

/-- Addition of priorities. This is normally used only for offsetting, e.g. `default + 1`. -/
syntax:65 (name := addPrio) prio " + " prio:66 : prio
/-- Subtraction of priorities. This is normally used only for offsetting, e.g. `default - 1`. -/
syntax:65 (name := subPrio) prio " - " prio:66 : prio

end Parser.Syntax

instance : CoeOut (TSyntax ks) Syntax where
  coe stx := stx.raw

instance : Coe SyntaxNodeKind SyntaxNodeKinds where
  coe k := List.cons k List.nil

end Lean

/--
Maximum precedence used in term parsers, in particular for terms in
function position (`ident`, `paren`, ...)
-/
macro "max"  : prec => `(prec| 1024)
/-- Precedence used for application arguments (`do`, `by`, ...). -/
macro "arg"  : prec => `(prec| 1023)
/-- Precedence used for terms not supposed to be used as arguments (`let`, `have`, ...). -/
macro "lead" : prec => `(prec| 1022)
/-- Parentheses are used for grouping precedence expressions. -/
macro "(" p:prec ")" : prec => return p
/-- Minimum precedence used in term parsers. -/
macro "min"  : prec => `(prec| 10)
/-- `(min+1)` (we can only write `min+1` after `Meta.lean`) -/
macro "min1" : prec => `(prec| 11)
/--
`max:prec` as a term. It is equivalent to `eval_prec max` for `eval_prec` defined at `Meta.lean`.
We use `max_prec` to workaround bootstrapping issues.
-/
macro "max_prec" : term => `(1024)

/-- The default priority `default = 1000`, which is used when no priority is set. -/
macro "default" : prio => `(prio| 1000)
/-- The standardized "low" priority `low = 100`, for things that should be lower than default priority. -/
macro "low"     : prio => `(prio| 100)
/--
The standardized "medium" priority `mid = 500`. This is lower than `default`, and higher than `low`.
-/
macro "mid"     : prio => `(prio| 500)
/-- The standardized "high" priority `high = 10000`, for things that should be higher than default priority. -/
macro "high"    : prio => `(prio| 10000)
/-- Parentheses are used for grouping priority expressions. -/
macro "(" p:prio ")" : prio => return p

/-
Note regarding priorities. We want `low < mid < default` because we have the following default instances:
```
@[default_instance low] instance (n : Nat) : OfNat Nat n where ...
@[default_instance mid] instance : Neg Int where ...
@[default_instance default] instance [Add α] : HAdd α α α where ...
@[default_instance default] instance [Sub α] : HSub α α α where ...
...
```

Monomorphic default instances must always "win" to preserve the Lean 3 monomorphic "look&feel".
The `Neg Int` instance must have precedence over the `OfNat Nat n` one, otherwise we fail to elaborate `#check -42`
See issue #1813 for an example that failed when `mid = default`.
-/

-- Basic notation for defining parsers
-- NOTE: precedence must be at least `arg` to be used in `macro` without parentheses

/--
`p+` is shorthand for `many1(p)`. It uses parser `p` 1 or more times, and produces a
`nullNode` containing the array of parsed results. This parser has arity 1.

If `p` has arity more than 1, it is auto-grouped in the items generated by the parser.
-/
syntax:arg stx:max "+" : stx

/--
`p*` is shorthand for `many(p)`. It uses parser `p` 0 or more times, and produces a
`nullNode` containing the array of parsed results. This parser has arity 1.

If `p` has arity more than 1, it is auto-grouped in the items generated by the parser.
-/
syntax:arg stx:max "*" : stx

/--
`(p)?` is shorthand for `optional(p)`. It uses parser `p` 0 or 1 times, and produces a
`nullNode` containing the array of parsed results. This parser has arity 1.

`p` is allowed to have arity n > 1 (in which case the node will have either 0 or n children),
but if it has arity 0 then the result will be ambiguous.

Because `?` is an identifier character, `ident?` will not work as intended.
You have to write either `ident ?` or `(ident)?` for it to parse as the `?` combinator
applied to the `ident` parser.
-/
syntax:arg stx:max "?" : stx

/--
`p1 <|> p2` is shorthand for `orelse(p1, p2)`, and parses either `p1` or `p2`.
It does not backtrack, meaning that if `p1` consumes at least one token then
`p2` will not be tried. Therefore, the parsers should all differ in their first
token. The `atomic(p)` parser combinator can be used to locally backtrack a parser.
(For full backtracking, consider using extensible syntax classes instead.)

On success, if the inner parser does not generate exactly one node, it will be
automatically wrapped in a `group` node, so the result will always be arity 1.

The `<|>` combinator does not generate a node of its own, and in particular
does not tag the inner parsers to distinguish them, which can present a problem
when reconstructing the parse. A well formed `<|>` parser should use disjoint
node kinds for `p1` and `p2`.
-/
syntax:2 stx:2 " <|> " stx:1 : stx

macro_rules
  | `(stx| $p +) => `(stx| many1($p))
  | `(stx| $p *) => `(stx| many($p))
  | `(stx| $p ?) => `(stx| optional($p))
  | `(stx| $p₁ <|> $p₂) => `(stx| orelse($p₁, $p₂))

/--
`p,*` is shorthand for `sepBy(p, ",")`. It parses 0 or more occurrences of
`p` separated by `,`, that is: `empty | p | p,p | p,p,p | ...`.

It produces a `nullNode` containing a `SepArray` with the interleaved parser
results. It has arity 1, and auto-groups its component parser if needed.
-/
macro:arg x:stx:max ",*"   : stx => `(stx| sepBy($x, ",", ", "))
/--
`p,+` is shorthand for `sepBy(p, ",")`. It parses 1 or more occurrences of
`p` separated by `,`, that is: `p | p,p | p,p,p | ...`.

It produces a `nullNode` containing a `SepArray` with the interleaved parser
results. It has arity 1, and auto-groups its component parser if needed.
-/
macro:arg x:stx:max ",+"   : stx => `(stx| sepBy1($x, ",", ", "))

/--
`p,*,?` is shorthand for `sepBy(p, ",", allowTrailingSep)`.
It parses 0 or more occurrences of `p` separated by `,`, possibly including
a trailing `,`, that is: `empty | p | p, | p,p | p,p, | p,p,p | ...`.

It produces a `nullNode` containing a `SepArray` with the interleaved parser
results. It has arity 1, and auto-groups its component parser if needed.
-/
macro:arg x:stx:max ",*,?" : stx => `(stx| sepBy($x, ",", ", ", allowTrailingSep))

/--
`p,+,?` is shorthand for `sepBy1(p, ",", allowTrailingSep)`.
It parses 1 or more occurrences of `p` separated by `,`, possibly including
a trailing `,`, that is: `p | p, | p,p | p,p, | p,p,p | ...`.

It produces a `nullNode` containing a `SepArray` with the interleaved parser
results. It has arity 1, and auto-groups its component parser if needed.
-/
macro:arg x:stx:max ",+,?" : stx => `(stx| sepBy1($x, ",", ", ", allowTrailingSep))

/--
`!p` parses the negation of `p`. That is, it fails if `p` succeeds, and
otherwise parses nothing. It has arity 0.
-/
macro:arg "!" x:stx:max : stx => `(stx| notFollowedBy($x))

/--
The `nat_lit n` macro constructs "raw numeric literals". This corresponds to the
`Expr.lit (.natVal n)` constructor in the `Expr` data type.

Normally, when you write a numeral like `#check 37`, the parser turns this into
an application of `OfNat.ofNat` to the raw literal `37` to cast it into the
target type, even if this type is `Nat` (so the cast is the identity function).
But sometimes it is necessary to talk about the raw numeral directly,
especially when proving properties about the `ofNat` function itself.
-/
syntax (name := rawNatLit) "nat_lit " num : term

@[inherit_doc] infixr:90 " ∘ "  => Function.comp
@[inherit_doc] infixr:35 " × "  => Prod
@[inherit_doc] infixr:35 " ×' " => PProd

@[inherit_doc] infix:50  " ∣ " => Dvd.dvd
@[inherit_doc] infixl:55 " ||| " => HOr.hOr
@[inherit_doc] infixl:58 " ^^^ " => HXor.hXor
@[inherit_doc] infixl:60 " &&& " => HAnd.hAnd
@[inherit_doc] infixl:65 " + "   => HAdd.hAdd
@[inherit_doc] infixl:65 " - "   => HSub.hSub
@[inherit_doc] infixl:70 " * "   => HMul.hMul
@[inherit_doc] infixl:70 " / "   => HDiv.hDiv
@[inherit_doc] infixl:70 " % "   => HMod.hMod
@[inherit_doc] infixl:75 " <<< " => HShiftLeft.hShiftLeft
@[inherit_doc] infixl:75 " >>> " => HShiftRight.hShiftRight
@[inherit_doc] infixr:80 " ^ "   => HPow.hPow
@[inherit_doc] infixl:65 " ++ "  => HAppend.hAppend
@[inherit_doc] prefix:75 "-"    => Neg.neg
@[inherit_doc] prefix:100 "~~~"  => Complement.complement

/-!
  Remark: the infix commands above ensure a delaborator is generated for each relations.
  We redefine the macros below to be able to use the auxiliary `binop%` elaboration helper for binary operators.
  It addresses issue #382. -/
macro_rules | `($x ||| $y) => `(binop% HOr.hOr $x $y)
macro_rules | `($x ^^^ $y) => `(binop% HXor.hXor $x $y)
macro_rules | `($x &&& $y) => `(binop% HAnd.hAnd $x $y)
macro_rules | `($x + $y)   => `(binop% HAdd.hAdd $x $y)
macro_rules | `($x - $y)   => `(binop% HSub.hSub $x $y)
macro_rules | `($x * $y)   => `(binop% HMul.hMul $x $y)
macro_rules | `($x / $y)   => `(binop% HDiv.hDiv $x $y)
macro_rules | `($x % $y)   => `(binop% HMod.hMod $x $y)
-- exponentiation should be considered a right action (#2854)
macro_rules | `($x ^ $y)   => `(rightact% HPow.hPow $x $y)
macro_rules | `($x ++ $y)  => `(binop% HAppend.hAppend $x $y)
macro_rules | `(- $x)      => `(unop% Neg.neg $x)

-- declare ASCII alternatives first so that the latter Unicode unexpander wins
@[inherit_doc] infix:50 " <= " => LE.le
@[inherit_doc] infix:50 " ≤ "  => LE.le
@[inherit_doc] infix:50 " < "  => LT.lt
@[inherit_doc] infix:50 " >= " => GE.ge
@[inherit_doc] infix:50 " ≥ "  => GE.ge
@[inherit_doc] infix:50 " > "  => GT.gt
@[inherit_doc] infix:50 " = "  => Eq
@[inherit_doc] infix:50 " == " => BEq.beq
/-!
  Remark: the infix commands above ensure a delaborator is generated for each relations.
  We redefine the macros below to be able to use the auxiliary `binrel%` elaboration helper for binary relations.
  It has better support for applying coercions. For example, suppose we have `binrel% Eq n i` where `n : Nat` and
  `i : Int`. The default elaborator fails because we don't have a coercion from `Int` to `Nat`, but
  `binrel%` succeeds because it also tries a coercion from `Nat` to `Int` even when the nat occurs before the int. -/
macro_rules | `($x <= $y) => `(binrel% LE.le $x $y)
macro_rules | `($x ≤ $y)  => `(binrel% LE.le $x $y)
macro_rules | `($x < $y)  => `(binrel% LT.lt $x $y)
macro_rules | `($x > $y)  => `(binrel% GT.gt $x $y)
macro_rules | `($x >= $y) => `(binrel% GE.ge $x $y)
macro_rules | `($x ≥ $y)  => `(binrel% GE.ge $x $y)
macro_rules | `($x = $y)  => `(binrel% Eq $x $y)
macro_rules | `($x == $y) => `(binrel_no_prop% BEq.beq $x $y)

@[inherit_doc] infixr:35 " /\\ " => And
@[inherit_doc] infixr:35 " ∧ "   => And
@[inherit_doc] infixr:30 " \\/ " => Or
@[inherit_doc] infixr:30 " ∨  "  => Or
@[inherit_doc] notation:max "¬" p:40 => Not p

@[inherit_doc] infixl:35 " && " => and
@[inherit_doc] infixl:30 " || " => or
@[inherit_doc] notation:max "!" b:40 => not b

@[inherit_doc] notation:50 a:50 " ∈ " b:50 => Membership.mem b a
/-- `a ∉ b` is negated elementhood. It is notation for `¬ (a ∈ b)`. -/
notation:50 a:50 " ∉ " b:50 => ¬ (a ∈ b)

@[inherit_doc] infixr:67 " :: " => List.cons
@[inherit_doc] infixr:100 " <$> " => Functor.map
@[inherit_doc] infixl:55  " >>= " => Bind.bind
@[inherit_doc HOrElse.hOrElse]   syntax:20 term:21 " <|> " term:20 : term
@[inherit_doc HAndThen.hAndThen] syntax:60 term:61 " >> " term:60 : term
@[inherit_doc Seq.seq]           syntax:60 term:60 " <*> " term:61 : term
@[inherit_doc SeqLeft.seqLeft]   syntax:60 term:60 " <* " term:61 : term
@[inherit_doc SeqRight.seqRight] syntax:60 term:60 " *> " term:61 : term

macro_rules | `($x <|> $y) => `(binop_lazy% HOrElse.hOrElse $x $y)
macro_rules | `($x >> $y)  => `(binop_lazy% HAndThen.hAndThen $x $y)
macro_rules | `($x <*> $y) => `(Seq.seq $x fun _ : Unit => $y)
macro_rules | `($x <* $y)  => `(SeqLeft.seqLeft $x fun _ : Unit => $y)
macro_rules | `($x *> $y)  => `(SeqRight.seqRight $x fun _ : Unit => $y)

namespace Lean

/--
`binderIdent` matches an `ident` or a `_`. It is used for identifiers in binding
position, where `_` means that the value should be left unnamed and inaccessible.
-/
syntax binderIdent := ident <|> hole

namespace Parser.Tactic

/--
A case tag argument has the form `tag x₁ ... xₙ`; it refers to tag `tag` and renames
the last `n` hypotheses to `x₁ ... xₙ`.
-/
syntax caseArg := binderIdent (ppSpace binderIdent)*

end Parser.Tactic
end Lean

@[inherit_doc dite] syntax (name := termDepIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " Lean.binderIdent " : " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if $h:ident : $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; dite $mvar (fun $h:ident => $t) (fun $h:ident => $e))
  | `(if _%$h : $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; dite $mvar (fun _%$h => $t) (fun _%$h => $e))

@[inherit_doc ite] syntax (name := termIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; ite $mvar $t $e)

/--
`if let pat := d then t else e` is a shorthand syntax for:
```
match d with
| pat => t
| _ => e
```
It matches `d` against the pattern `pat` and the bindings are available in `t`.
If the pattern does not match, it returns `e` instead.
-/
syntax (name := termIfLet)
  ppRealGroup(ppRealFill(ppIndent("if " "let " term " := " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if let $pat := $d then $t else $e) =>
    `(match $d:term with | $pat => $t | _ => $e)

@[inherit_doc cond] syntax (name := boolIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("bif " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(bif $c then $t else $e) => `(cond $c $t $e)

/--
Haskell-like pipe operator `<|`. `f <| x` means the same as the same as `f x`,
except that it parses `x` with lower precedence, which means that `f <| g <| x`
is interpreted as `f (g x)` rather than `(f g) x`.
-/
syntax:min term " <| " term:min : term

macro_rules
  | `($f $args* <| $a) => `($f $args* $a)
  | `($f <| $a) => `($f $a)

/--
Haskell-like pipe operator `|>`. `x |> f` means the same as the same as `f x`,
and it chains such that `x |> f |> g` is interpreted as `g (f x)`.
-/
syntax:min term " |> " term:min1 : term

macro_rules
  | `($a |> $f $args*) => `($f $args* $a)
  | `($a |> $f)        => `($f $a)

/--
Alternative syntax for `<|`. `f $ x` means the same as the same as `f x`,
except that it parses `x` with lower precedence, which means that `f $ g $ x`
is interpreted as `f (g x)` rather than `(f g) x`.
-/
-- Note that we have a whitespace after `$` to avoid an ambiguity with antiquotations.
syntax:min term atomic(" $" ws) term:min : term

macro_rules
  | `($f $args* $ $a) => `($f $args* $a)
  | `($f $ $a) => `($f $a)

@[inherit_doc Subtype] syntax "{ " withoutPosition(ident (" : " term)? " // " term) " }" : term

macro_rules
  | `({ $x : $type // $p }) => ``(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => ``(Subtype (fun ($x:ident : _) => $p))

/--
`without_expected_type t` instructs Lean to elaborate `t` without an expected type.
Recall that terms such as `match ... with ...` and `⟨...⟩` will postpone elaboration until
expected type is known. So, `without_expected_type` is not effective in this case.
-/
macro "without_expected_type " x:term : term => `(let aux := $x; aux)

namespace Lean

/--
* The `by_elab doSeq` expression runs the `doSeq` as a `TermElabM Expr` to
  synthesize the expression.
* `by_elab fun expectedType? => do doSeq` receives the expected type (an `Option Expr`)
  as well.
-/
syntax (name := byElab) "by_elab " doSeq : term

/--
Category for carrying raw syntax trees between macros; any content is printed as is by the pretty printer.
The only accepted parser for this category is an antiquotation.
-/
declare_syntax_cat rawStx

instance : Coe Syntax (TSyntax `rawStx) where
  coe stx := ⟨stx⟩

/-- `with_annotate_term stx e` annotates the lexical range of `stx : Syntax` with term info for `e`. -/
scoped syntax (name := withAnnotateTerm) "with_annotate_term " rawStx ppSpace term : term

/-- Normalize casts in an expression using the same method as the `norm_cast` tactic. -/
syntax (name := modCast) "mod_cast " term : term

/--
The attribute `@[deprecated]` on a declaration indicates that the declaration
is discouraged for use in new code, and/or should be migrated away from in
existing code. It may be removed in a future version of the library.

* `@[deprecated myBetterDef]` means that `myBetterDef` is the suggested replacement.
* `@[deprecated myBetterDef "use myBetterDef instead"]` allows customizing the deprecation message.
* `@[deprecated (since := "2024-04-21")]` records when the deprecation was first applied.
-/
syntax (name := deprecated) "deprecated" (ppSpace ident)? (ppSpace str)?
    (" (" &"since" " := " str ")")? : attr

/--
The `@[coe]` attribute on a function (which should also appear in a
`instance : Coe A B := ⟨myFn⟩` declaration) allows the delaborator to show
applications of this function as `↑` when printing expressions.
-/
syntax (name := Attr.coe) "coe" : attr

/--
This attribute marks a code action, which is used to suggest new tactics or replace existing ones.

* `@[command_code_action kind]`: This is a code action which applies to applications of the command
  `kind` (a command syntax kind), which can replace the command or insert things before or after it.

* `@[command_code_action kind₁ kind₂]`: shorthand for
  `@[command_code_action kind₁, command_code_action kind₂]`.

* `@[command_code_action]`: This is a command code action that applies to all commands.
  Use sparingly.
-/
syntax (name := command_code_action) "command_code_action" (ppSpace ident)* : attr

/--
Builtin command code action. See `command_code_action`.
-/
syntax (name := builtin_command_code_action) "builtin_command_code_action" (ppSpace ident)* : attr

/--
When `parent_dir` contains the current Lean file, `include_str "path" / "to" / "file"` becomes
a string literal with the contents of the file at `"parent_dir" / "path" / "to" / "file"`. If this
file cannot be read, elaboration fails.
-/
syntax (name := includeStr) "include_str " term : term

/--
The `run_cmd doSeq` command executes code in `CommandElabM Unit`.
This is the same as `#eval show CommandElabM Unit from discard do doSeq`.
-/
syntax (name := runCmd) "run_cmd " doSeq : command

/--
The `run_elab doSeq` command executes code in `TermElabM Unit`.
This is the same as `#eval show TermElabM Unit from discard do doSeq`.
-/
syntax (name := runElab) "run_elab " doSeq : command

/--
The `run_meta doSeq` command executes code in `MetaM Unit`.
This is the same as `#eval show MetaM Unit from do discard doSeq`.

(This is effectively a synonym for `run_elab` since `MetaM` lifts to `TermElabM`.)
-/
syntax (name := runMeta) "run_meta " doSeq : command

set_option linter.missingDocs false in
syntax guardMsgsFilterSeverity := &"info" <|> &"warning" <|> &"error" <|> &"all"

/--
`#reduce <expression>` reduces the expression `<expression>` to its normal form. This
involves applying reduction rules until no further reduction is possible.

By default, proofs and types within the expression are not reduced. Use modifiers
`(proofs := true)`  and `(types := true)` to reduce them.
Recall that propositions are types in Lean.

**Warning:** This can be a computationally expensive operation,
especially for complex expressions.

Consider using `#eval <expression>` for simple evaluation/execution
of expressions.
-/
syntax (name := reduceCmd) "#reduce " (atomic("(" &"proofs" " := " &"true" ")"))? (atomic("(" &"types" " := " &"true" ")"))? term : command

/--
A message filter specification for `#guard_msgs`.
- `info`, `warning`, `error`: capture messages with the given severity level.
- `all`: capture all messages (the default).
- `drop info`, `drop warning`, `drop error`: drop messages with the given severity level.
- `drop all`: drop every message.
These filters are processed in left-to-right order.
-/
syntax guardMsgsFilter := &"drop"? guardMsgsFilterSeverity

set_option linter.missingDocs false in
syntax guardMsgsWhitespaceArg := &"exact" <|> &"normalized" <|> &"lax"

/--
Whitespace handling for `#guard_msgs`:
- `whitespace := exact` requires an exact whitespace match.
- `whitespace := normalized` converts all newline characters to a space before matching
  (the default). This allows breaking long lines.
- `whitespace := lax` collapses whitespace to a single space before matching.
In all cases, leading and trailing whitespace is trimmed before matching.
-/
syntax guardMsgsWhitespace := &"whitespace" " := " guardMsgsWhitespaceArg

set_option linter.missingDocs false in
syntax guardMsgsOrderingArg := &"exact" <|> &"sorted"

/--
Message ordering for `#guard_msgs`:
- `ordering := exact` uses the exact ordering of the messages (the default).
- `ordering := sorted` sorts the messages in lexicographic order.
  This helps with testing commands that are non-deterministic in their ordering.
-/
syntax guardMsgsOrdering := &"ordering" " := " guardMsgsOrderingArg

set_option linter.missingDocs false in
syntax guardMsgsSpecElt := guardMsgsFilter <|> guardMsgsWhitespace <|> guardMsgsOrdering

set_option linter.missingDocs false in
syntax guardMsgsSpec := "(" guardMsgsSpecElt,* ")"

/--
`/-- ... -/ #guard_msgs in cmd` captures the messages generated by the command `cmd`
and checks that they match the contents of the docstring.

Basic example:
```lean
/--
error: unknown identifier 'x'
-/
#guard_msgs in
example : α := x
```
This checks that there is such an error and then consumes the message.

By default, the command captures all messages, but the filter condition can be adjusted.
For example, we can select only warnings:
```lean
/--
warning: declaration uses 'sorry'
-/
#guard_msgs(warning) in
example : α := sorry
```
or only errors
```lean
#guard_msgs(error) in
example : α := sorry
```
In the previous example, since warnings are not captured there is a warning on `sorry`.
We can drop the warning completely with
```lean
#guard_msgs(error, drop warning) in
example : α := sorry
```

In general, `#guard_msgs` accepts a comma-separated list of configuration clauses in parentheses:
```
#guard_msgs (configElt,*) in cmd
```
By default, the configuration list is `(all, whitespace := normalized, ordering := exact)`.

Message filters (processed in left-to-right order):
- `info`, `warning`, `error`: capture messages with the given severity level.
- `all`: capture all messages (the default).
- `drop info`, `drop warning`, `drop error`: drop messages with the given severity level.
- `drop all`: drop every message.

Whitespace handling (after trimming leading and trailing whitespace):
- `whitespace := exact` requires an exact whitespace match.
- `whitespace := normalized` converts all newline characters to a space before matching
  (the default). This allows breaking long lines.
- `whitespace := lax` collapses whitespace to a single space before matching.

Message ordering:
- `ordering := exact` uses the exact ordering of the messages (the default).
- `ordering := sorted` sorts the messages in lexicographic order.
  This helps with testing commands that are non-deterministic in their ordering.

For example, `#guard_msgs (error, drop all) in cmd` means to check warnings and drop
everything else.

The command elaborator has special support for `#guard_msgs` for linting.
The `#guard_msgs` itself wants to capture linter warnings,
so it elaborates the command it is attached to as if it were a top-level command.
However, the command elaborator runs linters for *all* top-level commands,
which would include `#guard_msgs` itself, and would cause duplicate and/or uncaptured linter warnings.
The top-level command elaborator only runs the linters if `#guard_msgs` is not present.
-/
syntax (name := guardMsgsCmd)
  (docComment)? "#guard_msgs" (ppSpace guardMsgsSpec)? " in" ppLine command : command

namespace Parser

/--
`#check_tactic t ~> r by commands` runs the tactic sequence `commands`
on a goal with `t` and sees if the resulting expression has reduced it
to `r`.
-/
syntax (name := checkTactic) "#check_tactic " term "~>" term "by" tactic : command

/--
`#check_tactic_failure t by tac` runs the tactic `tac`
on a goal with `t` and verifies it fails.
-/
syntax  (name := checkTacticFailure) "#check_tactic_failure " term "by" tactic : command

/--
`#check_simp t ~> r` checks `simp` reduces `t` to `r`.
-/
syntax (name := checkSimp) "#check_simp " term "~>" term : command

/--
`#check_simp t !~>` checks `simp` fails on reducing `t`.
-/
syntax (name := checkSimpFailure) "#check_simp " term "!~>" : command

/--
Time the elaboration of a command, and print the result (in milliseconds).

Example usage:
```
set_option maxRecDepth 100000 in
#time example : (List.range 500).length = 500 := rfl
```
-/
syntax (name := timeCmd) "#time " command : command

/--
`#discr_tree_key  t` prints the discrimination tree keys for a term `t` (or, if it is a single identifier, the type of that constant).
It uses the default configuration for generating keys.

For example,
```
#discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
-- bar _ (@OfNat.ofNat Nat _ _)

#discr_tree_simp_key Nat.add_assoc
-- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
```

`#discr_tree_simp_key` is similar to `#discr_tree_key`, but treats the underlying type
as one of a simp lemma, i.e. transforms it into an equality and produces the key of the
left-hand side.
-/
syntax (name := discrTreeKeyCmd) "#discr_tree_key " term : command

@[inherit_doc discrTreeKeyCmd]
syntax (name := discrTreeSimpKeyCmd) "#discr_tree_simp_key" term : command

/--
The `seal foo` command ensures that the definition of `foo` is sealed, meaning it is marked as `[irreducible]`.
This command is particularly useful in contexts where you want to prevent the reduction of `foo` in proofs.

In terms of functionality, `seal foo` is equivalent to `attribute [local irreducible] foo`.
This attribute specifies that `foo` should be treated as irreducible only within the local scope,
which helps in maintaining the desired abstraction level without affecting global settings.
-/
syntax "seal " (ppSpace ident)+ : command

/--
The `unseal foo` command ensures that the definition of `foo` is unsealed, meaning it is marked as `[semireducible]`, the
default reducibility setting. This command is useful when you need to allow some level of reduction of `foo` in proofs.

Functionally, `unseal foo` is equivalent to `attribute [local semireducible] foo`.
Applying this attribute makes `foo` semireducible only within the local scope.
-/
syntax "unseal " (ppSpace ident)+ : command

macro_rules
  | `(seal $fs:ident*) => `(attribute [local irreducible] $fs:ident*)
  | `(unseal $fs:ident*) => `(attribute [local semireducible] $fs:ident*)

end Parser
