/-!
# Dependent de Bruijn Indices

In this example, we represent program syntax terms in a type family parameterized by a list of types,
representing the typing context, or information on which free variables are in scope and what
their types are.


Remark: this example is based on an example in the book [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) by Adam Chlipala.
-/

/-!
Programmers who move to statically typed functional languages from scripting languages
often complain about the requirement that every element of a list have the same type. With
fancy type systems, we can partially lift this requirement. We can index a list type with a
“type-level” list that explains what type each element of the list should have. This has been
done in a variety of ways in Haskell using type classes, and we can do it much more cleanly
and directly in Lean.

We parameterize our heterogeneous lists by at type `α` and an `α`-indexed type `β`.
-/

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

/-!
We overload the `List.cons` notation `::` so we can also use it to create
heterogeneous lists.
-/
infix:67 " :: " => HList.cons

/-! We similarly overload the `List` notation `[]` for the empty heterogeneous list. -/
notation "[" "]" => HList.nil

/-!
Variables are represented in a way isomorphic to the natural numbers, where
number 0 represents the first element in the context, number 1 the second element, and so
on. Actually, instead of numbers, we use the `Member` inductive family.

The value of type `Member a as` can be viewed as a certificate that `a` is
an element of the list `as`. The constructor `Member.head` says that `a`
is in the list if the list begins with it. The constructor `Member.tail`
says that if `a` is in the list `bs`, it is also in the list `b::bs`.
-/
inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

/-!
Given a heterogeneous list `HList β is` and value of type `Member i is`, `HList.get`
retrieves an element of type `β i` from the list.
The pattern `.head` and `.tail h` are sugar for `Member.head` and `Member.tail h` respectively.
Lean can infer the namespace using the expected type.
-/
def HList.get : HList β is → Member i is → β i
  | a::as, .head => a
  | a::as, .tail h => as.get h

/-!
Here is the definition of the simple type system for our programming language, a simply typed
lambda calculus with natural numbers as the base type.
-/
inductive Ty where
  | nat
  | fn : Ty → Ty → Ty

/-!
We can write a function to translate `Ty` values to a Lean type
— remember that types are first class, so can be calculated just like any other value.
We mark `Ty.denote` as `[reducible]` to make sure the typeclass resolution procedure can
unfold/reduce it. For example, suppose Lean is trying to synthesize a value for the instance
`Add (Ty.denote Ty.nat)`. Since `Ty.denote` is marked as `[reducible]`,
the typeclass resolution procedure can reduce `Ty.denote Ty.nat` to `Nat`, and use
the builtin instance for `Add Nat` as the solution.

Recall that the term `a.denote` is sugar for `denote a` where `denote` is the function being defined.
We call it the "dot notation".
-/
@[reducible] def Ty.denote : Ty → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote

/-!
Here is the definition of the `Term` type, including variables, constants, addition,
function application and abstraction, and let binding of local variables.
Since `let` is a keyword in Lean, we use the "escaped identifier" `«let»`.
You can input the unicode (French double quotes) using `\f<<` (for `«`) and `\f>>` (for `»`).
The term `Term ctx .nat` is sugar for `Term ctx Ty.nat`, Lean infers the namespace using the expected type.
-/
inductive Term : List Ty → Ty → Type
  | var   : Member ty ctx → Term ctx ty
  | const : Nat → Term ctx .nat
  | plus  : Term ctx .nat → Term ctx .nat → Term ctx .nat
  | app   : Term ctx (.fn dom ran) → Term ctx dom → Term ctx ran
  | lam   : Term (dom :: ctx) ran → Term ctx (.fn dom ran)
  | «let» : Term ctx ty₁ → Term (ty₁ :: ctx) ty₂ → Term ctx ty₂

/-!
Here are two example terms encoding, the first addition packaged as a two-argument
curried function, and the second of a sample application of addition to constants.

The command `open Ty Term Member` opens the namespaces `Ty`, `Term`, and `Member`. Thus,
you can write `lam` instead of `Term.lam`.
-/
open Ty Term Member
def add : Term [] (fn nat (fn nat nat)) :=
  lam (lam (plus (var (tail head)) (var head)))

def three_the_hard_way : Term [] nat :=
  app (app add (const 1)) (const 2)

/-!
Since dependent typing ensures that any term is well-formed in its context and has a particular type,
it is easy to translate syntactic terms into Lean values.

The attribute `[simp]` instructs Lean to always try to unfold `Term.denote` applications when one applies
the `simp` tactic. We also say this is a hint for the Lean term simplifier.
-/
@[simp] def Term.denote : Term ctx ty → HList Ty.denote ctx → ty.denote
  | var h,     env => env.get h
  | const n,   _   => n
  | plus a b,  env => a.denote env + b.denote env
  | app f a,   env => f.denote env (a.denote env)
  | lam b,     env => fun x => b.denote (x :: env)
  | «let» a b, env => b.denote (a.denote env :: env)

/-!
You can show that the denotation of `three_the_hard_way` is indeed `3` using reflexivity.
-/
example : three_the_hard_way.denote [] = 3 :=
  rfl

/-!
We now define the constant folding optimization that traverses a term if replaces subterms such as
`plus (const m) (const n)` with `const (n+m)`.
-/
@[simp] def Term.constFold : Term ctx ty → Term ctx ty
  | const n   => const n
  | var h     => var h
  | app f a   => app f.constFold a.constFold
  | lam b     => lam b.constFold
  | «let» a b => «let» a.constFold b.constFold
  | plus a b  =>
    match a.constFold, b.constFold with
    | const n, const m => const (n+m)
    | a',      b'      => plus a' b'

/-!
The correctness of the `Term.constFold` is proved using induction, case-analysis, and the term simplifier.
We prove all cases but the one for `plus` using `simp [*]`. This tactic instructs the term simplifier to
use hypotheses such as `a = b` as rewriting/simplications rules.
We use the `split` to break the nested `match` expression in the `plus` case into two cases.
The local variables `iha` and `ihb` are the induction hypotheses for `a` and `b`.
The modifier `←` in a term simplifier argument instructs the term simplifier to use the equation as a rewriting rule in
the "reverse direction". That is, given `h : a = b`, `← h` instructs the term simplifier to rewrite `b` subterms to `a`.
-/
theorem Term.constFold_sound (e : Term ctx ty) : e.constFold.denote env = e.denote env := by
  induction e with simp [*]
  | plus a b iha ihb =>
    split
    next he₁ he₂ => simp [← iha, ← ihb, he₁, he₂]
    next => simp [iha, ihb]
