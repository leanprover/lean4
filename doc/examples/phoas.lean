/-!
# Parametric Higher-Order Abstract Syntax

In contrast to first-order encodings, higher-order encodings avoid explicit modeling of variable identity.
Instead, the binding constructs of an object language (the language being
formalized) can be represented using the binding constructs of the meta language (the language in which the formalization is done).
The best known higher-order encoding is called higher-order abstract syntax (HOAS),
and we can start by attempting to apply it directly in Lean.

Remark: this example is based on an example in the book [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) by Adam Chlipala.
-/

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
With HOAS, each object language binding construct is represented with a function of
the meta language. Here is what we get if we apply that idea within an inductive definition
of term syntax. However a naive encondig in Lean fails to meet the strict positivity restrictions
imposed by the Lean kernel. An alternate higher-order encoding is parametric HOAS, as introduced by Washburn
and Weirich for Haskell and tweaked by Adam Chlipala for use in Coq. The key idea is to parameterize the
declaration by a type family `rep` standing for a "representation of variables."
-/
inductive Term' (rep : Ty → Type) : Ty → Type
  | var   : rep ty → Term' rep ty
  | const : Nat → Term' rep .nat
  | plus  : Term' rep .nat → Term' rep .nat → Term' rep .nat
  | lam   : (rep dom → Term' rep ran) → Term' rep (.fn dom ran)
  | app   : Term' rep (.fn dom ran) → Term' rep dom → Term' rep ran
  | let   : Term' rep ty₁ → (rep ty₁ → Term' rep ty₂) → Term' rep ty₂

/-!
Lean accepts this definition because our embedded functions now merely take variables as
arguments, instead of arbitrary terms. One might wonder whether there is an easy loophole
to exploit here, instantiating the parameter `rep` as term itself. However, to do that, we
would need to choose a variable representation for this nested mention of term, and so on
through an infinite descent into term arguments.

We write the final type of a closed term using polymorphic quantification over all possible
choices of `rep` type family
-/

open Ty (nat fn)

namespace FirstTry

def Term (ty : Ty) := (rep : Ty → Type) → Term' rep ty

/-!
In the next two example, note how each is written as a function over a `rep` choice,
such that the specific choice has no impact on the structure of the term.
-/
def add : Term (fn nat (fn nat nat)) := fun _rep =>
  .lam fun x => .lam fun y => .plus (.var x) (.var y)

def three_the_hard_way : Term nat := fun rep =>
  .app (.app (add rep) (.const 1)) (.const 2)

end FirstTry

/-!
The argument `rep` does not even appear in the function body for `add`. How can that be?
By giving our terms expressive types, we allow Lean to infer many arguments for us. In fact,
we do not even need to name the `rep` argument! By using Lean implicit arguments and lambdas,
we can completely hide `rep` in these examples.
-/

def Term (ty : Ty) := {rep : Ty → Type} → Term' rep ty

def add : Term (fn nat (fn nat nat)) :=
  .lam fun x => .lam fun y => .plus (.var x) (.var y)

def three_the_hard_way : Term nat :=
  .app (.app add (.const 1)) (.const 2)

/-!
It may not be at all obvious that the PHOAS representation admits the crucial computable
operations. The key to effective deconstruction of PHOAS terms is one principle: treat
the `rep` parameter as an unconstrained choice of which data should be annotated on each
variable. We will begin with a simple example, that of counting how many variable nodes
appear in a PHOAS term. This operation requires no data annotated on variables, so we
simply annotate variables with `Unit` values. Note that, when we go under binders in the
cases for `lam` and `let`, we must provide the data value to annotate on the new variable we
pass beneath. For our current choice of `Unit` data, we always pass `()`.
-/

def countVars : Term' (fun _ => Unit) ty → Nat
  | .var _    => 1
  | .const _  => 0
  | .plus a b => countVars a + countVars b
  | .app f a  => countVars f + countVars a
  | .lam b    => countVars (b ())
  | .let a b  => countVars a + countVars (b ())

/-! We can now easily prove that `add` has two variables by using reflexivity -/

example : countVars add = 2 :=
  rfl

/-!
Here is another example, translating PHOAS terms into strings giving a first-order rendering.
To implement this translation, the key insight is to tag variables with strings, giving their names.
The function takes as an additional input `i` which is used to create variable names for binders.
We also use the string interpolation available in Lean. For example, `s!"x_{i}"` is expanded to
`"x_" ++ toString i`.
-/
def pretty (e : Term' (fun _ => String) ty) (i : Nat := 1) : String :=
  match e with
  | .var s     => s
  | .const n   => toString n
  | .app f a   => s!"({pretty f i} {pretty a i})"
  | .plus a b  => s!"({pretty a i} + {pretty b i})"
  | .lam f     =>
    let x := s!"x_{i}"
    s!"(fun {x} => {pretty (f x) (i+1)})"
  | .let a b  =>
    let x := s!"x_{i}"
    s!"(let {x} := {pretty a i}; => {pretty (b x) (i+1)}"

#eval pretty three_the_hard_way

/-!
It is not necessary to convert to a different representation to support many common
operations on terms. For instance, we can implement substitution of terms for variables.
The key insight here is to tag variables with terms, so that, on encountering a variable, we
can simply replace it by the term in its tag. We will call this function initially on a term
with exactly one free variable, tagged with the appropriate substitute. During recursion,
new variables are added, but they are only tagged with their own term equivalents. Note
that this function squash is parameterized over a specific `rep` choice.
-/
def squash : Term' (Term' rep) ty → Term' rep ty
 | .var e    => e
 | .const n  => .const n
 | .plus a b => .plus (squash a) (squash b)
 | .lam f    => .lam fun x => squash (f (.var x))
 | .app f a  => .app (squash f) (squash a)
 | .let a b  => .let (squash a) fun x => squash (b (.var x))

/-!
To define the final substitution function over terms with single free variables, we define
`Term1`, an analogue to Term that we defined before for closed terms.
-/
def Term1 (ty1 ty2 : Ty) := {rep : Ty → Type} → rep ty1 → Term' rep ty2

/-!
Substitution is defined by (1) instantiating a `Term1` to tag variables with terms and (2)
applying the result to a specific term to be substituted. Note how the parameter `rep` of
`squash` is instantiated: the body of `subst` is itself a polymorphic quantification over `rep`,
standing for a variable tag choice in the output term; and we use that input to compute a
tag choice for the input term.
-/

def subst (e : Term1 ty1 ty2) (e' : Term ty1) : Term ty2 :=
  squash (e e')

/-!
We can view `Term1` as a term with hole. In the following example,
`(fun x => plus (var x) (const 5))` can be viewed as the term `plus _ (const 5)` where
the hole `_` is instantiated by `subst` with `three_the_hard_way`
-/

#eval pretty <| subst (fun x => .plus (.var x) (.const 5)) three_the_hard_way

/-!
One further development, which may seem surprising at first,
is that we can also implement a usual term denotation function,
when we tag variables with their denotations.

The attribute `[simp]` instructs Lean to always try to unfold `denote` applications when one applies
the `simp` tactic. We also say this is a hint for the Lean term simplifier.
-/
@[simp] def denote : Term' Ty.denote ty → ty.denote
  | .var x    => x
  | .const n  => n
  | .plus a b => denote a + denote b
  | .app f a  => denote f (denote a)
  | .lam f    => fun x => denote (f x)
  | .let a b  => denote (b (denote a))

example : denote three_the_hard_way = 3 :=
  rfl

/-!
To summarize, the PHOAS representation has all the expressive power of more
standard encodings (e.g., using de Bruijn indices), and a variety of translations are actually much more pleasant to
implement than usual, thanks to the novel ability to tag variables with data.
-/

/-!
We now define the constant folding optimization that traverses a term if replaces subterms such as
`plus (const m) (const n)` with `const (n+m)`.
-/
@[simp] def constFold : Term' rep ty → Term' rep ty
  | .var x    => .var x
  | .const n  => .const n
  | .app f a  => .app (constFold f) (constFold a)
  | .lam f    => .lam fun x => constFold (f x)
  | .let a b  => .let (constFold a) fun x => constFold (b x)
  | .plus a b =>
    match constFold a, constFold b with
    | .const n, .const m => .const (n+m)
    | a',       b'       => .plus a' b'

/-!
The correctness of the `constFold` is proved using induction, case-analysis, and the term simplifier.
We prove all cases but the one for `plus` using `simp [*]`. This tactic instructs the term simplifier to
use hypotheses such as `a = b` as rewriting/simplications rules.
We use the `split` to break the nested `match` expression in the `plus` case into two cases.
The local variables `iha` and `ihb` are the induction hypotheses for `a` and `b`.
The modifier `←` in a term simplifier argument instructs the term simplifier to use the equation as a rewriting rule in
the "reverse direction. That is, given `h : a = b`, `← h` instructs the term simplifier to rewrite `b` subterms to `a`.
-/
theorem constFold_sound (e : Term' Ty.denote ty) : denote (constFold e) = denote e := by
  induction e with simp [*]
  | plus a b iha ihb =>
    split
    next he₁ he₂ => simp [← iha, ← ihb, he₁, he₂]
    next => simp [iha, ihb]
