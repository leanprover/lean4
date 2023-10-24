/-!
# The Well-Typed Interpreter

In this example, we build an interpreter for a simple functional programming language,
with variables, function application, binary operators and an `if...then...else` construct.
We will use the dependent type system to ensure that any programs which can be represented are well-typed.

Remark: this example is based on an example found in the Idris manual.
-/

/-!
Vectors
--------

A `Vector` is a list of size `n` whose elements belong to a type `α`.
-/

inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

/-!
We can overload the `List.cons` notation `::` and use it to create `Vector`s.
-/
infix:67 " :: " => Vector.cons

/-!
Now, we define the types of our simple functional language.
We have integers, booleans, and functions, represented by `Ty`.
-/
inductive Ty where
  | int
  | bool
  | fn (a r : Ty)

/-!
We can write a function to translate `Ty` values to a Lean type
— remember that types are first class, so can be calculated just like any other value.
We mark `Ty.interp` as `[reducible]` to make sure the typeclass resolution procedure can
unfold/reduce it. For example, suppose Lean is trying to synthesize a value for the instance
`Add (Ty.interp Ty.int)`. Since `Ty.interp` is marked as `[reducible]`,
the typeclass resolution procedure can reduce `Ty.interp Ty.int` to `Int`, and use
the builtin instance for `Add Int` as the solution.
-/
@[reducible] def Ty.interp : Ty → Type
  | int    => Int
  | bool   => Bool
  | fn a r => a.interp → r.interp

/-!
Expressions are indexed by the types of the local variables, and the type of the expression itself.
-/
inductive HasType : Fin n → Vector Ty n → Ty → Type where
  | stop : HasType 0 (ty :: ctx) ty
  | pop  : HasType k ctx ty → HasType k.succ (u :: ctx) ty

inductive Expr : Vector Ty n → Ty → Type where
  | var   : HasType i ctx ty → Expr ctx ty
  | val   : Int → Expr ctx Ty.int
  | lam   : Expr (a :: ctx) ty → Expr ctx (Ty.fn a ty)
  | app   : Expr ctx (Ty.fn a ty) → Expr ctx a → Expr ctx ty
  | op    : (a.interp → b.interp → c.interp) → Expr ctx a → Expr ctx b → Expr ctx c
  | ife   : Expr ctx Ty.bool → Expr ctx a → Expr ctx a → Expr ctx a
  | delay : (Unit → Expr ctx a) → Expr ctx a

/-!
We use the command `open` to create the aliases `stop` and `pop` for `HasType.stop` and `HasType.pop` respectively.
-/
open HasType (stop pop)

/-!
Since expressions are indexed by their type, we can read the typing rules of the language from the definitions of the constructors.
Let us look at each constructor in turn.

We use a nameless representation for variables — they are de Bruijn indexed.
Variables are represented by a proof of their membership in the context, `HasType i ctx ty`,
which is a proof that variable `i` in context `ctx` has type `ty`.

We can treat `stop` as a proof that the most recently defined variable is well-typed,
and `pop n` as a proof that, if the `n`th most recently defined variable is well-typed, so is the `n+1`th.
In practice, this means we use `stop` to refer to the most recently defined variable,
`pop stop` to refer to the next, and so on, via the `Expr.var` constructor.

A value `Expr.val` carries a concrete representation of an integer.

A lambda `Expr.lam` creates a function. In the scope of a function of type `Ty.fn a ty`, there is a
new local variable of type `a`.

A function application `Expr.app` produces a value of type `ty` given a function from `a` to `ty` and a value of type `a`.

The constructor `Expr.op` allows us to use arbitrary binary operators, where the type of the operator informs what the types of the arguments must be.

Finally, the constructor `Exp.ife` represents a `if-then-else` expression. The condition is a Boolean, and each branch must have the same type.

The auxiliary constructor `Expr.delay` is used to delay evaluation.
-/


/-!
When we evaluate an `Expr`, we’ll need to know the values in scope, as well as their types. `Env` is an environment,
indexed over the types in scope. Since an environment is just another form of list, albeit with a strongly specified connection
to the vector of local variable types, we overload again the notation `::` so that we can use the usual list syntax.
Given a proof that a variable is defined in the context, we can then produce a value from the environment.
-/
inductive Env : Vector Ty n → Type where
  | nil  : Env Vector.nil
  | cons : Ty.interp a → Env ctx → Env (a :: ctx)

infix:67 " :: " => Env.cons

def Env.lookup : HasType i ctx ty → Env ctx → ty.interp
  | stop,  x :: xs => x
  | pop k, x :: xs => lookup k xs

/-!
Given this, an interpreter is a function which translates an `Expr` into a Lean value with respect to a specific environment.
-/
def Expr.interp (env : Env ctx) : Expr ctx ty → ty.interp
  | var i     => env.lookup i
  | val x     => x
  | lam b     => fun x => b.interp (Env.cons x env)
  | app f a   => f.interp env (a.interp env)
  | op o x y  => o (x.interp env) (y.interp env)
  | ife c t e => if c.interp env then t.interp env else e.interp env
  | delay a   => (a ()).interp env

open Expr

/-!
We can make some simple test functions. Firstly, adding two inputs `fun x y => y + x` is written as follows.
-/

def add : Expr ctx (Ty.fn Ty.int (Ty.fn Ty.int Ty.int)) :=
  lam (lam (op (·+·) (var stop) (var (pop stop))))

#eval add.interp Env.nil 10 20

/-!
More interestingly, a factorial function fact (e.g. `fun x => if (x == 0) then 1 else (fact (x-1) * x)`), can be written as.
Note that this is a recursive (non-terminating) definition. For every input value, the interpreter terminates, but the
definition itself is non-terminating. We use two tricks to make sure Lean accepts it. First, we use the auxiliary constructor
`Expr.delay` to delay its unfolding. Second, we add the annotation `decreasing_by sorry` which can be viewed as
"trust me, this recursive definition makes sense". Recall that `sorry` is an unsound axiom in Lean.
-/

def fact : Expr ctx (Ty.fn Ty.int Ty.int) :=
  lam (ife (op (·==·) (var stop) (val 0))
           (val 1)
           (op (·*·) (delay fun _ => app fact (op (·-·) (var stop) (val 1))) (var stop)))
  decreasing_by sorry

#eval fact.interp Env.nil 10
