## Implicit Arguments

Suppose we define the `compose` function as.

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

The function `compose` takes three types, ``α``, ``β``, and ``γ``, and two functions, ``g : β → γ`` and ``f : α → β``, a value `x : α`, and
returns ``g (f x)``, the composition of ``g`` and ``f``.
We say `compose` is polymorphic over types ``α``, ``β``, and ``γ``. Now, let's use `compose`:

```lean
# def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
#   g (f x)
def double (x : Nat) := 2*x
def triple (x : Nat) := 3*x

#check compose Nat Nat Nat double triple 10 -- Nat
#eval  compose Nat Nat Nat double triple 10 -- 60

def appendWorld (s : String) := s ++ "world"
#check String.length -- String → Nat

#check compose String String Nat String.length appendWorld "hello" -- Nat
#eval  compose String String Nat String.length appendWorld "hello" -- 10
```

Because `compose` is polymorphic over types ``α``, ``β``, and ``γ``, we have to provide them in the examples above.
But this information is redundant: one can infer the types from the arguments ``g`` and ``f``.
This is a central feature of dependent type theory: terms carry a lot of information, and often some of that information can be inferred from the context.
In Lean, one uses an underscore, ``_``, to specify that the system should fill in the information automatically.

```lean
# def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
#  g (f x)
# def double (x : Nat) := 2*x
# def triple (x : Nat) := 3*x
#check compose _ _ _ double triple 10 -- Nat
#eval  compose Nat Nat Nat double triple 10 -- 60
# def appendWorld (s : String) := s ++ "world"
# #check String.length -- String → Nat
#check compose _ _ _ String.length appendWorld "hello" -- Nat
#eval  compose _ _ _ String.length appendWorld "hello" -- 10
```
It is still tedious, however, to type all these underscores. When a function takes an argument that can generally be inferred from context,
Lean allows us to specify that this argument should, by default, be left implicit. This is done by putting the arguments in curly braces, as follows:

```lean
def compose {α β γ : Type} (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
# def double (x : Nat) := 2*x
# def triple (x : Nat) := 3*x
#check compose double triple 10 -- Nat
#eval  compose double triple 10 -- 60
# def appendWorld (s : String) := s ++ "world"
# #check String.length -- String → Nat
#check compose String.length appendWorld "hello" -- Nat
#eval  compose String.length appendWorld "hello" -- 10
```
All that has changed are the braces around ``α β γ: Type``.
It makes these three arguments implicit. Notationally, this hides the specification of the type,
making it look as though ``compose`` simply takes 3 arguments.

Variables can also be specified as implicit when they are declared with
the ``variables`` command:

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

variable (α β : Type u)
variable (a : α) (b : β)

#check ident
#check ident a
#check ident b
```

This definition of ``ident`` here has the same effect as the one above.

Lean has very complex mechanisms for instantiating implicit arguments, and we will see that they can be used to infer function types, predicates, and even proofs.
The process of instantiating these "holes," or "placeholders," in a term is part of a bigger process called *elaboration*.
The presence of implicit arguments means that at times there may be insufficient information to fix the meaning of an expression precisely.
An expression like ``ident`` is said to be *polymorphic*, because it can take on different meanings in different contexts.

One can always specify the type ``T`` of an expression ``e`` by writing ``(e : T)``.
This instructs Lean's elaborator to use the value ``T`` as the type of ``e`` when trying to elaborate it.
In the following example, this mechanism is used to specify the desired types of the expressions ``ident``.

```lean
def ident {α : Type u} (a : α) : α := a

#check (ident : Nat → Nat) -- Nat → Nat
```

Numerals are overloaded in Lean, but when the type of a numeral cannot be inferred, Lean assumes, by default, that it is a natural number.
So the expressions in the first two ``#check`` commands below are elaborated in the same way, whereas the third ``#check`` command interprets ``2`` as an integer.

```lean
#check 2         -- Nat
#check (2 : Nat) -- Nat
#check (2 : Int) -- Int
```

Sometimes, however, we may find ourselves in a situation where we have declared an argument to a function to be implicit,
but now want to provide the argument explicitly. If ``foo`` is such a function, the notation ``@foo`` denotes the same function with all
the arguments made explicit.

```lean
# def ident {α : Type u} (a : α) : α := a
variable (α β : Type)

#check @ident           -- {α : Type u} → α → α
#check @ident α         -- α → α
#check @ident β         -- β → β
#check @ident Nat       -- Nat → Nat
#check @ident Bool true -- Bool
```

Notice that now the first ``#check`` command gives the type of the identifier, ``ident``, without inserting any placeholders.
Moreover, the output indicates that the first argument is implicit.

Named arguments enable you to specify an argument for a parameter by matching the argument with
its name rather than with its position in the parameter list. You can use them to specify explicit *and* implicit arguments.
If you don't remember the order of the parameters but know their names, you can send the arguments in any order.
You may also provide the value for an implicit parameter when
Lean failed to infer it. Named arguments also improve the readability of your code by identifying what
each argument represents.

```lean
# def ident {α : Type u} (a : α) : α := a

#check ident (α := Nat)  -- Nat → Nat
#check ident (α := Bool) -- Bool → Bool
```
