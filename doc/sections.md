# Variables and Sections

Consider the following three function definitions:
```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

Lean provides us with the ``variable`` command to make such declarations look more compact:

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```
We can declare variables of any type, not just ``Type`` itself:
```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```
Printing them out shows that all three groups of definitions have exactly the same effect.

The ``variable`` command instructs Lean to insert the declared variables as bound variables in definitions that refer to them.
Lean is smart enough to figure out which variables are used explicitly or implicitly in a definition. We can therefore proceed as
though ``α``, ``β``, ``γ``, ``g``, ``f``, ``h``, and ``x`` are fixed objects when we write our definitions, and let Lean abstract
the definitions for us automatically.

When declared in this way, a variable stays in scope until the end of the file we are working on.
Sometimes, however, it is useful to limit the scope of a variable. For that purpose, Lean provides the notion of a ``section``:

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

When the section is closed, the variables go out of scope, and become nothing more than a distant memory.

You do not have to indent the lines within a section. Nor do you have to name a section, which is to say,
you can use an anonymous ``section`` / ``end`` pair.
If you do name a section, however, you have to close it using the same name.
Sections can also be nested, which allows you to declare new variables incrementally.
