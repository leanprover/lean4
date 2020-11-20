# Namespaces

Lean provides us with the ability to group definitions into nested, hierarchical *namespaces*:

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

When we declare that we are working in the namespace ``Foo``, every identifier we declare has
a full name with prefix "``Foo.``" Within the namespace, we can refer to identifiers
by their shorter names, but once we end the namespace, we have to use the longer names.

The ``open`` command brings the shorter names into the current context. Often, when we import a
module, we will want to open one or more of the namespaces it contains, to have access to the short identifiers.
But sometimes we will want to leave this information hidden, for example, when they conflict with
identifiers in another namespace we want to use. Thus namespaces give us a way to manage our working environment.

For example, Lean groups definitions and theorems involving lists into a namespace ``List``.
```lean
#check List.nil
#check List.cons
#check List.map
```
We will discuss their types, below. The command ``open List`` allows us to use the shorter names:
```lean
open List

#check nil
#check cons
#check map
```
Like sections, namespaces can be nested:
```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```
Namespaces that have been closed can later be reopened, even in another file:
```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

Like sections, nested namespaces have to be closed in the order they are opened.
Namespaces and sections serve different purposes: namespaces organize data and sections declare variables for insertion in definitions.
Sections are also useful for delimiting the scope of commands such as ``set_option`` and ``open``.

In many respects, however, a ``namespace ... end`` block behaves the same as a ``section ... end`` block.
In particular, if you use the ``variable`` command within a namespace, its scope is limited to the namespace.
Similarly, if you use an ``open`` command within a namespace, its effects disappear when the namespace is closed.
