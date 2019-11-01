inductive Foo : Type
| mk : Nat → Foo

namespace Foo
def worksInNamespace : Foo → Nat
| mk n => n --works
end Foo

-- The following fails, because `namespace Foo` is not open,
-- despite the `Foo.` prefix in the name.
def Foo.failsWithPrefix : Foo → Nat
| mk n => n -- error: invalid application, function expected

def Foo.worksWithQualifiedName : Foo → Nat
| Foo.mk n => n -- works

/-
This has always (slightly) annoyed me, because
I find that function bodies can be clunky without the open namespace,
while surrounding functions with

namespace Foo
def ...
end Foo

adds a lot of clutter to a file.

Here are the semantics I always seem to expect:

def Foo.f ...

as sugar for

namespace Foo
def f ...
end Foo
-/
