open Lean PrettyPrinter

namespace ns
inductive Foo | mk: Foo

@[app_unexpander Foo.mk]
def unexpadFoo : Lean.PrettyPrinter.Unexpander | `($x) => `(unexpand)

def foo := Foo.mk
#print foo

@[app_unexpander ns.Foo.mk]
def unexpadFoo' : Lean.PrettyPrinter.Unexpander | `($x) => `(unexpand)
def bar := ns.Foo.mk

#print bar
end ns
