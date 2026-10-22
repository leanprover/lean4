module

public import Lean

/-! Deprecations and undecorated APIs provided by the dependency. -/

public section

namespace Dep

@[deprecated "old dependency name" (since := "2000-01-02")]
def old : Nat := 1

@[deprecated_arg old new (since := "2000-01-02")]
def renamed (new : Nat) : Nat := new

def upstreamFunction (new : Nat) : Nat := new

syntax (name := oldTerm) "dep_old_term" : term
macro_rules | `(dep_old_term) => `(1)
deprecated_syntax oldTerm "old dependency syntax" (since := "2000-01-02")

syntax (name := upstreamTerm) "upstream_term" : term
macro_rules | `(upstream_term) => `(1)

end Dep

@[deprecated "old dependency option" (since := "2000-01-02")]
meta register_option Dep.oldOption : Bool := { defValue := false }
