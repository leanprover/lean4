module

import Consumer.Own

/-! Imported modules from the current package warn independently of dependencies. -/

set_option linter.deprecated true
set_option linter.deprecated.syntax true

#guard_msgs in
example : Nat := Dep.old

#guard_msgs in
example : Nat := Dep.renamed (old := 1)

#guard_msgs in
example : Nat := dep_old_term

#guard_msgs in
macro "consumer_quote" : term => ``(dep_old_term)

#guard_msgs in
set_option Dep.oldOption true

#guard_msgs in
example := set_option Dep.oldOption true in 1

/-- warning: `ownOld` has been deprecated: old local name -/
#guard_msgs in
example : Nat := ownOld

/-- warning: `ownOldOption` has been deprecated: old local option -/
#guard_msgs in
set_option ownOldOption true

/-- warning: syntax 'Dep.upstreamTerm' has been deprecated: locally deprecated syntax -/
#guard_msgs (substring := true) in
example : Nat := upstream_term

/-- warning: parameter `old` of `Dep.upstreamFunction` has been deprecated, use `new` instead -/
#guard_msgs (substring := true) in
example : Nat := Dep.upstreamFunction (old := 1)

set_option deprecation.warnings.local "2000-01-01"
set_option deprecation.warnings "all"

#guard_msgs in
example : Nat := ownOld

#guard_msgs in
example : Nat := upstream_term

#guard_msgs in
example : Nat := Dep.upstreamFunction (old := 1)

#guard_msgs in
set_option ownOldOption true

/-- warning: `Dep.old` has been deprecated: old dependency name -/
#guard_msgs in
example : Nat := Dep.old

/-- warning: syntax 'Dep.oldTerm' has been deprecated: old dependency syntax -/
#guard_msgs (substring := true) in
example : Nat := dep_old_term

/-- warning: quotation uses deprecated syntax 'Dep.oldTerm': old dependency syntax -/
#guard_msgs (substring := true) in
macro "noisy_consumer_quote" : term => ``(dep_old_term)

/-- warning: parameter `old` of `Dep.renamed` has been deprecated, use `new` instead -/
#guard_msgs (substring := true) in
example : Nat := Dep.renamed (old := 1)

/-- warning: `Dep.oldOption` has been deprecated: old dependency option -/
#guard_msgs in
set_option Dep.oldOption true

/-- warning: `Dep.oldOption` has been deprecated: old dependency option -/
#guard_msgs in
example := set_option Dep.oldOption true in 1
