import Lean
/-!
# Tests for the `#where` command
-/

-- Restore the options to a pristine state
set_option internal.cmdlineSnapshots false

/-- info: -- In root namespace with initial scope -/
#guard_msgs in #where

noncomputable section
/-- info: noncomputable section -/
#guard_msgs in #where
end

namespace WhereTest
variable (x : Nat) (α : Type)
/--
info: namespace WhereTest

variable (x : Nat) (α : Type)
-/
#guard_msgs in #where

universe u v
universe w

/--
info: namespace WhereTest

universe u v w

variable (x : Nat) (α : Type)
-/
#guard_msgs in #where

set_option pp.piBinderTypes false

/--
info: namespace WhereTest

universe u v w

variable (x : Nat) (α : Type)

set_option pp.piBinderTypes false
-/
#guard_msgs in #where

include x

/--
info: namespace WhereTest

universe u v w

variable (x : Nat) (α : Type)

include x

set_option pp.piBinderTypes false
-/
#guard_msgs in #where

end WhereTest

section
open Lean Meta

/--
info: open Lean Lean.Meta
-/
#guard_msgs in #where

open Elab hiding TermElabM

/--
info: open Lean Lean.Meta
open Lean.Elab hiding TermElabM
-/
#guard_msgs in #where

open Command Std
open Array renaming map -> listMap

/--
info: open Lean Lean.Meta
open Lean.Elab hiding TermElabM
open Lean.Elab.Command Std
open Array renaming map → listMap
-/
#guard_msgs in #where
end


/-!
Stripping comments on `variable` binders
-/
section
variable (a : Nat)
-- Some discussion
  (b : Nat)
-- Some more discussion

/-- info: variable (a : Nat) (b : Nat) -/
#guard_msgs in #where

end
