module
import Lean
/-!
# Tests for the `#where` command, `module` features
-/

-- Restore the options to a pristine state
set_option internal.cmdlineSnapshots false
set_option printMessageEndPos false
set_option Elab.inServer false

/-- info: -- In root namespace with initial scope -/
#guard_msgs in #where

/-!
Test `noncomputable section`
-/
noncomputable section
/-- info: noncomputable section -/
#guard_msgs in #where
end

/-!
Test `public section`
-/
public section
/-- info: public section -/
#guard_msgs in #where
end

/-!
Test `@[expose] section`
-/
@[expose] section
/-- info: @[expose] section -/
#guard_msgs in #where
end

/-!
Test `meta section`
-/
meta section
/-- info: meta section -/
#guard_msgs in #where
end

/-!
Test combination
-/
@[expose] public noncomputable meta section
/-- info: @[expose] public noncomputable meta section -/
#guard_msgs in #where
end

/-!
Test combination with interleaved namespace. Since `#where` only prints the current scope,
all the `section` modifiers are combined.
-/
public section
namespace Foo
@[expose] section Bar
/--
info: @[expose] public section

namespace Foo
-/
#guard_msgs in #where
end Bar
end Foo
end
