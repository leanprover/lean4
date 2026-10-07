import Prv.Foo

#check { name := "leo", val := 15 : Foo }
#check { name := "leo", val := 15 : Foo }.name
/-- error: Field `val` from structure `Foo` is private -/
#guard_msgs in
#check { name := "leo", val := 15 : Foo }.val

/-- error: Unknown identifier `a` -/
#guard_msgs in
#check a

/--
error: overloaded, errors ⏎
  failed to synthesize instance of type class
    EmptyCollection (Name "hello")
  ⏎
  Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
  ⏎
  invalid {...} notation, constructor for `Name` is marked as private
-/
#guard_msgs in
def m1 : Name "hello" := {}

/-- error: Invalid `⟨...⟩` notation: Constructor for `Name` is marked as private -/
#guard_msgs in
def m2 : Name "hello" := ⟨"hello"⟩

/-- error: Unknown constant `Name.mk` -/
#guard_msgs in
def m3 : Name "hello" := Name.mk "hello"

/-! Tactics that select a constructor do not apply an inaccessible private constructor either. -/

/--
error: Tactic `constructor` failed: constructor `Name.mk✝` is marked as private

⊢ Name "hello"
-/
#guard_msgs in
def m4 : Name "hello" := by constructor; exact "hello"

/--
error: Tactic `left` failed: constructor `Choice.fst✝` is marked as private

⊢ Choice
-/
#guard_msgs in
def m5 : Choice := by left; exact 0

/-! `Mixed.hidden` is skipped, so `Mixed.shown` is the only constructor that matches. -/

#guard_msgs in
example : (by constructor; exact 0 : Mixed) = .shown 0 := rfl
