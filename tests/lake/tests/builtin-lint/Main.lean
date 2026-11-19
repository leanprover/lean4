import Main.Sub

set_option linter.defProp true
set_option linter.checkUnivs true

def shouldBeTheorem : 1 = 1 := rfl

set_option linter.defProp false in
def skippedViolation : 2 = 2 := rfl

@[reducible, instance]
def reducibleInstShouldBeTheorem : Nonempty Bool := ⟨true⟩

instance plainInstIsOk : Nonempty String := ⟨""⟩

universe u v in
def badUnivDecl (α : Type (max u v)) : Type (max u v) := α

set_option linter.checkUnivs false in
universe u v in
def badUnivSkipped (α : Type (max u v)) : Type (max u v) := α
