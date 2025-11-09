
set_option linter.unusedVariables false in
def thisWorks (x : α₁) (y : size₁) := ()

set_option relaxedAutoImplicit false in
def thisBreaks (x : α₂) (y : size₂) := ()

set_option autoImplicit false in
def thisAlsoBreaks (x : α₃) (y : size₃) := ()
