
set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedVariables false in
def thisWorks (x : α₁) (y : size₁) := ()

set_option autoImplicit true in
set_option relaxedAutoImplicit false in
def thisBreaks (x : α₂) (y : size₂) := ()

set_option autoImplicit false in
set_option relaxedAutoImplicit true in
def thisAlsoBreaks (x : α₃) (y : size₃) := ()

set_option autoImplicit false in
set_option relaxedAutoImplicit false in
def thisDefinitelyBreaks (x : α₄) (y : size₄) := ()
