/-!
Tests `linter.fmt.missing.ignorePrivate`, which suppresses `fmt.missing` warnings for
syntax declared with `local`, whose node kinds are mangled by `mkPrivateName`.
-/

local macro "my_local_cmd " x:ident : command => `(def $x := 1)
macro "my_public_cmd " x:ident : command => `(def $x := 2)

set_option linter.fmt.missing true

-- Both kinds are reported by default.
my_local_cmd a
my_public_cmd b

set_option linter.fmt.missing.ignorePrivate true

-- Only the public kind is still reported.
my_local_cmd c
my_public_cmd d
