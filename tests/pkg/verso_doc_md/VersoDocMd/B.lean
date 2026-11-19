module

public import VersoDocMd.Defs
public import VersoDocMd.A

public section

/-! Defines `Bar`, whose docstring includes `Foo`'s docstring through the deferred Markdown renderer role. -/

set_option doc.verso true
set_option doc.verso.suggestions false

/-- Included: {include_docstring}`Foo` -/
def Bar : Nat := 1
