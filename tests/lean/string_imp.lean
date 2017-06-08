def f : string → list char
| ⟨d⟩ := d -- ERROR string implementation is sealed

def g : string → list char
| (string_imp.mk d) := d -- ERROR string implementation is sealed

def h (s : string) : list char :=
string_imp.cases_on s (λ d, d) -- ERROR string implementation is sealed
