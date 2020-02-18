/-
Sub-optimal error message.
The implementation detail that an auxiliary function `foo._main` leaks,
when there is a simple explanation for the problem that doesn't involve it.
-/

def foo : Nat → Unit
| 0 => ()
| n+1 => foo n

-- Second recursive function with same name.
/-
def foo : Nat → Unit
| 0 => ()
| n+1 => foo n
-/
-- error: equation compiler failed to create auxiliary declaration 'foo._main'
-- nested exception message:
-- invalid declaration, a declaration named 'foo._main' has already been declared

/-
[Leo]: Rob Lewis reported the issue for Lean3 a few years ago. I told him I would not fix it since I think it is obvious to understand the problem. We will write a new equation compiler. We will fix it if it only if it doesn't increase the complexity.
-/
