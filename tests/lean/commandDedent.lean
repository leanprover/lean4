/-!
Dedent before the next command should prevent partial input from being read as part of the current
command.
-/

def foo :=
  1

de  -- should say 'expected command'
