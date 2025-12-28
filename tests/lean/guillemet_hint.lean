/-!
  # Guillemet hint for using keywords as identifiers

  When a keyword/token is used where an identifier is expected, the error
  message should suggest wrapping it in guillemets («»).
-/

-- Using reserved word as function parameter (shows guillemet hint)
def bar (if : Nat) : Nat := 0  -- 'if' is a keyword

-- This should work (guillemets escape the keyword)
def good1 («if» : Nat) : Nat := «if»

#check good1
