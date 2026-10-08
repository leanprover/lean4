-- Test that using a keyword where an identifier is expected shows guillemet hint

def good1 («if» : Nat) : Nat := «if»

-- error below
def bad1 (if : Nat) : Nat := if
