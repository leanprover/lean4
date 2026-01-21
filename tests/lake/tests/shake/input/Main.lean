module

public import Lib.A
public import Lib.B

-- Does not use Lib.B, uses Lib.A privately only
def myValue : Nat := valueA
