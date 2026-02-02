module

import Lib.A

-- Does not use Lib.B, uses Lib.A privately only
def myValue : Nat := valueA
