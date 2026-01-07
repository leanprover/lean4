import Lib.A
import Lib.B

-- Only uses valueA, so Lib.B should be removed by shake
def myValue : Nat := valueA
