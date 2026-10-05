module

import Plain.UsesTest
import Test.UsesDep
import Test.UsesPlain

public def main : IO Unit := IO.println (fromPlain + fromTest + fromDep)
