module

-- `import all` so that `Test.A`'s IR is loaded; see `Plain/BadImport.lean`
import all Test.A

public def fromPlain : Nat := twice 10
