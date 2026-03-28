module

import CollectAxioms.Chain.Bottom

-- A public def whose body is stripped on export; the axiom dependency
-- is only in the body, not the type.
public def chainDef : True := chainAx
