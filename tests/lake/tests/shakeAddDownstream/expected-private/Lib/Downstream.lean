module

public import Lib.HasPriv
import Lib.Init

/-! Does not see the private `Lib.Init` import of `Lib.HasPriv`. -/

@[expose] public def downstreamVal : Nat := hasPrivVal
