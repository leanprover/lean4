module

public import Lib.HasPriv

/-! Does not see the private `Lib.Init` import of `Lib.HasPriv`. -/

@[expose] public def downstreamVal : Nat := hasPrivVal
