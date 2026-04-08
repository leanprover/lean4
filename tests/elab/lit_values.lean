import Lean
open Lean Meta
run_meta IO.println (← getNatValue? (toExpr 2))
run_meta IO.println (← getNatValue? (mkRawNatLit 2))
run_meta IO.println (← getIntValue? (toExpr (2 : Int)))
run_meta IO.println (← getIntValue? (toExpr (-2)))
run_meta IO.println (← getCharValue? (toExpr 'a'))
#eval getStringValue? (toExpr "hello")
run_meta IO.println (← getFinValue? (toExpr (3 : Fin 5)))
run_meta IO.println (← getBitVecValue? (toExpr (3 : BitVec 12)))
run_meta IO.println (← getUInt8Value? (toExpr (2 : UInt8)))
run_meta IO.println (← getUInt16Value? (toExpr (2 : UInt16)))
run_meta IO.println (← getUInt32Value? (toExpr (2 : UInt32)))
run_meta IO.println (← getUInt64Value? (toExpr (2 : UInt64)))
