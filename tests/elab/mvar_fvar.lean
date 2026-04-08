import Lean

open Lean

instance : Coe Name FVarId where
  coe n := { name := n }

instance : Coe Name MVarId where
  coe n := { name := n }

#eval (mkFVar `a).hasFVar
#eval (mkApp (mkConst `foo) (mkFVar `a)).hasFVar
#eval (mkApp (mkConst `foo) (mkConst `a)).hasFVar

#eval (mkMVar `a).hasMVar
#eval (mkApp (mkConst `foo) (mkMVar `a)).hasMVar
#eval (mkApp (mkConst `foo) (mkConst `a)).hasMVar
