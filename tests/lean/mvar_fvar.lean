import Init.Lean
open Lean

#eval (mkFVar `a).hasFVar
#eval (mkApp (mkConst `foo) (mkFVar `a)).hasFVar
#eval (mkApp (mkConst `foo) (mkConst `a)).hasFVar

#eval (mkMVar `a).hasMVar
#eval (mkApp (mkConst `foo) (mkMVar `a)).hasMVar
#eval (mkApp (mkConst `foo) (mkConst `a)).hasMVar
