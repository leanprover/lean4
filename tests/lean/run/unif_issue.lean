import Lean

open Lean

#eval toString $
  Unhygienic.run do
    let a ← `(Nat.one);
    let rhs_0 : _ := fun (a : Lean.Syntax) (b : Lean.Syntax) => pure Syntax.missing;
    let rhs_1 : _ := fun (_a : _) => pure Lean.Syntax.missing;
    let discr_2 : _ := a;
    ite (Lean.Syntax.isOfKind discr_2 (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Lean") "Parser") "Term") "add"))
      (let discr_3 : _ := Lean.Syntax.getArg discr_2 0;
       let discr_4 : _ := Lean.Syntax.getArg discr_2 1;
       let discr_5 : _ := Lean.Syntax.getArg discr_2 2;
       rhs_0 discr_3 discr_5)
      (let discr_7 : _ := a;
       rhs_1 Unit.unit)


#check (pure 0 : Id Nat)

#check (let rhs := fun a => pure a; rhs 0 : Id Nat)

#check toString $
  Unhygienic.run do
    let a ← `(Nat.one);
    let rhs_0 : _ := fun (a : Lean.Syntax) (b : Lean.Syntax) => pure Syntax.missing;
    let rhs_1 : _ := fun (_a : _) => pure Lean.Syntax.missing;
    let discr_2 : _ := a;
    ite (Lean.Syntax.isOfKind discr_2 (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Lean") "Parser") "Term") "add"))
      (let discr_3 : _ := Lean.Syntax.getArg discr_2 0;
       let discr_4 : _ := Lean.Syntax.getArg discr_2 1;
       let discr_5 : _ := Lean.Syntax.getArg discr_2 2;
       rhs_0 discr_3 discr_5)
      (let discr_7 : _ := a;
       rhs_1 Unit.unit)
