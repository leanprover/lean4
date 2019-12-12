import Init.Lean
open Lean

structure S1 :=
(x y : Nat)

structure S2 extends S1 :=
(z : Nat)

structure S3 :=
(w : Nat)

structure S4 extends S2, S3 :=
(s : Nat)

def check (b : Bool) : MetaIO Unit :=
unless b $ throw $ IO.userError "check failed"

def tst : MetaIO Unit :=
do env ← MetaIO.getEnv;
   IO.println (getStructureFields env `Lean.Environment);
   check $ getStructureFields env `S4 == #[`toS2, `toS3, `s];
   check $ getStructureFields env `S1 == #[`x, `y];
   check $ isSubobjectField? env `S4 `toS2 == some `S2;
   check $ getParentStructures env `S4 == #[`S2, `S3];
   check $ findField? env `S4 `x == some `S1;
   check $ findField? env `S4 `x1 == none;
   IO.println (getStructureFieldsFlattened env `S4);
   pure ()

#eval tst
