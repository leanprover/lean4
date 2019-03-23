import init.lean.options

open Lean

@[init] def initRegopt1 : IO Unit :=
registerOption `myNatOpt {defValue := DataValue.ofNat 0, descr := "my Nat option" }

@[init] def initRegopt2 : IO Unit :=
registerOption `myBoolOpt {defValue := DataValue.ofBool true, descr := "my Bool option" }

@[init] def initRegopt3 : IO Unit :=
registerOption `myStringOpt {defValue := DataValue.ofString "", descr := "my String option" }

@[init] def initRegopt4 : IO Unit :=
registerOption `myIntOpt {defValue := DataValue.ofInt 0, descr := "my Int option" }


def main : IO Unit :=
do getOptionDescr `myNatOpt >>= IO.println,
   getOptionDescr `myBoolOpt >>= IO.println,
   getOptionDescr `myIntOpt >>= IO.println,
   let os : Options := {},
   os ← setOptionFromString os "myNatOpt = 100",
   IO.println (os.getNat `myNatOpt),
   os ← setOptionFromString os "myIntOpt = -20",
   IO.println (os.getInt `myIntOpt),
   pure ()
