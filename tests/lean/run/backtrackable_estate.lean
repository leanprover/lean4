import Init.System.IO


structure MyState :=
  bs : Nat := 0 -- backtrackable state
  ps : Nat := 0 -- non backtrackable state

instance : Repr MyState where
  reprPrec s _ := repr (s.bs, s.ps)

instance : EStateM.Backtrackable Nat MyState :=
{ save    := fun s => s.bs,
  restore := fun s d => { s with bs := d }  }

abbrev M := EStateM String MyState

def bInc : M Unit := -- increment backtrackble counter
modify $ fun s => { s with bs := s.bs + 1 }

def pInc : M Unit := -- increment nonbacktrackable counter
modify $ fun s => { s with ps := s.ps + 1 }

def tst : M MyState :=
do bInc;
   pInc;
   ((bInc *> throw "failed") <|> pInc);
   pInc;
   get

#eval tst.run' {} -- (some (1, 3))
