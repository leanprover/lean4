import Init.System.IO

structure MyState :=
(bs : Nat := 0) -- backtrackable state
(ps : Nat := 0) -- non backtrackable state

instance : HasRepr MyState :=
⟨fun s => repr (s.bs, s.ps)⟩

instance : EState.Backtrackable Nat MyState :=
{ save    := fun s => s.bs,
  restore := fun s d => { bs := d, .. s }  }

abbrev M := EState String MyState

def bInc : M Unit := -- increment backtrackble counter
modify $ fun s => { bs := s.bs + 1, .. s }

def pInc : M Unit := -- increment nonbacktrackable counter
modify $ fun s => { ps := s.ps + 1, .. s }

def tst : M MyState :=
do bInc;
   pInc;
   ((bInc *> throw "failed") <|> pInc);
   pInc;
   get

#eval tst.run' {} -- (some (1, 3))
