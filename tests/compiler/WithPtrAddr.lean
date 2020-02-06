
-- import Test.WithPtrAddrUtil
variables {α β : Type}

@[inline]
def withPtrAddr' [Subsingleton β] (x : α) (k : USize → β) : β :=
withPtrAddr x k $ fun _ _ => Subsingleton.elim _ _

def withPtrAddr'' [Subsingleton β] (x : α) (k : USize → β) : β :=
withPtrAddr x k $ fun _ _ => Subsingleton.elim _ _

def main : IO Unit := do
  let list := [1,2];
  IO.println $ withPtrAddr list
    (fun p => dbgTrace (toString $ p == 0) $ fun x => x)
    (fun _ _ => Subsingleton.elim _ _);
  IO.println $ withPtrAddr' list
    (fun p => dbgTrace (toString $ p == 0) $ fun x => x);
  IO.println $ withPtrAddr'' list
    (fun p => dbgTrace (toString $ p == 0) $ fun x => x);
  pure ()


#eval main
