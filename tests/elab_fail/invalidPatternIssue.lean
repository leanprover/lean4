structure Pos where
  protected succ ::
  protected pred : Nat

protected def Pos.add : Pos → Pos → Pos
| Pos.succ x, Pos.succ y => Pos.succ (x + y).succ
instance : Add Pos := ⟨Pos.add⟩

instance (x : Nat) : OfNat Pos x.succ := ⟨Pos.succ x⟩

def f : Pos → Pos
| 1 => 1
| x+1 => f x + x + 1
