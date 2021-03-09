abbrev M := ExceptT String $ StateT Nat Id

/- The following instances are not needed, but they speedup the proof -/
instance : Monad M := inferInstance
instance : LawfulMonad M := inferInstance
instance : MonadStateOf Nat M := inferInstance
instance : Bind M := inferInstance
instance : Pure M := inferInstance

syntax "bigAdd0Seq! " num : term

macro_rules
  | `(bigAdd0Seq! $n) =>
    let n := n.toNat
    if n == 0 then
      `(pure ())
    else
      `(get >>= fun n => set (0 + n) >>= fun _ => bigAdd0Seq! $(Lean.quote (n - 1)))

@[simp] theorem get_set  : (get >>= fun n => set n) = (pure () : M Unit) :=
  rfl

set_option maxRecDepth   1000000
set_option maxHeartbeats 1000000

theorem ex : (bigAdd0Seq! 40 : M Unit) = pure () := by
  simp

-- set_option pp.explicit true
-- set_option pp.notation false
-- #print ex
