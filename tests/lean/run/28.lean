structure bv (w : Nat) := (u:Unit)

inductive val : Type
| bv (w : Nat) : bv w → val

inductive memtype : Type
| ptr : Unit → memtype

inductive instr : Type
| load : memtype -> val -> instr
| store : Unit -> Unit -> Unit -> instr

structure sim (a:Type) :=
  (runSim :
     ∀{z:Type},
     (IO.Error → z)  /- error continuation -/ →
     (a → z) /- normal continuation -/ →
     z)

instance monad : Monad sim :=
  { bind := λa b mx mf => sim.mk (λz kerr k =>
       mx.runSim kerr (λx => (mf x).runSim kerr k))
  , pure := λa x => sim.mk (λz _ k => k x)
  }

instance monadExcept : MonadExcept IO.Error sim :=
  { throw := λa err => sim.mk (λz kerr _k => kerr err)
  , catch := λa m handle => sim.mk (λz kerr k =>
      let kerr' := λerr => (handle err).runSim kerr k;
      m.runSim kerr' k)
  }.

def f : sim val := throw (IO.userError "ASDF")
def g : sim Unit := throw (IO.userError "ASDF")

def evalInstr : instr → sim (Option val)
| instr.load mt pv =>
      match mt, pv with
      | memtype.ptr _, val.bv 27 _ => throw (IO.userError "ASDF")
      | _, _ => throw (IO.userError "expected pointer value in load" )

| instr.store _ _ _ =>
   do pv <- f;
      _ <- g;
      match pv with
      | val.bv 27 _ => throw (IO.userError "asdf")
      | _ => throw (IO.userError "expected pointer value in store" )
