-- TODO: renable test after we restore tactic framework
#exit
import init.IO

/- An extensible effects library, inspired by "Freer Monads, More Extensible Effects" (O. Kiselyov, H. Ishii)
   and https://github.com/lexi-lambda/freer-simple -/

def N := 100 -- Default number of interations for testing

def effect := Type → Type

class member {α : Type*} (x : α) (xs : List α) :=
(idx : ℕ)
(prf : xs.nth idx = some x)

instance memberHead {α : Type*} (x : α) (xs) : member x (x::xs) :=
⟨0, by simp⟩

instance memberTail {α : Type*} (x y : α) (ys) [member x ys] : member x (y::ys) :=
⟨member.idx x ys + 1, by simp [member.prf x ys]⟩

class lastMember {α : Type*} (x : outParam α) (xs : List α) extends member x xs

instance lastMemberSingleton {α : Type*} (x : α) : lastMember x [x] := {}
instance lastMemberTail {α : Type*} (x y : α) (ys) [lastMember x ys] : lastMember x (y::ys) := {}


structure union (effs : List effect) (α : Type) :=
(eff : effect)
[mem : member eff effs]
(val : eff α)

section
variables {α : Type} {effs : List effect} {eff : effect}

@[inline] def union.inj (val : eff α) [member eff effs] : union effs α :=
{ eff := eff, val := val }

@[inline] def union.prj (u : union effs α) (eff : effect) [mem : member eff effs] : Option (eff α) :=
if h : member.idx eff effs = @member.idx _ u.eff effs u.mem then
  have u.eff = eff,
    by apply Option.some.inj; rw [←member.prf eff effs, ←@member.prf _ u.eff effs u.mem, h],
  some $ cast (congrFun this _) u.val
else none

@[inline] def union.decomp (u : union (eff::effs) α) : eff α ⊕ union effs α :=
begin
  have prf := @member.prf _ u.eff (eff::effs) u.mem,
  cases h : @member.idx _ u.eff (eff::effs) u.mem,
  case Nat.zero {
    have : u.eff = eff,
    by apply Option.some.inj; rw [←prf, h, List.nth],
    rw ←this,
    exact Sum.inl u.val
  },
  case Nat.succ : idx {
    rw [h] at prf,
    exact Sum.inr { mem := ⟨idx, prf⟩, ..u }
  }
end
end


inductive eff (effs : List effect) (α : Type)
| pure {} (a : α) : eff
| impure {β : Type} (u : union effs β) (k : β → eff) : eff

def eff.bind {α β : Type} {effs : List effect} : eff effs α → (α → eff effs β) → eff effs β
| (eff.pure a) f := f a
| (@eff.impure _ _ β u k) f := eff.impure u (fun b => eff.bind (k b) f)

instance (effs) : Monad (eff effs) :=
{ pure := fun α => eff.pure,
  bind := fun α β => eff.bind }

@[inline] def eff.send {e : effect} {effs α} [member e effs] : e α → eff effs α :=
fun x => eff.impure (union.inj x) pure

@[inline] def eff.sendM {e : effect} {effs α} [Monad e] [lastMember e effs] : e α → eff effs α :=
fun x => eff.impure (union.inj x) pure

@[inline] def eff.handleRelay {e : effect} {effs α β} (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff (e :: effs) β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ β u k) := match u.decomp with
  | Sum.inl e := h e (fun b => eff.handleRelay (k b))
  | Sum.inr u := eff.impure u (fun b => eff.handleRelay (k b))


@[inline] def eff.handleRelayΣ {e : effect} {effs α β} {σ : Type} (ret : σ → β → eff effs α)
  (h : ∀ {β}, σ → e β → (σ → β → eff effs α) → eff effs α) : σ → eff (e :: effs) β → eff effs α
| st (eff.pure a) := ret st a
| st (@eff.impure _ _ β u k) := match u.decomp with
  | Sum.inl e := h st e (fun st b => eff.handleRelayΣ st (k b))
  | Sum.inr u := eff.impure u (fun b => eff.handleRelayΣ st (k b))


@[inline] def eff.interpose (e : effect) {effs α β} [member e effs] (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff effs β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ β u k) := match u.prj e with
  | some e := h e (fun b => eff.interpose (k b))
  | none   := eff.impure u (fun b => eff.interpose (k b))


inductive Reader (ρ : Type) : Type → Type
| read {} : Reader ρ

@[inline] def eff.read {ρ effs} [member (Reader ρ) effs] : eff effs ρ := eff.send Reader.read
instance {ρ effs} [member (Reader ρ) effs] : MonadReader ρ (eff effs) := ⟨eff.read⟩

@[inline] def Reader.run {ρ effs α} (env : ρ) : eff (Reader ρ :: effs) α → eff effs α :=
eff.handleRelay pure (fun β x k => by cases x; exact k env)


inductive State (σ : Type) : Type → Type
| get {} : State σ
| put : σ → State Unit

@[inline] def eff.get {σ effs} [member (State σ) effs] : eff effs σ := eff.send State.get
@[inline] def eff.put {σ effs} [member (State σ) effs] (s : σ) : eff effs Unit := eff.send (State.put s)
instance {σ effs} [member (State σ) effs] : MonadState σ (eff effs) :=
⟨fun α x => do st ← eff.get;
           let ⟨a, s'⟩ := x.run st;
           eff.put s';
           pure a⟩

@[inline] def State.run {σ effs α} (st : σ) : eff (State σ :: effs) α → eff effs (α × σ) :=
eff.handleRelayΣ (fun st a => pure (a, st)) (fun β st x k => begin
  cases x,
  case State.get { exact k st st },
  case State.put : st' { exact k st' () }
end) st

inductive Exception (ε α : Type) : Type
| throw {} (ex : ε) : Exception

@[inline] def eff.throw {ε α effs} [member (Exception ε) effs] (ex : ε) : eff effs α := eff.send (Exception.throw ex)
@[inline] def eff.catch {ε α effs} [member (Exception ε) effs] (x : eff effs α) (handle : ε → eff effs α) : eff effs α :=
x.interpose (Exception ε) pure (fun β x k => match x with Exception.throw e := handle e)
instance {ε effs} [member (Exception ε) effs] : MonadExcept ε (eff effs) :=
⟨fun α => eff.throw, fun α => eff.catch⟩

@[inline] def Exception.run {ε effs α} : eff (Exception ε :: effs) α → eff effs (Except ε α) :=
eff.handleRelay (pure ∘ Except.ok) (fun β x k => match x with Exception.throw e := pure (Except.error e))


def eff.run {α : Type} : eff [] α → α
| (eff.pure a) := a

def eff.runM {α : Type} {m} [Monad m] : eff [m] α → m α
| (eff.pure a) := pure a
| (eff.impure u k) := match u.decomp with
  | Sum.inl m := m >>= fun a => eff.runM (k a)

instance (m effs) [member m effs] : HasMonadLift m (eff effs) :=
⟨fun α => eff.send⟩

section examples

-- from http://okmij.org/ftp/Haskell/extensible/EffDynCatch.hs

@[inline] def IO.try {α} : IO α → IO (Except IO.error α) :=
fun x => IO.catch (Except.ok <$> x) (pure ∘ Except.error)

instance : HasRepr IO.error :=
⟨fun e => match e with
      | IO.error.sys n := "IO.error.sys " ++ repr n
      | IO.error.other s := "IO.error.other " ++ repr s⟩

@[inline] def eff.catchIO {effs α} [member IO effs] (x : eff effs α) (catch : IO.error → eff effs α) : eff effs α :=
x.interpose IO pure (fun β x k => do ex ← monadLift x.try;
                                 match ex with
                                 | Except.ok b := k b
                                 | Except.error e := catch e)

-- like `IO.try`, but can be used at any point, not just in the very last layer
@[inline] def eff.tryIO {α effs} [member IO effs] (x : eff effs α) : eff effs (Except IO.error α) :=
eff.catchIO (Except.ok <$> x) (pure ∘ Except.error)

@[inline] def exfn : Bool → IO Bool
| tt := IO.fail "thrown"
| ff := pure tt

-- handle IO exceptions before State
def test1 :=
  let tf : Bool → eff [IO] _ := fun (x : Bool) => Reader.run x $ State.run ([] : List String) $ eff.tryIo $
  do modify (fun xs => "begin"::xs);
     x ← read;
     r ← monadLift $ exfn x;
     modify (fun xs => "end"::xs);
     pure r in
  do repr <$> eff.runM (tf tt) >>= IO.println;
     repr <$> eff.runM (tf ff) >>= IO.println

#eval test1

-- handle IO exceptions after State
def test2 :=
  let tf : Bool → eff [IO] _ := fun (x : Bool) => Reader.run x $ eff.tryIo $ State.run ([] : List String) $
  do modify (fun xs => "begin"::xs);
     x ← read;
     r ← monadLift $ exfn x;
     modify (fun xs => "end"::xs);
     pure r in
  do repr <$> eff.runM (tf tt) >>= IO.println;
     repr <$> eff.runM (tf ff) >>= IO.println

#eval test2

end examples

section benchmarks
def State.run {σ α : Type*} : State σ α → σ → α × σ := StateT.run

def benchStateClassy {m : Type → Type*} [Monad m] [MonadState ℕ m] : ℕ → m ℕ
| 0 := get
| (Nat.succ n) := modify (+n) >> benchStateClassy n

setOption profiler True
#eval State.run (benchStateClassy N) 0
#eval eff.run $ State.run 0 (benchStateClassy N)

#eval State.run (ReaderT.run (ReaderT.run (ReaderT.run (benchStateClassy N) 0) 0) 0) 0
#eval eff.run $ State.run 0 $ Reader.run 0 $ Reader.run 0 $ Reader.run 0 (benchStateClassy N)

-- left-associated binds lead to quadratic run time (section 2.6)
def benchStateClassy' {m : Type → Type*} [Monad m] [MonadState ℕ m] : ℕ → m ℕ
| 0 := get
| (Nat.succ n) := benchStateClassy' n <* modify (+n)

#eval eff.run $ State.run 0 (benchStateClassy' (N/100))
#eval eff.run $ State.run 0 (benchStateClassy' (N/20))
#eval eff.run $ State.run 0 (benchStateClassy' (N/10))

def benchStateT : ℕ → State ℕ ℕ
| 0 := get
| (Nat.succ n) := modify (+n) >> benchStateT n

#eval State.run (benchStateT N) 0

def benchState : ℕ → eff [State ℕ] ℕ
| 0 := get
| (Nat.succ n) := modify (+n) >> benchState n

#eval eff.run $ State.run 0 (benchState N)
end benchmarks
