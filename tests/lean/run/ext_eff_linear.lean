-- TODO: renable test after we restore tactic framework
#exit
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

inductive ftcQueue (m : Type → Type 1) : Type → Type → Type 1
| leaf {α β} (f : α → m β) : ftcQueue α β
| Node {α β γ} : Thunk (ftcQueue α β) → Thunk (ftcQueue β γ) → ftcQueue α γ

inductive ftcQueue.lView (m : Type → Type 1) : Type → Type → Type 1
| single {α β} (f : α → m β) : ftcQueue.lView α β
| cons {α β γ} (f : α → m β) : (Unit → ftcQueue m β γ) → ftcQueue.lView α γ

meta def ftcQueue.viewLAux {m : Type → Type 1} {α} : Π {β γ}, ftcQueue m α β → Thunk (ftcQueue m β γ) → ftcQueue.lView m α γ
| β γ (ftcQueue.leaf f) q := ftcQueue.lView.cons f q
| β γ (ftcQueue.Node n m) q := ftcQueue.viewLAux (n ()) (ftcQueue.Node (m ()) (q ()))

meta def ftcQueue.viewL {m : Type → Type 1} {α β} : ftcQueue m α β → ftcQueue.lView m α β
| (ftcQueue.leaf f) := ftcQueue.lView.single f
| (ftcQueue.Node n m) := ftcQueue.viewLAux (n ()) (m ())

meta inductive eff (effs : List effect) : Type → Type 1
| pure {} {α : Type} (a : α) : eff α
| impure {α β : Type} (u : union effs β) (k : ftcQueue eff β α) : eff α

meta abbreviation arrs (effs) := ftcQueue (eff effs)

meta def arrs.apply {effs} : Π {α β}, arrs effs α β → α → eff effs β
| α β q a := match q.viewL with
  | ftcQueue.lView.single f := f a
  | ftcQueue.lView.cons f q := match f a with
    | eff.pure b := arrs.apply (q ()) b
    | eff.impure u k := eff.impure u (ftcQueue.Node k (q ()))

meta def eff.bind {α β : Type} {effs : List effect} : eff effs α → (α → eff effs β) → eff effs β
| (eff.pure a) f := f a
| (@eff.impure _ _ β u k) f := eff.impure u (ftcQueue.Node k (ftcQueue.leaf f))

meta instance (effs) : Monad (eff effs) :=
{ pure := λ α, eff.pure,
  bind := λ α β, eff.bind }

@[inline] meta def eff.send {e : effect} {effs α} [member e effs] : e α → eff effs α :=
λ x, eff.impure (union.inj x) (ftcQueue.leaf pure)

@[inline] meta def eff.handleRelay {e : effect} {effs α β} (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff (e :: effs) β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ γ u k) := match u.decomp with
  | Sum.inl e := h e (λ c, eff.handleRelay (arrs.apply k c))
  | Sum.inr u := eff.impure u (ftcQueue.leaf (λ c, eff.handleRelay (arrs.apply k c)))


@[inline] meta def eff.handleRelayΣ {e : effect} {effs α β} {σ : Type} (ret : σ → β → eff effs α)
  (h : ∀ {β}, σ → e β → (σ → β → eff effs α) → eff effs α) : σ → eff (e :: effs) β → eff effs α
| st (eff.pure a) := ret st a
| st (@eff.impure _ _ γ u k) := match u.decomp with
  | Sum.inl e := h st e (λ st c, eff.handleRelayΣ st (arrs.apply k c))
  | Sum.inr u := eff.impure u (ftcQueue.leaf (λ c, eff.handleRelayΣ st (arrs.apply k c)))


@[inline] meta def eff.interpose {e : effect} {effs α β} [member e effs] (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff effs β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ γ u k) := match u.prj e with
  | some e := h e (λ c, eff.interpose (arrs.apply k c))
  | none   := eff.impure u (ftcQueue.leaf (λ c, eff.interpose (arrs.apply k c)))


inductive Reader (ρ : Type) : Type → Type
| read {} : Reader ρ

@[inline] meta def eff.read {ρ effs} [member (Reader ρ) effs] : eff effs ρ := eff.send Reader.read
meta instance {ρ effs} [member (Reader ρ) effs] : MonadReader ρ (eff effs) := ⟨eff.read⟩

@[inline] meta def Reader.run {ρ effs α} (env : ρ) : eff (Reader ρ :: effs) α → eff effs α :=
eff.handleRelay pure (λ β x k, by cases x; exact k env)


inductive State (σ : Type) : Type → Type
| get {} : State σ
| put : σ → State Unit

@[inline] meta def eff.get {σ effs} [member (State σ) effs] : eff effs σ := eff.send State.get
@[inline] meta def eff.put {σ effs} [member (State σ) effs] (s : σ) : eff effs Unit := eff.send (State.put s)
meta instance {σ effs} [member (State σ) effs] : MonadState σ (eff effs) :=
⟨λ α x, do st ← eff.get,
           let ⟨a, s'⟩ := x.run st,
           eff.put s',
           pure a⟩

meta def State.run {σ effs α} (st : σ) : eff (State σ :: effs) α → eff effs (α × σ) :=
eff.handleRelayΣ (λ st a, pure (a, st)) (λ β st x k, begin
  cases x,
  case State.get { exact k st st },
  case State.put : st' { exact k st' () }
end) st

inductive Exception (ε α : Type) : Type
| throw {} (ex : ε) : Exception

@[inline] meta def eff.throw {ε α effs} [member (Exception ε) effs] (ex : ε) : eff effs α := eff.send (Exception.throw ex)
@[inline] meta def eff.catch {ε α effs} [member (Exception ε) effs] (x : eff effs α) (handle : ε → eff effs α) : eff effs α :=
x.interpose pure (λ β x k, match (x : Exception ε β) with Exception.throw e := handle e)
meta instance {ε effs} [member (Exception ε) effs] : MonadExcept ε (eff effs) :=
⟨λ α, eff.throw, λ α, eff.catch⟩

@[inline] meta def Exception.run {ε effs α} : eff (Exception ε :: effs) α → eff effs (Except ε α) :=
eff.handleRelay (pure ∘ Except.ok) (λ β x k, match x with Exception.throw e := pure (Except.error e))


meta def eff.run {α : Type} : eff [] α → α
| (eff.pure a) := a


section benchmarks
def State.run {σ α : Type*} : State σ α → σ → α × σ := StateT.run

def benchStateClassy {m : Type → Type*} [Monad m] [MonadState ℕ m] : ℕ → m ℕ
| 0 := get
| (Nat.succ n) := benchStateClassy n <* modify (+n)

setOption profiler True
#eval State.run (benchStateClassy N) 0
#eval eff.run $ State.run 0 (benchStateClassy N)

#eval State.run (ReaderT.run (ReaderT.run (ReaderT.run (benchStateClassy N) 0) 0) 0) 0
#eval eff.run $ State.run 0 $ Reader.run 0 $ Reader.run 0 $ Reader.run 0 (benchStateClassy N)

-- ftcQueue removes the quadratic slowdown
def benchStateClassy' {m : Type → Type*} [Monad m] [MonadState ℕ m] : ℕ → m ℕ
| 0 := get
| (Nat.succ n) := benchStateClassy' n <* modify (+n)


#eval eff.run $ State.run 0 (benchStateClassy' (N/100))
#eval eff.run $ State.run 0 (benchStateClassy' (N/20))
#eval eff.run $ State.run 0 (benchStateClassy' N)

def benchStateT : ℕ → State ℕ ℕ
| 0 := get
| (Nat.succ n) := modify (+n) >> benchStateT n

#eval State.run (benchStateT N) 0

meta def benchState : ℕ → eff [State ℕ] ℕ
| 0 := get
| (Nat.succ n) := modify (+n) >> benchState n

#eval eff.run $ State.run 0 (benchState N)
end benchmarks
