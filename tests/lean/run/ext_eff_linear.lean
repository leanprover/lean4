/- An extensible effects library, inspired by "Freer Monads, More Extensible Effects" (O. Kiselyov, H. Ishii)
   and https://github.com/lexi-lambda/freer-simple -/

def effect := Type → Type

class member {α : Type*} (x : α) (xs : list α) :=
(idx : ℕ)
(prf : xs.nth idx = some x)

instance member_head {α : Type*} (x : α) (xs) : member x (x::xs) :=
⟨0, by simp⟩

instance member_tail {α : Type*} (x y : α) (ys) [member x ys] : member x (y::ys) :=
⟨member.idx x ys + 1, by simp [member.prf x ys]⟩


structure union (effs : list effect) (α : Type) :=
(eff : effect)
[mem : member eff effs]
(val : eff α)

section
variables {α : Type} {effs : list effect} {eff : effect}

@[inline] def union.inj (val : eff α) [member eff effs] : union effs α :=
{ eff := eff, val := val }

@[inline] def union.prj (u : union effs α) (eff : effect) [mem : member eff effs] : option (eff α) :=
if h : member.idx eff effs = @member.idx _ u.eff effs u.mem then
  have u.eff = eff,
    by apply option.some.inj; rw [←member.prf eff effs, ←@member.prf _ u.eff effs u.mem, h],
  some $ cast (congr_fun this _) u.val
else none

@[inline] def union.decomp (u : union (eff::effs) α) : eff α ⊕ union effs α :=
begin
  have prf := @member.prf _ u.eff (eff::effs) u.mem,
  cases h : @member.idx _ u.eff (eff::effs) u.mem,
  case nat.zero {
    have : u.eff = eff,
    by apply option.some.inj; rw [←prf, h, list.nth],
    rw ←this,
    exact sum.inl u.val
  },
  case nat.succ : idx {
    rw [h] at prf,
    exact sum.inr { mem := ⟨idx, prf⟩, ..u }
  }
end
end


inductive ftc_queue (m : Type → Type 1) : Type → Type → Type 1
| leaf {α β} (f : α → m β) : ftc_queue α β
| node {α β γ} : thunk (ftc_queue α β) → thunk (ftc_queue β γ) → ftc_queue α γ

inductive ftc_queue.l_view (m : Type → Type 1) : Type → Type → Type 1
| single {α β} (f : α → m β) : ftc_queue.l_view α β
| cons {α β γ} (f : α → m β) : (unit → ftc_queue m β γ) → ftc_queue.l_view α γ

meta def ftc_queue.view_l_aux {m : Type → Type 1} {α} : Π {β γ}, ftc_queue m α β → thunk (ftc_queue m β γ) → ftc_queue.l_view m α γ
| β γ (ftc_queue.leaf f) q := ftc_queue.l_view.cons f q
| β γ (ftc_queue.node n m) q := ftc_queue.view_l_aux (n ()) (ftc_queue.node (m ()) (q ()))

meta def ftc_queue.view_l {m : Type → Type 1} {α β} : ftc_queue m α β → ftc_queue.l_view m α β
| (ftc_queue.leaf f) := ftc_queue.l_view.single f
| (ftc_queue.node n m) := ftc_queue.view_l_aux (n ()) (m ())

meta inductive eff (effs : list effect) : Type → Type 1
| pure {} {α : Type} (a : α) : eff α
| impure {α β : Type} (u : union effs β) (k : ftc_queue eff β α) : eff α

meta abbreviation arrs (effs) := ftc_queue (eff effs)

meta def arrs.apply {effs} : Π {α β}, arrs effs α β → α → eff effs β
| α β q a := match q.view_l with
  | ftc_queue.l_view.single f := f a
  | ftc_queue.l_view.cons f q := match f a with
    | eff.pure b := arrs.apply (q ()) b
    | eff.impure u k := eff.impure u (ftc_queue.node k (q ()))

meta def eff.bind {α β : Type} {effs : list effect} : eff effs α → (α → eff effs β) → eff effs β
| (eff.pure a) f := f a
| (@eff.impure _ _ β u k) f := eff.impure u (ftc_queue.node k (ftc_queue.leaf f))

meta instance (effs) : monad (eff effs) :=
{ pure := λ α, eff.pure,
  bind := λ α β, eff.bind }

@[inline] meta def eff.send {e : effect} {effs α} [member e effs] : e α → eff effs α :=
λ x, eff.impure (union.inj x) (ftc_queue.leaf pure)

@[inline] meta def eff.handle_relay {e : effect} {effs α β} (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff (e :: effs) β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ γ u k) := match u.decomp with
  | sum.inl e := h e (λ c, eff.handle_relay (arrs.apply k c))
  | sum.inr u := eff.impure u (ftc_queue.leaf (λ c, eff.handle_relay (arrs.apply k c)))


@[inline] meta def eff.handle_relay_σ {e : effect} {effs α β} {σ : Type} (ret : σ → β → eff effs α)
  (h : ∀ {β}, σ → e β → (σ → β → eff effs α) → eff effs α) : σ → eff (e :: effs) β → eff effs α
| st (eff.pure a) := ret st a
| st (@eff.impure _ _ γ u k) := match u.decomp with
  | sum.inl e := h st e (λ st c, eff.handle_relay_σ st (arrs.apply k c))
  | sum.inr u := eff.impure u (ftc_queue.leaf (λ c, eff.handle_relay_σ st (arrs.apply k c)))


@[inline] meta def eff.interpose {e : effect} {effs α β} [member e effs] (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff effs β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ γ u k) := match u.prj e with
  | some e := h e (λ c, eff.interpose (arrs.apply k c))
  | none   := eff.impure u (ftc_queue.leaf (λ c, eff.interpose (arrs.apply k c)))


inductive Reader (ρ : Type) : Type → Type
| read {} : Reader ρ

@[inline] meta def eff.read {ρ effs} [member (Reader ρ) effs] : eff effs ρ := eff.send Reader.read
meta instance {ρ effs} [member (Reader ρ) effs] : monad_reader ρ (eff effs) := ⟨eff.read⟩

@[inline] meta def Reader.run {ρ effs α} (env : ρ) : eff (Reader ρ :: effs) α → eff effs α :=
eff.handle_relay pure (λ β x k, by cases x; exact k env)


inductive State (σ : Type) : Type → Type
| get {} : State σ
| put : σ → State unit

@[inline] meta def eff.get {σ effs} [member (State σ) effs] : eff effs σ := eff.send State.get
@[inline] meta def eff.put {σ effs} [member (State σ) effs] (s : σ) : eff effs unit := eff.send (State.put s)
meta instance {σ effs} [member (State σ) effs] : monad_state σ (eff effs) :=
⟨λ α x, do st ← eff.get,
           let ⟨a, s'⟩ := x.run st,
           eff.put s',
           pure a⟩

meta def State.run {σ effs α} (st : σ) : eff (State σ :: effs) α → eff effs (α × σ) :=
eff.handle_relay_σ (λ st a, pure (a, st)) (λ β st x k, begin
  cases x,
  case State.get { exact k st st },
  case State.put : st' { exact k st' () }
end) st

inductive Exception (ε α : Type) : Type
| throw {} (ex : ε) : Exception

@[inline] meta def eff.throw {ε α effs} [member (Exception ε) effs] (ex : ε) : eff effs α := eff.send (Exception.throw ex)
@[inline] meta def eff.catch {ε α effs} [member (Exception ε) effs] (x : eff effs α) (handle : ε → eff effs α) : eff effs α :=
x.interpose pure (λ β x k, match (x : Exception ε β) with Exception.throw e := handle e)
meta instance {ε effs} [member (Exception ε) effs] : monad_except ε (eff effs) :=
⟨λ α, eff.throw, λ α, eff.catch⟩

@[inline] meta def Exception.run {ε effs α} : eff (Exception ε :: effs) α → eff effs (except ε α) :=
eff.handle_relay (pure ∘ except.ok) (λ β x k, match x with Exception.throw e := pure (except.error e))


meta def eff.run {α : Type} : eff [] α → α
| (eff.pure a) := a


section benchmarks
def state.run {σ α : Type*} : state σ α → σ → α × σ := state_t.run

def bench_state_classy {m : Type → Type*} [monad m] [monad_state ℕ m] : ℕ → m ℕ
| 0 := get
| (nat.succ n) := bench_state_classy n <* modify (+n)

set_option profiler true
#eval state.run (bench_state_classy 10000) 0
#eval eff.run $ State.run 0 (bench_state_classy 10000)

#eval state.run (reader_t.run (reader_t.run (reader_t.run (bench_state_classy 10000) 0) 0) 0) 0
#eval eff.run $ State.run 0 $ Reader.run 0 $ Reader.run 0 $ Reader.run 0 (bench_state_classy 10000)

-- ftc_queue removes the quadratic slowdown
def bench_state_classy' {m : Type → Type*} [monad m] [monad_state ℕ m] : ℕ → m ℕ
| 0 := get
| (nat.succ n) := bench_state_classy' n <* modify (+n)

#eval eff.run $ State.run 0 (bench_state_classy' 100)
#eval eff.run $ State.run 0 (bench_state_classy' 500)
#eval eff.run $ State.run 0 (bench_state_classy' 1000)

def bench_state_t : ℕ → state ℕ ℕ
| 0 := get
| (nat.succ n) := modify (+n) >> bench_state_t n

#eval state.run (bench_state_t 10000) 0

meta def bench_State : ℕ → eff [State ℕ] ℕ
| 0 := get
| (nat.succ n) := modify (+n) >> bench_State n

#eval eff.run $ State.run 0 (bench_State 10000)
end benchmarks
