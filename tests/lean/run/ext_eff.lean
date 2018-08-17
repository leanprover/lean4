-- TODO: renable test after we restore tactic framework
#exit
import init.io

/- An extensible effects library, inspired by "Freer Monads, More Extensible Effects" (O. Kiselyov, H. Ishii)
   and https://github.com/lexi-lambda/freer-simple -/

def N := 100 -- Default number of interations for testing

def effect := Type → Type

class member {α : Type*} (x : α) (xs : list α) :=
(idx : ℕ)
(prf : xs.nth idx = some x)

instance member_head {α : Type*} (x : α) (xs) : member x (x::xs) :=
⟨0, by simp⟩

instance member_tail {α : Type*} (x y : α) (ys) [member x ys] : member x (y::ys) :=
⟨member.idx x ys + 1, by simp [member.prf x ys]⟩

class last_member {α : Type*} (x : out_param α) (xs : list α) extends member x xs

instance last_member_singleton {α : Type*} (x : α) : last_member x [x] := {}
instance last_member_tail {α : Type*} (x y : α) (ys) [last_member x ys] : last_member x (y::ys) := {}


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


inductive eff (effs : list effect) (α : Type)
| pure {} (a : α) : eff
| impure {β : Type} (u : union effs β) (k : β → eff) : eff

def eff.bind {α β : Type} {effs : list effect} : eff effs α → (α → eff effs β) → eff effs β
| (eff.pure a) f := f a
| (@eff.impure _ _ β u k) f := eff.impure u (λ b, eff.bind (k b) f)

instance (effs) : monad (eff effs) :=
{ pure := λ α, eff.pure,
  bind := λ α β, eff.bind }

@[inline] def eff.send {e : effect} {effs α} [member e effs] : e α → eff effs α :=
λ x, eff.impure (union.inj x) pure

@[inline] def eff.send_m {e : effect} {effs α} [monad e] [last_member e effs] : e α → eff effs α :=
λ x, eff.impure (union.inj x) pure

@[inline] def eff.handle_relay {e : effect} {effs α β} (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff (e :: effs) β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ β u k) := match u.decomp with
  | sum.inl e := h e (λ b, eff.handle_relay (k b))
  | sum.inr u := eff.impure u (λ b, eff.handle_relay (k b))


@[inline] def eff.handle_relay_σ {e : effect} {effs α β} {σ : Type} (ret : σ → β → eff effs α)
  (h : ∀ {β}, σ → e β → (σ → β → eff effs α) → eff effs α) : σ → eff (e :: effs) β → eff effs α
| st (eff.pure a) := ret st a
| st (@eff.impure _ _ β u k) := match u.decomp with
  | sum.inl e := h st e (λ st b, eff.handle_relay_σ st (k b))
  | sum.inr u := eff.impure u (λ b, eff.handle_relay_σ st (k b))


@[inline] def eff.interpose (e : effect) {effs α β} [member e effs] (ret : β → eff effs α)
  (h : ∀ {β}, e β → (β → eff effs α) → eff effs α) : eff effs β → eff effs α
| (eff.pure a) := ret a
| (@eff.impure _ _ β u k) := match u.prj e with
  | some e := h e (λ b, eff.interpose (k b))
  | none   := eff.impure u (λ b, eff.interpose (k b))


inductive Reader (ρ : Type) : Type → Type
| read {} : Reader ρ

@[inline] def eff.read {ρ effs} [member (Reader ρ) effs] : eff effs ρ := eff.send Reader.read
instance {ρ effs} [member (Reader ρ) effs] : monad_reader ρ (eff effs) := ⟨eff.read⟩

@[inline] def Reader.run {ρ effs α} (env : ρ) : eff (Reader ρ :: effs) α → eff effs α :=
eff.handle_relay pure (λ β x k, by cases x; exact k env)


inductive State (σ : Type) : Type → Type
| get {} : State σ
| put : σ → State unit

@[inline] def eff.get {σ effs} [member (State σ) effs] : eff effs σ := eff.send State.get
@[inline] def eff.put {σ effs} [member (State σ) effs] (s : σ) : eff effs unit := eff.send (State.put s)
instance {σ effs} [member (State σ) effs] : monad_state σ (eff effs) :=
⟨λ α x, do st ← eff.get,
           let ⟨a, s'⟩ := x.run st,
           eff.put s',
           pure a⟩

@[inline] def State.run {σ effs α} (st : σ) : eff (State σ :: effs) α → eff effs (α × σ) :=
eff.handle_relay_σ (λ st a, pure (a, st)) (λ β st x k, begin
  cases x,
  case State.get { exact k st st },
  case State.put : st' { exact k st' () }
end) st

inductive Exception (ε α : Type) : Type
| throw {} (ex : ε) : Exception

@[inline] def eff.throw {ε α effs} [member (Exception ε) effs] (ex : ε) : eff effs α := eff.send (Exception.throw ex)
@[inline] def eff.catch {ε α effs} [member (Exception ε) effs] (x : eff effs α) (handle : ε → eff effs α) : eff effs α :=
x.interpose (Exception ε) pure (λ β x k, match x with Exception.throw e := handle e)
instance {ε effs} [member (Exception ε) effs] : monad_except ε (eff effs) :=
⟨λ α, eff.throw, λ α, eff.catch⟩

@[inline] def Exception.run {ε effs α} : eff (Exception ε :: effs) α → eff effs (except ε α) :=
eff.handle_relay (pure ∘ except.ok) (λ β x k, match x with Exception.throw e := pure (except.error e))


def eff.run {α : Type} : eff [] α → α
| (eff.pure a) := a

def eff.run_m {α : Type} {m} [monad m] : eff [m] α → m α
| (eff.pure a) := pure a
| (eff.impure u k) := match u.decomp with
  | sum.inl m := m >>= λ a, eff.run_m (k a)

instance (m effs) [member m effs] : has_monad_lift m (eff effs) :=
⟨λ α, eff.send⟩

section examples

-- from http://okmij.org/ftp/Haskell/extensible/EffDynCatch.hs

@[inline] def io.try {α} : io α → io (except io.error α) :=
λ x, io.catch (except.ok <$> x) (pure ∘ except.error)

instance : has_repr io.error :=
⟨λ e, match e with
      | io.error.sys n := "io.error.sys " ++ repr n
      | io.error.other s := "io.error.other " ++ repr s⟩

@[inline] def eff.catch_io {effs α} [member io effs] (x : eff effs α) (catch : io.error → eff effs α) : eff effs α :=
x.interpose io pure (λ β x k, do ex ← monad_lift x.try,
                                 match ex with
                                 | except.ok b := k b
                                 | except.error e := catch e)

-- like `io.try`, but can be used at any point, not just in the very last layer
@[inline] def eff.try_io {α effs} [member io effs] (x : eff effs α) : eff effs (except io.error α) :=
eff.catch_io (except.ok <$> x) (pure ∘ except.error)

@[inline] def exfn : bool → io bool
| tt := io.fail "thrown"
| ff := pure tt

-- handle IO exceptions before State
def test1 :=
  let tf : bool → eff [io] _ := λ (x : bool), Reader.run x $ State.run ([] : list string) $ eff.try_io $
  do modify (λ xs, "begin"::xs),
     x ← read,
     r ← monad_lift $ exfn x,
     modify (λ xs, "end"::xs),
     pure r in
  do repr <$> eff.run_m (tf tt) >>= io.println,
     repr <$> eff.run_m (tf ff) >>= io.println

#eval test1

-- handle IO exceptions after State
def test2 :=
  let tf : bool → eff [io] _ := λ (x : bool), Reader.run x $ eff.try_io $ State.run ([] : list string) $
  do modify (λ xs, "begin"::xs),
     x ← read,
     r ← monad_lift $ exfn x,
     modify (λ xs, "end"::xs),
     pure r in
  do repr <$> eff.run_m (tf tt) >>= io.println,
     repr <$> eff.run_m (tf ff) >>= io.println

#eval test2

end examples

section benchmarks
def state.run {σ α : Type*} : state σ α → σ → α × σ := state_t.run

def bench_state_classy {m : Type → Type*} [monad m] [monad_state ℕ m] : ℕ → m ℕ
| 0 := get
| (nat.succ n) := modify (+n) >> bench_state_classy n

set_option profiler true
#eval state.run (bench_state_classy N) 0
#eval eff.run $ State.run 0 (bench_state_classy N)

#eval state.run (reader_t.run (reader_t.run (reader_t.run (bench_state_classy N) 0) 0) 0) 0
#eval eff.run $ State.run 0 $ Reader.run 0 $ Reader.run 0 $ Reader.run 0 (bench_state_classy N)

-- left-associated binds lead to quadratic run time (section 2.6)
def bench_state_classy' {m : Type → Type*} [monad m] [monad_state ℕ m] : ℕ → m ℕ
| 0 := get
| (nat.succ n) := bench_state_classy' n <* modify (+n)

#eval eff.run $ State.run 0 (bench_state_classy' (N/100))
#eval eff.run $ State.run 0 (bench_state_classy' (N/20))
#eval eff.run $ State.run 0 (bench_state_classy' (N/10))

def bench_state_t : ℕ → state ℕ ℕ
| 0 := get
| (nat.succ n) := modify (+n) >> bench_state_t n

#eval state.run (bench_state_t N) 0

def bench_State : ℕ → eff [State ℕ] ℕ
| 0 := get
| (nat.succ n) := modify (+n) >> bench_State n

#eval eff.run $ State.run 0 (bench_State N)
end benchmarks
