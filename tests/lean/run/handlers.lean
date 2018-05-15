import system.io

/- Based on https://github.com/slindley/effect-handlers -/

def N := 100 -- Default number of interations for testing

namespace handlers

class is_op (op : Type → Type → Type*) := mk {} ::
(return : Type → Type → Type)

class handler (h : Type) := mk {} ::
(result : Type)

class handles (h : Type) [handler h] (op : Type → Type → Type*) [is_op op] (e : out_param Type) :=
(clause {} {u} : op e u → (is_op.return op e u → h → handler.result h) → h → handler.result h)

structure comp (h : Type*) [handler h] (α : Type*) :=
(handle : (α → h → handler.result h) → h → handler.result h)

@[inline] def comp.do {h e u} {op : Type → Type → Type*} [is_op op] [handler h] [handles h op e] (f : op e u) : comp h (is_op.return op e u) :=
⟨λ k h, handles.clause f k h⟩

instance (h) [handler h] : monad (comp h) :=
{ pure := λ α v, ⟨λ k h, k v h⟩,
  bind := λ α β ⟨c⟩ f, ⟨λ k h, c (λ x h', (f x).handle k h') h⟩ }


inductive Put : Type → Type → Type 1
| mk {σ : Type} (s : σ) : Put σ unit

instance Put.op : is_op Put := ⟨λ _ _, unit⟩

inductive Get : Type → Type → Type 1
| mk {σ : Type} : Get σ unit

instance Get.op : is_op Get := ⟨λ σ _, σ⟩

@[inline] def get {h σ } [handler h] [handles h Get σ] : comp h σ :=
comp.do Get.mk
@[inline] def put {h σ} [handler h] [handles h Put σ] (s : σ) : comp h unit :=
comp.do (Put.mk s)

instance (h σ) [handler h] [handles h Get σ] [handles h Put σ] : monad_state σ (comp h) :=
{ lift := λ α x, do s ← get,
                    let (a, s') := x.run s,
                    put s,
                    pure a }

structure state_h (h : Type) (σ : Type) (α : Type) := mk {} ::
(state : σ)

instance (h σ α) [handler h] : handler (state_h h σ α) := ⟨comp h α⟩

instance state_h_handle_Get (h σ α) [handler h] : handles (state_h h σ α) Get σ :=
⟨λ _ _ k ⟨st⟩, k st ⟨st⟩⟩

instance state_h_handle_Put (h σ α) [handler h] : handles (state_h h σ α) Put σ :=
⟨λ _ op k _, by cases op with _ st'; apply k () ⟨st'⟩⟩

instance state_h_forward (h op σ α) [handler h] [is_op op] [handles h op α] : handles (state_h h σ α) op α :=
⟨λ _ op k hi, comp.do op >>= (λ x, k x hi)⟩

@[inline] def handle_state {h σ α} [handler h] (st : σ) (x : comp (state_h h σ α) α) : comp h α :=
x.handle (λ a _, (pure a : comp h α)) ⟨st⟩


inductive Read : Type → Type → Type 1
| mk {ρ : Type} : Read ρ unit

instance Read.op : is_op Read := ⟨λ ρ _, ρ⟩

@[inline] def read {h ρ} [handler h] [handles h Read ρ] : comp h ρ :=
comp.do Read.mk

instance (h ρ) [handler h] [handles h Read ρ] : monad_reader ρ (comp h) :=
⟨read⟩

structure read_h (h : Type) (ρ : Type) (α : Type) := mk {} ::
(env : ρ)

instance read_h.handler (h ρ α) [handler h] : handler (read_h h ρ α) := ⟨comp h α⟩

instance read_h_handle_Read (h ρ α) [handler h] : handles (read_h h ρ α) Read ρ :=
⟨λ _ _ k ⟨env⟩, k env ⟨env⟩⟩

instance read_h_forward (h op ρ α) [handler h] [is_op op] [handles h op α] : handles (read_h h ρ α) op α :=
⟨λ _ op k hi, comp.do op >>= (λ x, k x hi)⟩

@[inline] def handle_read {h ρ α} [handler h] (env : ρ) (x : comp (read_h h ρ α) α) : comp h α :=
x.handle (λ a _, (pure a : comp h α)) ⟨env⟩


structure pure_h (α : Type) := mk {}

instance pure_h.handler (α) : handler (pure_h α) := ⟨α⟩

@[inline] def handle_pure {α} (x : comp (pure_h α) α) : α :=
x.handle (λ a _, a) ⟨⟩
end handlers


open handlers

section benchmarks
def state.run {σ α : Type*} : state σ α → σ → α × σ := state_t.run

def bench_state_classy {m : Type → Type*} [monad m] [monad_state ℕ m] : ℕ → m ℕ
| 0 := get
| (nat.succ n) := modify (+n) >> bench_state_classy n

set_option profiler true
#eval state.run (bench_state_classy N) 0
#eval handle_pure $ handle_state 0 (bench_state_classy N)

#eval state.run (reader_t.run (reader_t.run (bench_state_classy N) 0) 0) 0
#eval handle_pure $ handle_state 0 $ handle_read 0 $ handle_read 0 (bench_state_classy N)

-- left-associated binds lead to quadratic run time (section 2.6)
def bench_state_classy' {m : Type → Type*} [monad m] [monad_state ℕ m] : ℕ → m ℕ
| 0 := get
| (nat.succ n) := bench_state_classy' n <* modify (+n)

#eval handle_pure $ handle_state 0 (bench_state_classy' (N/100))
#eval handle_pure $ handle_state 0 (bench_state_classy' (N/20))
#eval handle_pure $ handle_state 0 (bench_state_classy' (N/10))

def bench_state_t : ℕ → state ℕ ℕ
| 0 := get
| (nat.succ n) := modify (+n) >> bench_state_t n

#eval state.run (bench_state_t N) 0

def bench_state_h : ℕ → comp (state_h (pure_h ℕ) ℕ ℕ) ℕ
| 0 := handlers.get
| (nat.succ n) := modify (+n) >> bench_state_h n

#eval handle_pure $ handle_state 0 (bench_state_h N)
end benchmarks
