import init.IO

#exit

/- Based on https://github.com/slindley/effect-handlers -/

def N := 100 -- Default number of interations for testing

namespace handlers

class isOp (op : Type → Type → Type*) := mk {} ::
(return : Type → Type → Type)

class handler (h : Type) := mk {} ::
(Result : Type)

class handles (h : Type) [handler h] (op : Type → Type → Type*) [isOp op] (e : outParam Type) :=
(clause {} {u} : op e u → (isOp.return op e u → h → handler.Result h) → h → handler.Result h)

structure comp (h : Type*) [handler h] (α : Type*) :=
(handle : (α → h → handler.Result h) → h → handler.Result h)

@[inline] def comp.do {h e u} {op : Type → Type → Type*} [isOp op] [handler h] [handles h op e] (f : op e u) : comp h (isOp.return op e u) :=
⟨λ k h, handles.clause f k h⟩

instance (h) [handler h] : Monad (comp h) :=
{ pure := λ α v, ⟨λ k h, k v h⟩,
  bind := λ α β ⟨c⟩ f, ⟨λ k h, c (λ x h', (f x).handle k h') h⟩ }


inductive Put : Type → Type → Type 1
| mk {σ : Type} (s : σ) : Put σ Unit

instance Put.op : isOp Put := ⟨λ _ _, Unit⟩

inductive Get : Type → Type → Type 1
| mk {σ : Type} : Get σ Unit

instance Get.op : isOp Get := ⟨λ σ _, σ⟩

@[inline] def get {h σ } [handler h] [handles h Get σ] : comp h σ :=
comp.do Get.mk
@[inline] def put {h σ} [handler h] [handles h Put σ] (s : σ) : comp h Unit :=
comp.do (Put.mk s)

instance (h σ) [handler h] [handles h Get σ] [handles h Put σ] : MonadState σ (comp h) :=
{ get := get,
  put := put,
  modify := λ f, f <$> get >>= put }

structure stateH (h : Type) (σ : Type) (α : Type) := mk {} ::
(State : σ)

instance (h σ α) [handler h] : handler (stateH h σ α) := ⟨comp h α⟩

instance stateHHandleGet (h σ α) [handler h] : handles (stateH h σ α) Get σ :=
⟨λ _ _ k ⟨st⟩, k st ⟨st⟩⟩

instance stateHHandlePut (h σ α) [handler h] : handles (stateH h σ α) Put σ :=
⟨λ _ op k _, by cases op with _ st'; apply k () ⟨st'⟩⟩

instance stateHForward (h op σ α) [handler h] [isOp op] [handles h op α] : handles (stateH h σ α) op α :=
⟨λ _ op k hi, comp.do op >>= (λ x, k x hi)⟩

@[inline] def handleState {h σ α} [handler h] (st : σ) (x : comp (stateH h σ α) α) : comp h α :=
x.handle (λ a _, (pure a : comp h α)) ⟨st⟩


inductive Read : Type → Type → Type 1
| mk {ρ : Type} : Read ρ Unit

instance Read.op : isOp Read := ⟨λ ρ _, ρ⟩

@[inline] def read {h ρ} [handler h] [handles h Read ρ] : comp h ρ :=
comp.do Read.mk

instance (h ρ) [handler h] [handles h Read ρ] : MonadReader ρ (comp h) :=
⟨read⟩

structure readH (h : Type) (ρ : Type) (α : Type) := mk {} ::
(env : ρ)

instance readH.handler (h ρ α) [handler h] : handler (readH h ρ α) := ⟨comp h α⟩

instance readHHandleRead (h ρ α) [handler h] : handles (readH h ρ α) Read ρ :=
⟨λ _ _ k ⟨env⟩, k env ⟨env⟩⟩

instance readHForward (h op ρ α) [handler h] [isOp op] [handles h op α] : handles (readH h ρ α) op α :=
⟨λ _ op k hi, comp.do op >>= (λ x, k x hi)⟩

@[inline] def handleRead {h ρ α} [handler h] (env : ρ) (x : comp (readH h ρ α) α) : comp h α :=
x.handle (λ a _, (pure a : comp h α)) ⟨env⟩


structure pureH (α : Type) := mk {}

instance pureH.handler (α) : handler (pureH α) := ⟨α⟩

@[inline] def handlePure {α} (x : comp (pureH α) α) : α :=
x.handle (λ a _, a) ⟨⟩
end handlers


open handlers

section benchmarks
def State.run {σ α : Type*} : State σ α → σ → α × σ := StateT.run

def benchStateClassy {m : Type → Type*} [Monad m] [MonadState ℕ m] : ℕ → m ℕ
| 0 := get
| (Nat.succ n) := modify (+n) >> benchStateClassy n

setOption profiler True
#eval State.run (benchStateClassy N) 0
#eval handlePure $ handleState 0 (benchStateClassy N)

#eval State.run (ReaderT.run (ReaderT.run (benchStateClassy N) 0) 0) 0
#eval handlePure $ handleState 0 $ handleRead 0 $ handleRead 0 (benchStateClassy N)

-- left-associated binds lead to quadratic run time (section 2.6)
def benchStateClassy' {m : Type → Type*} [Monad m] [MonadState ℕ m] : ℕ → m ℕ
| 0 := get
| (Nat.succ n) := benchStateClassy' n <* modify (+n)

#eval handlePure $ handleState 0 (benchStateClassy' (N/100))
#eval handlePure $ handleState 0 (benchStateClassy' (N/20))
#eval handlePure $ handleState 0 (benchStateClassy' (N/10))

def benchStateT : ℕ → State ℕ ℕ
| 0 := get
| (Nat.succ n) := modify (+n) >> benchStateT n

#eval State.run (benchStateT N) 0

def benchStateH : ℕ → comp (stateH (pureH ℕ) ℕ ℕ) ℕ
| 0 := handlers.get
| (Nat.succ n) := modify (+n) >> benchStateH n

#eval handlePure $ handleState 0 (benchStateH N)
end benchmarks
