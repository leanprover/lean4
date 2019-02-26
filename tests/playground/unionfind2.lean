def StateT (m : Type → Type) (σ : Type) (α : Type) := σ → m (α × σ)
namespace StateT
variables {m : Type → Type} [monad m] {σ : Type} {α β : Type}
@[inline] protected def pure (a : α) : StateT m σ α := λ s, pure (a, s)
@[inline] protected def bind (x : StateT m σ α) (f : α → StateT m σ β) : StateT m σ β := λ s, do (a, s') ← x s, f a s'
@[inline] def read : StateT m σ σ := λ s, pure (s, s)
@[inline] def write (s' : σ) : StateT m σ unit := λ s, pure ((), s')
@[inline] def updt (f : σ → σ) : StateT m σ unit := λ s, pure ((), f s)
instance : monad (StateT m σ) :=
{pure := @StateT.pure _ _ _, bind := @StateT.bind _ _ _}
end StateT

def ExceptT (m : Type → Type) (ε : Type) (α : Type) := m (except ε α)
namespace ExceptT
variables {m : Type → Type} [monad m] {ε : Type} {α β : Type}
@[inline] protected def pure (a : α) : ExceptT m ε α := (pure (except.ok a) : m (except ε α))
@[inline] protected def bind (x : ExceptT m ε α) (f : α → ExceptT m ε β) : ExceptT m ε β :=
(do { v ← x, match v with
       | except.error e := pure (except.error e)
       | except.ok a    := f a } : m (except ε β))
@[inline] def error (e : ε) : ExceptT m ε α := (pure (except.error e) : m (except ε α))
@[inline] def lift (x : m α) : ExceptT m ε α := (do {a ← x, pure (except.ok a) } : m (except ε α))
instance : monad (ExceptT m ε) :=
{pure := @ExceptT.pure _ _ _, bind := @ExceptT.bind _ _ _}
end ExceptT

abbreviation node := nat

structure node_data :=
(find : node) (rank : nat := 0)

abbreviation uf_data := array node_data

abbreviation M (α : Type) := ExceptT (StateT id uf_data) string α
@[inline] def read : M uf_data := ExceptT.lift StateT.read
@[inline] def write (s : uf_data) : M unit := ExceptT.lift (StateT.write s)
@[inline] def updt (f : uf_data → uf_data) : M unit := ExceptT.lift (StateT.updt f)
@[inline] def error {α : Type} (e : string) : M α := ExceptT.error e
def run {α : Type} (x : M α) (s : uf_data := array.nil) : except string α × uf_data :=
x s

def capacity : M nat :=
do d ← read, pure d.size

def find_entry_aux : nat → node → M node_data
| 0     n := error "out of fuel"
| (i+1) n :=
  do s ← read,
     if h : n < s.size then
       do { let e := s.read ⟨n, h⟩,
            if e.find = n then pure e
            else do e₁ ← find_entry_aux i e.find,
                    updt (λ s, s.write' n e₁),
                    pure e₁ }
     else error "invalid node"

def find_entry (n : node) : M node_data :=
do c ← capacity,
   find_entry_aux c n

def find (n : node) : M node :=
do e ← find_entry n, pure e.find

def mk : M node :=
do n ← capacity,
   updt $ λ s, s.push {find := n, rank := 1},
   pure n

def union (n₁ n₂ : node) : M unit :=
do r₁ ← find_entry n₁,
   r₂ ← find_entry n₂,
   if r₁.find = r₂.find then pure ()
   else updt $ λ s,
     if r₁.rank < r₂.rank then s.write' r₁.find { find := r₂.find }
     else if r₁.rank = r₂.rank then
        let s₁ := s.write' r₁.find { find := r₂.find } in
        s₁.write' r₂.find { rank := r₂.rank + 1, .. r₂}
     else s.write' r₂.find { find := r₁.find }


def mk_nodes : nat → M unit
| 0     := pure ()
| (n+1) := mk *> mk_nodes n

def check_eq (n₁ n₂ : node) : M unit :=
do r₁ ← find n₁, r₂ ← find n₂,
   unless (r₁ = r₂) $ error "nodes are not equal"

def merge_pack_aux : nat → nat → nat → M unit
| 0     _ _ := pure ()
| (i+1) n d :=
  do c ← capacity,
  if (n+d) < c
  then union n (n+d) *> merge_pack_aux i (n+1) d
  else pure ()

def merge_pack (d : nat) : M unit :=
do c ← capacity, merge_pack_aux c 0 d

def num_eqs_aux : nat → node → nat → M nat
| 0     _ r := pure r
| (i+1) n r :=
  do c ← capacity,
     if n < c
     then do { n₁ ← find n, num_eqs_aux i (n+1) (if n = n₁ then r else r+1) }
     else pure r

def num_eqs : M nat :=
do c ← capacity,
   num_eqs_aux c 0 0

def test (n : nat) : M nat :=
if n < 2 then error "input must be greater than 1"
else do
  mk_nodes n,
  merge_pack 50000,
  merge_pack 10000,
  merge_pack 5000,
  merge_pack 1000,
  num_eqs

def main (xs : list string) : io uint32 :=
let n := xs.head.to_nat in
match run (test n) with
| (except.ok v, s)    := io.println' ("ok " ++ to_string v) *> pure 0
| (except.error e, s) := io.println' ("Error : " ++ e) *> pure 1
