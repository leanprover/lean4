/-!
Tests that `trace.Meta.synthInstance` partitions the type class resolution cache: with the trace
enabled, a query is only served from the cache if it was already traced, so that the trace of a
query answered in an earlier command is not reduced to `(cached)`.
-/

class Too (α : Type) where

instance : Too Nat := ⟨⟩

set_option trace.Meta.synthInstance.cache true

/-- trace: [Meta.synthInstance.cache] new: Too Nat -/
#guard_msgs in
def t1 : Unit := let _ : Too Nat := inferInstance; ()

/-- trace: [Meta.synthInstance.cache] cached: Too Nat -/
#guard_msgs in
def t2 : Unit := let _ : Too Nat := inferInstance; ()

-- The first traced query is searched again, and traced in full.
/--
trace: [Meta.synthInstance] ✅️ Too Nat
  [Meta.synthInstance.cache] new: Too Nat
  [Meta.synthInstance] ✅️ new goal Too Nat
    [Meta.synthInstance.instances] #[instTooNat]
  [Meta.synthInstance.apply] ✅️ apply instTooNat to Too Nat
    [Meta.synthInstance.tryResolve] ✅️ Too Nat ≟ Too Nat
    [Meta.synthInstance.answer] ✅️ Too Nat
  [Meta.synthInstance] result instTooNat
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
def t3 : Unit := let _ : Too Nat := inferInstance; ()

-- A repeated traced query is served from the cache.
/--
trace: [Meta.synthInstance] ✅️ Too Nat
  [Meta.synthInstance.cache] cached: Too Nat
  [Meta.synthInstance] result instTooNat (cached)
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
def t4 : Unit := let _ : Too Nat := inferInstance; ()

-- The entries recorded without the trace remain valid.
/-- trace: [Meta.synthInstance.cache] cached: Too Nat -/
#guard_msgs in
def t5 : Unit := let _ : Too Nat := inferInstance; ()
