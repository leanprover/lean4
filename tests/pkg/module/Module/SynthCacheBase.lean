module

/-! Auxiliary module for `Module.SynthCache`. -/

public class SynthCacheTest (α : Type) where
  val : Nat

public instance instSynthCacheTestBase : SynthCacheTest Nat := ⟨1⟩
