module

public import Module.SynthCacheBase
import Module.SynthCachePriv

/-!
Type class resolution results are not shared between the public and the private scope:
`instSynthCacheTestPriv` is imported privately, so it is found in proofs but not in public
signatures, and a cached result of one scope must not be served in the other, within a command or
across commands.
-/

public theorem publicThenPrivate : SynthCacheTest.val Nat = 1 :=
  have : SynthCacheTest.val Nat = 2 := rfl
  rfl

theorem privateScope : SynthCacheTest.val Nat = 2 := rfl

public theorem publicAfterPrivate : SynthCacheTest.val Nat = 1 := by rfl
