## `simp` local confluence checker

The `Lean.SimpLC` library provides a simp local confluence checker.

* `simp_lc check`: Investigates the full simp set.
* `simp_lc check in X Y Z`: Investigates the simp set in the specified namespaces.
* `simp_lc inspect`: Investigates one pair
* `simp_lc whitelist`: Whitelists a critical pair
* `simp_lc ignore`: Ignores one lemma

The `Lean.SimpLC.Whitelists` module sets up whitelists and ignores for the core Lean repository.

You can check that the simp set for built-in types is still confluent in a downstream library using
```lean
import Lean.SimpLC.Whitelists

#guard_msgs (drop info) in
simp_lc check in String Char Float USize UInt64 UInt32 UInt16 UInt8 PLift ULift Prod Sum Range
  Subtype ByteArray FloatArray List Option Array Int Nat Bool Id
  Monad LawfulFunctor LawfulApplicative LawfulMonad LawfulSingleton Std
```
(optionally adding `_root_`).

You can also add specific namespaces for your project, or even run `simp_lc check` to check all simp lemmas.

