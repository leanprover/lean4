## `simp` local confluence checker

The `Simplc` library provides a simp local confluence checker. 

* `simp_lc check`: Investigates the full simp set.
* `simp_lc check in X Y Z`: Investigates the simp set in the specified namespaces.
* `simp_lc inspect`: Investigates one pair
* `simp_lc whitelist`: Whitelists a critical pair
* `simp_lc ignore`: Ignores one lemma

The `SimplcLean` library sets up whitelists and ignores for the core Lean repository,
and checks the simp set. It is run during CI.

To use in a downstream library, add
```toml
[[require]]
name = "simplc"
git = "https://github.com/leanprover/lean4"
rev = "master"
subDir = "tests/simplc"
```
to your `lakefile.toml`, and then use
```lean
import SimplcLean

#guard_msgs (drop info) in
simp_lc check in String Char Float USize UInt64 UInt32 UInt16 UInt8 PLift ULift Prod Sum Range Subtype ByteArray FloatArray
  List Option Array Int Nat Bool Id Monad LawfulMonad LawfulSingleton Std
```
(optionally adding `_root_`), to recheck the simp set on basic data types,
and then add any additional namespaces specific to your library.

