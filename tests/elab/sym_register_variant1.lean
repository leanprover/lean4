import Lean

open Lean Meta Sym.Simp

/-! Tests for `register_sym_simp` command -/

-- Basic variant with pre and post
register_sym_simp testVariant1 where
  pre  := ground
  post := rewrite [Nat.zero_add]

-- Variant with only post
register_sym_simp testVariant2 where
  post := ground >> rewrite [Nat.zero_add, Nat.add_zero]

-- Variant with only pre
register_sym_simp testVariant3 where
  pre := telescope

-- Variant with config overrides
register_sym_simp testVariant4 where
  pre := ground
  post := rewrite [Nat.zero_add]
  maxSteps := 50000
  maxDischargeDepth := 3

-- Variant with discharger
register_sym_simp testVariant5 where
  post := rewrite [Nat.zero_add] with self

-- Variant with combinators
register_sym_simp testVariant6 where
  post := ground >> rewrite [Nat.zero_add] <|> rewrite [Nat.add_zero]

-- Empty variant (no fields)
register_sym_simp testVariantEmpty where

-- Verify variants are registered
#eval show MetaM Unit from do
  let env ← getEnv
  let some v1 := getSymSimpVariant? env `testVariant1 | throwError "testVariant1 not found"
  guard v1.pre?.isSome
  guard v1.post?.isSome
  let some v2 := getSymSimpVariant? env `testVariant2 | throwError "testVariant2 not found"
  guard v2.pre?.isNone
  guard v2.post?.isSome
  let some v3 := getSymSimpVariant? env `testVariant3 | throwError "testVariant3 not found"
  guard v3.pre?.isSome
  guard v3.post?.isNone
  let some v4 := getSymSimpVariant? env `testVariant4 | throwError "testVariant4 not found"
  guard (v4.config.maxSteps == 50000)
  guard (v4.config.maxDischargeDepth == 3)
  let some _ := getSymSimpVariant? env `testVariantEmpty | throwError "testVariantEmpty not found"
  guard (getSymSimpVariant? env `nonExistent |>.isNone)

-- Duplicate field detection
/--
error: duplicate `pre` field
-/
#guard_msgs in
register_sym_simp testBadDuplicate where
  pre := ground
  pre := telescope