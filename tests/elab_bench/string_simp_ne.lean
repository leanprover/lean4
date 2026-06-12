import Lean

/-!
Benchmark: String equality/inequality simproc kernel efficiency.

Tests `simp` on string literal (in)equality for various string lengths.
The kernel verifies proof terms from `String.reduceEq`/`String.reduceNe`.

Key variables:
- String length: affects `String.ofList` kernel evaluation (unavoidable O(n))
- Position of first difference: with the `congrArg List.get?Internal` optimization,
  the inequality proof cost is O(first_diff_pos) instead of O(string_length)
-/

set_option Elab.async false
set_option maxHeartbeats 8000000

open Lean Elab Command in
/-- Generate `example : s₁ ≠ s₂ := by simp` where s₁ = n×'a'++"x" and s₂ = n×'a'++"y". -/
elab "#bench_string_ne_suffix " n:num : command => do
  let n := n.getNat
  let pfx := String.ofList (List.replicate n 'a')
  let s1 := pfx ++ "x"
  let s2 := pfx ++ "y"
  elabCommand (← `(#time example : ($(Syntax.mkStrLit s1) : String) ≠ ($(Syntax.mkStrLit s2) : String) := by simp))

open Lean Elab Command in
/-- Generate `example : s₁ ≠ s₂ := by simp` where s₁ = "x"++n×'a' and s₂ = "y"++n×'a'.
    Strings differ at the first character — tests O(1) inequality proof. -/
elab "#bench_string_ne_prefix " n:num : command => do
  let n := n.getNat
  let sfx := String.ofList (List.replicate n 'a')
  let s1 := "x" ++ sfx
  let s2 := "y" ++ sfx
  elabCommand (← `(#time example : ($(Syntax.mkStrLit s1) : String) ≠ ($(Syntax.mkStrLit s2) : String) := by simp))

open Lean Elab Command in
/-- Generate `example : s = s := by simp` with s = n×'a'. -/
elab "#bench_string_eq " n:num : command => do
  let n := n.getNat
  let s := String.ofList (List.replicate n 'a')
  elabCommand (← `(#time example : ($(Syntax.mkStrLit s) : String) = ($(Syntax.mkStrLit s) : String) := by simp))

-- Ne: shared prefix of increasing length (differ at last character)
-- Tests scaling of the full proof pipeline
#bench_string_ne_suffix 0
#bench_string_ne_suffix 10
#bench_string_ne_suffix 100
#bench_string_ne_suffix 500
#bench_string_ne_suffix 1000
#bench_string_ne_suffix 2000

-- Ne: long strings that differ at the first character
-- The congrArg optimization makes the inequality proof O(1);
-- remaining cost is String.ofList kernel verification
#bench_string_ne_prefix 1000
#bench_string_ne_prefix 2000

-- Eq: identical strings of increasing length (constant time with eq_true rfl)
#bench_string_eq 10
#bench_string_eq 500
#bench_string_eq 2000
