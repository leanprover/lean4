import Lean
/-!
Regression test for #16012: kernel reduction of `String.toList` on a string literal must take time
linear in the length of the literal, and must not exceed the default `maxRecDepth`. Before the fix,
`String.toList` decoded the bytes with `ByteArray.utf8Decode?`, which indexes into an array (about
8 s for 400 characters), and `List.utf8Encode` built the bytes with nested `push` calls.
-/

open Lean Elab Command

/-- `mk_lit n` adds `s : String`, a literal of `n` copies of `a`. -/
elab "mk_lit " n:num : command => do
  let str := String.ofList (List.replicate n.getNat 'a')
  elabCommand (← `(def $(mkIdent `s) : String := $(Syntax.mkStrLit str)))

mk_lit 2000

theorem viaString : s.toList.length = 2000 := by decide +kernel

theorem viaLength : s.length = 2000 := by decide +kernel

theorem viaBytes : s.toByteArray.size = 2000 := by decide +kernel

-- Multi-byte characters (UTF-8 sequences of length 1, 2, 3 and 4)
example : "aé∀𝔸b".toList = ['a', 'é', '∀', '𝔸', 'b'] := by decide +kernel
example : "aé∀𝔸b".toList ≠ ['a', 'é', '∀', '𝔸'] := by decide +kernel
example : "L∃∀N".length = 4 := by decide +kernel

-- The elaborator can still reduce `String.toList`
example : "aé∀𝔸b".toList = ['a', 'é', '∀', '𝔸', 'b'] := by decide
example : "aé∀𝔸b".toList = ['a', 'é', '∀', '𝔸', 'b'] := rfl
example : "".toList = [] := rfl
