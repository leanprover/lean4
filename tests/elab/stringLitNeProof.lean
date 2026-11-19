import Lean
/-!
Tests `mkStringLitNeProof`: the proofs are checked by the kernel against the inequality between
the two `String` literals.
-/
open Lean Meta

def checkNe (s₁ s₂ : String) : MetaM Unit := do
  let proof ← mkStringLitNeProof s₁ s₂
  let type := mkApp3 (mkConst ``Ne [1]) (mkConst ``String) (mkStrLit s₁) (mkStrLit s₂)
  check proof
  unless (← isDefEq (← inferType proof) type) do
    throwError "unexpected type for {s₁.quote} ≠ {s₂.quote}"
  let decl := .thmDecl { name := `test, levelParams := [], type, value := proof }
  match (← getEnv).toKernelEnv.addDecl (← getOptions) decl with
  | .ok _ => pure ()
  | .error e => throwError "kernel rejected {s₁.quote} ≠ {s₂.quote}: {e.toMessageData (← getOptions)}"

run_meta do
  let long := String.ofList (List.replicate 300 'a')
  for (s₁, s₂) in [
      -- Different character
      ("a", "b"), ("abc", "abd"), ("abc", "xbc"), ("abcd", "abxde"),
      ("registered_name_17", "registered_name_18"), (long ++ "b", long ++ "c"),
      -- One is a prefix of the other
      ("", "a"), ("a", ""), ("abc", "abcd"), ("abcd", "abc"), (long, long ++ "b"),
      -- The character `'\x00'`
      ("a", "a\x00"), ("a\x00", "a"), ("\x00", "\x01"),
      -- Non-ASCII characters
      ("é", "ê"), ("é😀b", "é😀c"), ("😀", "😁"), ("é", "é😀")] do
    checkNe s₁ s₂
