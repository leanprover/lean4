import init.lean.expander

open Lean
open Lean.Parser
open Lean.Expander

def prof {α : Type} (msg : String) (p : IO α) : IO α :=
let msg₁ := "Time for '" ++ msg ++ "':" in
let msg₂ := "Memory usage for '" ++ msg ++ "':" in
allocprof msg₂ (timeit msg₁ p)

@[derive HasView] def leaf.Parser : termParser := node! leaf ["foo"]
@[derive HasView] def node.Parser : termParser := node! node [children: Combinators.many Term.Parser]

def node.arity := 4

def mkStx : ℕ → Syntax
| 0 := review leaf {}
| (n+1) := review node $ ⟨(List.replicate node.arity Syntax.missing).map (λ _, mkStx n)⟩

def cfg : FrontendConfig := {filename := "foo", fileMap := FileMap.fromString "", input := ""}

def test (transformers : List (Name × transformer)) (stx : Syntax) : IO Unit :=
match expand stx {cfg with transformers := RBMap.fromList transformers _} with
| Except.ok _ := pure ()
| Except.error e := throw e.toString

def testNoOp  := test []
def testNoExp := test [(`node, λ stx, noExpansion)]
def testSimple := test [(`node, λ stx, pure $ Syntax.mkNode ⟨`node2⟩ $ let v := view node stx in v.children)]

def main (xs : List String) : IO Unit := do
  let stx := mkStx 11, --xs.head.toNat,
  prof "testNoOp" $ testNoOp stx,
  prof "testNoExp" $ testNoExp stx,
  prof "testSimple" $ testSimple stx,
  pure ()
