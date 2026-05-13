/-! This file tests semantic token kinds. -/

universe u

inductive SemanticTokenData where
  | atom : SemanticTokenData

inductive SemanticTokenProp (A : Type u) : A → Prop where
  | intro (a : A) : SemanticTokenProp A a

structure SemanticTokenStruct where
  field : Nat

class SemanticTokenInterface (A : Type u) where
  op : A → A

def SemanticTokenFamily (A : Type u) : Type u := List A

def SemanticTokenPredicate (A : Type u) (a : A) : Prop := a = a

def semanticTokenValue : Nat := 1

def semanticTokenRecursive : Nat → Nat
  | 0 => 0
  | n + 1 => semanticTokenRecursive n

theorem semanticTokenProof (A : Type u) (a : A) : SemanticTokenPredicate A a := rfl

def semanticTokenUse (A : Type u) [SemanticTokenInterface A] (a : A)
    (h : SemanticTokenProp A a) : SemanticTokenFamily Nat :=
  let s : SemanticTokenStruct := { field := semanticTokenValue }
  let d : SemanticTokenData := SemanticTokenData.atom
  let p : SemanticTokenPredicate A a := semanticTokenProof A a
  let q : SemanticTokenProp A a := h
  match d with
  | .atom =>
    let _ : SemanticTokenPredicate A a := p
    let _ : SemanticTokenProp A a := q
    List.cons s.field List.nil

def foo1 (x : Nat) := x.succ
def foo2 (x : Nat) := x |>.succ
theorem foo3 (x : Nat) : True :=
  let y := x.succ
  have : y = y := rfl
  True.intro

#eval 1
--^ collectDiagnostics
--^ textDocument/semanticTokens/full
