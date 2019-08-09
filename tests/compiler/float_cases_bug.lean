inductive Term : Type
| const : Nat -> Term
| app   : List Term -> Term

namespace Term
instance : Inhabited Term := ⟨Term.const 0⟩
partial def hasToString : Term -> String | const n   => "CONST(" ++ toString n ++ ")" | app ts    => "APP"
instance : HasToString Term := ⟨hasToString⟩
end Term

open Term

structure MyState : Type := (ts : List Term)
def emit (t : Term) : State MyState Unit := modify (λ ms => ⟨t::ms.ts⟩)

partial def foo : MyState -> Term -> Term -> List Term
| ms₀, t, u =>
  let stateT : State MyState Unit := do {

    match t with
    | const _  => pure ()
    | app _   => emit (const 1) *> pure () ;

    match t, u with
    | app _,  app _   => emit (app []) *> pure ()
    | _, _ => pure () ;

    match t, u with
    | app _,  app _   => emit (app []) *> pure ()
    | _, _ => emit (const 2) *> pure ()

  } ;

  (stateT.run ⟨[]⟩).2.ts.reverse

def main : IO Unit := IO.println $ foo ⟨[]⟩ (app []) (app [])
