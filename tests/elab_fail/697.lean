inductive Maybe (a : Type) : Type where
| ok: a -> Maybe a
| err: Maybe a

structure P (a: Type) where
   runP: String -> Maybe (String × a)

def ppure {a: Type} (v: a): P a := { runP :=  λ s => Maybe.ok (s, v) }

def pbind {a b: Type} (pa: P a) (a2pb : a -> P b): P b :=
   { runP := λs => match pa.runP s with
            | Maybe.ok (s', a) => (a2pb a).runP  s'
            | Maybe.err => Maybe.err
   }

instance : Monad P := { pure := ppure, bind := pbind }

def pfail : P a := { runP := λ _  => Maybe.err }

instance : Inhabited (P a) where default := pfail


mutual
partial def pregion : P Unit :=  do
  pblock

partial def pop : P Unit := do
  pregion

partial def pblock : P Unit := do
   pop
end

-- partial def foo : Unit :=
--  foo

def main: IO Unit := do
  return ()
