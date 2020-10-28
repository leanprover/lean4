

namespace ForIn

inductive Step.{u} (α : Type u)
| done  : α → Step α
| yield : α → Step α

class Fold.{u, v, w, z} (m : Type w → Type z) [Monad m] (α : outParam (Type u)) (s : Type v) : Type (max v u z (w+1)):=
(fold {β : Type w} (as : s) (init : β) (f : α → β → m (Step β)) : m β)

export Fold (fold)

class FoldMap.{u, w} (m : Type u → Type w) [Monad m] (s : Type u → Type u) : Type (max (u+1) w):=
(foldMap {α β : Type u} (as : s α) (init : β) (f : α → β → m (Step (α × β))) : m (s α × β))

export FoldMap (foldMap)

@[inline] instance {m} {α} [Monad m] : Fold m α (List α) :=
{ fold := fun as init f =>
    let rec @[specialize] loop
      | [], b    => pure b
      | a::as, b => do
        let s ← f a b
        (match s with
         | Step.done b     => pure b
         | Step.yield b => loop as b)
    loop as init }

@[inline] instance {m} [Monad m] : FoldMap m List :=
{ foldMap := fun as init f =>
    let rec @[specialize] loop
      | [], rs, b => pure (rs.reverse, b)
      | a::as, rs, b => do
        let s ← f a b
        (match s with
         | Step.done (a, b)     => pure ((a :: rs).reverse ++ as, b)
         | Step.yield (a, b) => loop as (a::rs) b)
    loop as [] init }

def tst1 : IO Nat :=
fold [1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14] 0 fun a b =>
  if a % 2 == 0 then do
    IO.println (">> " ++ toString a ++ " " ++ toString b)
    (if b > 20 then return Step.done b
     else return Step.yield (a+b))
  else
    return Step.yield b

#eval tst1

def tst1' : IO Unit := do
let (as, b) ← foldMap [1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14] 0 fun a b =>
  if a % 2 == 0 then do
    IO.println (">> " ++ toString a ++ " " ++ toString b)
    (if b > 20 then return Step.done (a, b)
     else return Step.yield (a/2, a+b))
  else
    return Step.yield (a, b)
IO.println as
IO.println b
pure ()

#eval tst1'

instance Prod.fold {m α β γ δ} [Monad m] [i₁ : Fold m α γ] [i₂ : Fold m β δ] : Fold m (α × β) (γ × δ) :=
{ fold := fun s init f =>
   Fold.fold s.1 init fun a x => do
     Fold.fold s.2 (Step.yield x) fun b x =>
        match x with
        | Step.done _ => return Step.done x
        | Step.yield x => do
          let s ← f (a, b) x
          (match s with
           | Step.done _     => return Step.done s
           | Step.yield _ => return Step.yield s) }

def tst2 (threshold : Nat) : IO Nat :=
fold ([1, 2, 3, 4, 5, 10], [10, 20, 30, 40, 50]) 0 fun (a, b) s => do
  IO.println (">> " ++ toString a ++ ", " ++ toString b ++ ", " ++ toString s)
  (if s > threshold then return Step.done s
   else return Step.yield (s+a+b))

#eval tst2 170
#eval tst2 800

structure Range :=
(lower upper : Nat)

@[inline] instance Range.fold {m} [Monad m] : Fold m Nat Range :=
{ fold := fun s init f =>
  let base := s.lower + s.upper - 2
  let rec @[specialize] loop : Nat → _ → _
    | 0,   b => pure b
    | i+1, b =>
      let j := base - i
      if j >= s.upper then return b
      else do
        let s ← f j b
        (match s with
         | Step.done b     => return b
         | Step.yield b => loop i b)
  loop (s.upper - 1) init }

@[inline] def range (a : Nat) (b : Option Nat := none) : Range :=
match b with
| none      => ⟨0, a⟩
| some b    => ⟨a, b⟩

instance : OfNat (Option Nat) :=
⟨fun n => some n⟩

def tst3 : IO Nat :=
fold (range 5 10) 0 fun i s => do
  IO.println (">> " ++ toString i)
  return Step.yield (s+i)

#eval tst3

theorem zeroLtOfLt : {a b : Nat} → a < b → 0 < b
| 0,   _, h => h
| a+1, b, h =>
  have a < b from Nat.ltTrans (Nat.ltSuccSelf _) h
  zeroLtOfLt this

@[inline] instance {m} {α} [Monad m] : Fold m α (Array α) :=
{ fold := fun as init f =>
    let rec @[specialize] loop : (i : Nat) → i ≤ as.size → _
      | 0, h, b   => pure b
      | i+1, h, b =>
        have h' : i < as.size          from Nat.ltOfLtOfLe (Nat.ltSuccSelf i) h
        have as.size - 1 < as.size     from Nat.subLt (zeroLtOfLt h') (decide! (0 < 1))
        have as.size - 1 - i < as.size from Nat.ltOfLeOfLt (Nat.subLe (as.size - 1) i) this; do
        let s ← f (as.get ⟨as.size - 1 - i, this⟩) b
        (match s with
         | Step.done b     => pure b
         | Step.yield b => loop i (Nat.leOfLt h') b)
    loop as.size (Nat.leRefl _) init }

-- set_option trace.compiler.ir.result true

def tst4 : IO Nat :=
fold (#[1, 2, 3, 4, 5] : Array Nat) 0 fun a b => do
  IO.println (">> " ++ toString a ++ " " ++ toString b)
  return Step.yield (a+b)

#eval tst4

end ForIn
