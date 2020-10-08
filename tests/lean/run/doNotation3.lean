new_frontend

theorem zeroLtOfLt : {a b : Nat} → a < b → 0 < b
| 0,   _, h => h
| a+1, b, h =>
  have a < b from Nat.ltTrans (Nat.ltSuccSelf _) h
  zeroLtOfLt this

def fold {m α β} [Monad m] (as : Array α) (b : β) (f : α → β → m β) : m β := do
let rec loop : (i : Nat) → i ≤ as.size → β → m β
  | 0,   h, b => b
  | i+1, h, b => do
    have h' : i < as.size          from Nat.ltOfLtOfLe (Nat.ltSuccSelf i) h
    have as.size - 1 < as.size     from Nat.subLt (zeroLtOfLt h') (decide! (0 < 1))
    have as.size - 1 - i < as.size from Nat.ltOfLeOfLt (Nat.subLe (as.size - 1) i) this
    let b ← f (as.get ⟨as.size - 1 - i, this⟩) b
    loop i (Nat.leOfLt h') b
loop as.size (Nat.leRefl _) b

#eval Id.run $ fold #[1, 2, 3, 4] 0 (pure $ · + ·)

theorem ex : (Id.run $ fold #[1, 2, 3, 4] 0 (pure $ · + ·)) = 10 :=
rfl

def fold2 {m α β} [Monad m] (as : Array α) (b : β) (f : α → β → m β) : m β :=
let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
  match i, h with
  | 0,   h => return b
  | i+1, h =>
    have h' : i < as.size          from Nat.ltOfLtOfLe (Nat.ltSuccSelf i) h
    have as.size - 1 < as.size     from Nat.subLt (zeroLtOfLt h') (decide! (0 < 1))
    have as.size - 1 - i < as.size from Nat.ltOfLeOfLt (Nat.subLe (as.size - 1) i) this
    let b ← f (as.get ⟨as.size - 1 - i, this⟩) b
    loop i (Nat.leOfLt h') b
loop as.size (Nat.leRefl _) b
