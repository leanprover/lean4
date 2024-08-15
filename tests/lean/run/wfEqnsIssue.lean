def HList (αs : List (Type u)) : Type u := αs.foldr Prod.{u, u} PUnit

@[match_pattern] def HList.nil : HList [] := ⟨⟩
@[match_pattern] def HList.cons (a : α) (as : HList αs): HList (α :: αs) := (a, as)

def HList.set : {αs : _} → HList αs → (i : Fin αs.length) → αs.get i → HList αs
  | _ :: _, cons a as, ⟨0,          h⟩, b => cons b as
  | _ :: _, cons a as, ⟨Nat.succ n, h⟩, b => cons a (set as ⟨n, Nat.le_of_succ_le_succ h⟩ b)
  | [],     nil,       _,               _ => nil

instance : EmptyCollection (HList ∅) where
  emptyCollection := HList.nil

notation:30 Γ " ⊢ " α => HList Γ → α

-- simplify well-founded recursion proofs by ignoring context sizes
local instance : SizeOf (List α) := ⟨fun _ => 0⟩ in

-- m: base monad
-- ω: `return` type, `m ω` is the type of the entire `do` block
-- Γ: `do`-local immutable context
-- Δ: `do`-local mutable context
-- b: `break` allowed
-- c: `continue` allowed
-- α: local result type, `m α` is the type of the statement
inductive Stmt (m : Type u → Type _) (ω : Type u) : (Γ Δ : List (Type u)) → (b c : Bool) → (α : Type u) → Type _ where
  | expr (e : Γ ⊢ Δ ⊢ m α) : Stmt m ω Γ Δ b c α
  | bind (s₁ : Stmt m ω Γ Δ b c α) (s₂ : Stmt m ω (α :: Γ) Δ b c β) : Stmt m ω Γ Δ b c β
  | letmut (e : Γ ⊢ Δ ⊢ α) (s : Stmt m ω Γ (α :: Δ) b c β) : Stmt m ω Γ Δ b c β
  | ass (x : Fin Δ.length) (e : Γ ⊢ Δ ⊢ Δ.get x) : Stmt m ω Γ Δ b c PUnit
  | ite (e : Γ ⊢ Δ ⊢ Bool) (s₁ s₂ : Stmt m ω Γ Δ b c α) : Stmt m ω Γ Δ b c α
  | ret (e : Γ ⊢ Δ ⊢ ω) : Stmt m ω Γ Δ b c α
  --| sfor [ForM m γ α] (e : Σ Γ → γ) (body : α → Stmt m ω Γ Δ true PUnit) : Stmt m ω Γ Δ b c PUnit
  | sfor (e : Γ ⊢ Δ ⊢ List α) (body : Stmt m ω (α :: Γ) Δ true true PUnit) : Stmt m ω Γ Δ b c PUnit
  | sbreak : Stmt m ω Γ Δ true c α
  | scont : Stmt m ω Γ Δ b true α

-- normal and abnormal result values
inductive Res (ω α : Type _) : (b c : Bool) → Type _ where
  | val (a : α) : Res ω α b c
  | ret (o : ω) : Res ω α b c
  | rbreak : Res ω α true c
  | rcont : Res ω α b true

instance : Coe α (Res ω α b c) := ⟨Res.val⟩
instance : Coe (Id α) (Res ω α b c) := ⟨Res.val⟩

def Ctx.extendBot (x : α) : {Γ : _} → HList Γ → HList (Γ ++ [α])
  | [],     _               => HList.cons x HList.nil
  | _ :: _, HList.cons a as => HList.cons a (extendBot x as)

def Ctx.extend (x : α) : HList Γ → HList (α :: Γ) :=
  fun σ => HList.cons x σ

def Ctx.drop : HList (α :: Γ) → HList Γ
  | HList.cons a as => as

@[simp]
def Stmt.mapCtx (f : HList Γ' → HList Γ) : Stmt m ω Γ Δ b c β → Stmt m ω Γ' Δ b c β
  | expr e => expr (e ∘ f)
  | bind s₁ s₂ => bind (s₁.mapCtx f) (s₂.mapCtx (fun | HList.cons a as => HList.cons a (f as)))
  | letmut e s => letmut (e ∘ f) (s.mapCtx f)
  | ass x e => ass x (e ∘ f)
  | ite e s₁ s₂ => ite (e ∘ f) (s₁.mapCtx f) (s₂.mapCtx f)
  | ret e => ret (e ∘ f)
  | sfor e body => sfor (e ∘ f) (body.mapCtx (fun | HList.cons a as => HList.cons a (f as)))
  | sbreak => sbreak
  | scont => scont
termination_by s => sizeOf s
