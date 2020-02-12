new_frontend

-- set_option syntaxMaxDepth 100
-- set_option trace.Elab true
-- set_option trace.Meta true
-- set_option trace.Meta.synthInstance false

def adapt1 {m m' σ σ'} {n n' : Type → Type} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
⟨fun split join => monadMap @(fun α => adaptState split join : forall (α : Type), m α → m' α)⟩ -- monadMap (adaptState split join : m α → m' α)⟩

def adapt2 {m m' σ σ'} {n n' : Type → Type} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
⟨fun split join => monadMap @(fun α => (adaptState split join : m α → m' α))⟩ -- monadMap (adaptState split join : m α → m' α)⟩

def adapt3 {m m' σ σ'} {n n' : Type → Type} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
⟨fun split join => monadMap (m:=m) (m':=m') (adaptState split join)⟩

-- TODO:
-- def adapt4 {m m' σ σ'} {n n' : Type → Type} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
-- ⟨fun split join => monadMap (adaptState split join : m _ → m' _)⟩ -- monadMap (adaptState split join : m α → m' α)⟩
