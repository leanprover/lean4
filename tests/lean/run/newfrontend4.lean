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

/-
The following fails because we cannot synthesize the instance
```
  [MonadFunctorT
     (λ (β : Type), m  (?m_1 σ'' α split join β))
     (λ (β : Type), m' (?m_1 σ'' α split join β))
     n
     (λ {α : Type}, n' α)]
```
Note that we have an instance `[MonadFunctorT m m' n n']`. The TC procedure performs eta-reduction, and manage to reduce
`(λ {α : Type}, n' α)` to `n'`, but it cannot eta-reduce the arguments
```
     (λ (β : Type), m  (?m_1 σ'' α split join β))
     (λ (β : Type), m' (?m_1 σ'' α split join β))
```
The reduction is blocked by the metavariable applications `(?m_1 σ'' α split join β)`.
Remark: eta-expansion would also not solve the problem. The TC procedure would convert the instance
`[MonadFunctorT m m' n n']`
into
`[MonadFunctorT (fun β => m β) (fun β => m' β) (fun α => n α) (fun α => n' α)]`
but it would fail trying to unify
```
?m_1 σ'' α split join β =?= β
```
since `?m_1` was not created by the TC procedure. It was created by the elaborator.
-/
-- def adapt4 {m m' σ σ'} {n n' : Type → Type} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
-- ⟨fun split join => monadMap (adaptState split join : m _ → m' _)⟩ -- monadMap (adaptState split join : m α → m' α)⟩
