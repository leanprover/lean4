/- Arguments to implicit binders are inserted automatically. It would be nice if *parameters* in the definition of a term of such a type would
   be inserted automatically as well.
   For a good overview over (and one solution to) this topic, see https://github.com/AndrasKovacs/elaboration-zoo/tree/master/experimental/poly-instantiation. -/

-- works
example {m σ} [Alternative m] [Monad m] : Alternative (StateT σ m) :=
{ failure := @StateT.failure _ _ _ _,
  orelse  := @StateT.orelse _ _ _ _,
  .. StateT.Monad }

-- works
example {m σ} [Alternative m] [Monad m] : Alternative (StateT σ m) :=
{ failure := fun α => StateT.failure,
  orelse  := fun α => StateT.orelse,
  .. StateT.Monad }

-- fails
example {m σ} [Alternative m] [Monad m] : Alternative (StateT σ m) :=
{ failure := StateT.failure,
  orelse  := StateT.orelse,
  .. StateT.Monad }

-- works
universes u v
example {m m' σ σ'} {n n' : Type u → Type v} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
⟨fun σ'' α split join => monadMap (fun α => (adaptState split join : m α → m' α))⟩

-- fails
example {m m' σ σ'} {n n' : Type u → Type v} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
⟨fun split join => monadMap (adaptState split join)⟩
