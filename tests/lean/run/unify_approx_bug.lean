open tactic

/-
 Given a metavariable ?m with local context

    (α : Type) (a : α)

 then, the following unification problem should fail

   ?m α =?= ((λ (α : Type) (a : α), α) α a)

 type_context will try the type incorrect assignment

    ?m := λ α', ((λ (α : Type) (a : α), α) α' a)
-/
def ex1 (α : Type) (a : α) : Type → Type :=
by
  (do
    mvar1 ← mk_meta_var `(Type → Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```((λ (α : Type) (a : α), α) α a),
    unify (mvar1 alpha) t semireducible tt, -- should fail
    exact mvar1)
  <|>
  (intros >> assumption)

/-
 Given metavariable ?m_1 and ?m_2 with local context

    (α : Type) (a : α)

 then, the following unification constrains should be solved

   ?m_1 α =?= id ?m_2
   ?m_2   =?= α

 After processing the first constraint, we have

   ?m_1 := λ α', id ?m_2[α := α']
   ?m_2 := ?m_3

  where ?m_3 is a fresh metavariable with a local context
  that does not contain `a`, since `a` depends on `α`.

 After processing the second constraint, we have

   ?m_3 := α
-/
def ex2 (α : Type) (a : α) : Type → Type :=
by do
    mvar1 ← mk_meta_var `(Type → Type),
    mvar2 ← mk_meta_var `(Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(id %%mvar2),
    unify (mvar1 alpha) t semireducible tt, -- should create an auxiliary mvar and assign it to mvar2
    unify mvar2 alpha,  -- the local context of the auxiliary declaration does not contain `a`
    exact mvar1

/-
 Given metavariable ?m_1 and ?m_2 with local context

    (α : Type) (a : α)

 then, the following unification constrains should be solved

   ?m_1 α =?= id ?m_2
   ?m_2   =?= ((λ (α : Type) (a : α), α) α a)

 After processing the first constraint, we have

   ?m_1 := λ α', id ?m_2[α := α']
   ?m_2 := ?m_3

  where ?m_3 is a fresh metavariable with a local context
  that does not contain `a`, since `a` depends on `α`.

 When processing the second constraint, it fails
 because it tries to assing `((λ (α : Type) (a : α), α) α a)`
 to `?m_3`, but `a` is not in the context of `?m_3`.
-/
def ex3 (α : Type) (a : α) : Type → Type :=
by (do
    mvar1 ← mk_meta_var `(Type → Type),
    mvar2 ← mk_meta_var `(Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(id %%mvar2),
    unify (mvar1 alpha) t semireducible tt, -- should create an auxiliary mvar and assign it to mvar2
    t     ← to_expr ```((λ (α : Type) (a : α), α) α a),
    unify mvar2 t semireducible tt,  -- should fail `a` is not in the scope
    exact mvar1)
    <|> (intros >> assumption)

def f (α : Type) (a : α) := α

/-
 Given a metavariable ?m with local context

    (α : Type) (a : α)

 then, the following unification problem should fail

   ?m α =?= f α a

 type_context will try the type incorrect assignment

    ?m := λ α', f α' a
-/
def ex4 (α : Type) (a : α) : Type → Type :=
by
  (do
    mvar1 ← mk_meta_var `(Type → Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(f α a),
    unify (mvar1 alpha) t semireducible tt, -- should fail
    exact mvar1)
  <|>
  (intros >> assumption)

/-
 Given a metavariable ?m with local context

    (α : Type) (a : α)

 then, the following unification problem should work

   ?m α a =?= f α a

 type_context assigns

    ?m := λ α' a', f α' a'
-/
def ex5 (α : Type) (a : α) : Π A : Type, A → Type :=
by do
    mvar1 ← mk_meta_var `(Π A : Type, A → Type),
    alpha ← to_expr ```(α),
    a     ← to_expr ```(a),
    t     ← to_expr ```(f α a),
    unify (mvar1 alpha a) t semireducible tt, -- should work
    exact mvar1

/-
 Given metavariable ?m_1 and ?m_2 with local context

    (α : Type) (a : α)

 then, the following unification constrains should be solved

   ?m_1 α =?= id ?m_2
   ?m_2   =?= f α a

 After processing the first constraint, we have

   ?m_1 := λ α', id ?m_2[α := α']
   ?m_2 := ?m_3

  where ?m_3 is a fresh metavariable with a local context
  that does not contain `a`, since `a` depends on `α`.

 When processing the second constraint, it fails
 because it tries to assign `f α a`
 to `?m_3`, but `a` is not in the context of `?m_3`.
-/
def ex6 (α : Type) (a : α) : Type → Type :=
by (do
    mvar1 ← mk_meta_var `(Type → Type),
    mvar2 ← mk_meta_var `(Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(id %%mvar2),
    unify (mvar1 alpha) t semireducible tt, -- should create an auxiliary mvar and assign it to mvar2
    t     ← to_expr ```(f α a),
    unify mvar2 t semireducible tt,  -- should fail `a` is not in the scope
    exact mvar1)
    <|> (intros >> assumption)

def g (α : Type) (a b : α) := α

/-
 Given a metavariable ?m with local context

    (α : Type) (a : α)

 then, the following unification problem should fail

   ?m α =?= g α a a

 type_context will try the type incorrect assignment

    ?m := λ α', g α' a a
-/
def ex7 (α : Type) (a : α) : Type → Type :=
by
  (do
    mvar1 ← mk_meta_var `(Type → Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(g α a a),
    unify (mvar1 alpha) t semireducible tt, -- should fail
    exact mvar1)
  <|>
  (intros >> assumption)

constant C (α : Type) (a : α) : Type

/-
 Given a metavariable ?m with local context

   (α : Type) (a : α) (x : C α a)

 then, the following unification problem should fail

      ?m α x =?= α

 type_context will try the type incorrect assignment

      ?m := λ (α' : Type) (x' : C α' a), α'

  type_context detects the problem when it tries to unify the type of `?m`
  with type of (λ (α' : Type) (x' : C α' a), α')
-/
def ex8 (α : Type) (a : α) (x : C α a) : Type :=
by
  (do
  mvar_type ← to_expr ```(C α a → Type),
  mvar_type ← to_expr ```(Type → %%mvar_type),
  mvar1 ← mk_meta_var mvar_type,
  alpha ← to_expr ```(α),
  x     ← to_expr ```(x),
  unify (mvar1 alpha x) alpha semireducible tt, -- should fail
  exact (mvar1 alpha x))
  <|> assumption

/-
 Given a metavariable ?m with local context

    (α : Type) (a : α)

 then, the following unification problem should work

   ?m α =?= a

 type_context assigns

    ?m := λ α', a

  The point of this example is to make sure
  future modifications to type_context do not
  prevent us from solving valid problems like this one.
-/
def ex9 (α : Type) (a : α) : Type → α :=
by do
    mvar_type ← to_expr ```(Type → α),
    mvar1 ← mk_meta_var mvar_type,
    alpha ← to_expr ```(α),
    t     ← to_expr ```(a),
    unify (mvar1 alpha) t semireducible tt, -- should work
    exact mvar1
