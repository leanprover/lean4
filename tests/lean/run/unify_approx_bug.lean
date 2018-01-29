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
by do
  fail_if_success
  (do
    mvar1 ← mk_meta_var `(Type → Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```((λ (α : Type) (a : α), α) α a),
    unify (mvar1 alpha) t semireducible tt, -- should fail
    exact mvar1),
  intros, assumption

/-
 Given metavariable ?m_1 and ?m_2 with local context

    (α : Type) (a : α)

 then, the following unification constrains should be solved

   ?m_1 α =?= id ?m_2
   ?m_2   =?= α

 The first constraint is solved using first-order unification
 because we cannot guarantee that the solution will be type correct
 for every term we may assign to `?m_2`

    ?m_1 := λ α', id ?m_2[α := α']

 So, we get `?m_2 := α`.

 Remark: see option c) at workaround A2 described at type_context::process_assignment
-/
def ex2 (α : Type) (a : α) : Type → Type :=
by do
    mvar1 ← mk_meta_var `(Type → Type),
    mvar2 ← mk_meta_var `(Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(id %%mvar2),
    unify (mvar1 alpha) t semireducible tt, -- first-order unification is used here
    unify mvar2 alpha,
    exact mvar1

/-
 Given metavariable ?m_1 and ?m_2 with local context

    (α : Type) (a : α)

 then, the following unification constrains should be solved

   ?m_1 α =?= id ?m_2
   ?m_2   =?= ((λ (α : Type) (a : α), α) α a)

 Again, similarly to the previous example, we use
 first-order unification to process the first constraint,
 and we get `?m_2 := α`. The second constraint
 is satisfied because `((λ (α : Type) (a : α), α) α a)`
 is definitionally equal to `α`.
-/
def ex3 (α : Type) (a : α) : Type → Type :=
by do
    mvar1 ← mk_meta_var `(Type → Type),
    mvar2 ← mk_meta_var `(Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(id %%mvar2),
    unify (mvar1 alpha) t semireducible tt, -- should create an auxiliary mvar and assign it to mvar2
    t     ← to_expr ```((λ (α : Type) (a : α), α) α a),
    unify mvar2 t semireducible tt,  -- should fail `a` is not in the scope
    exact mvar1

def f (α : Type) (a : α) := α

constant f' (α : Type) (a : α) : Type

/-
 Given a metavariable ?m with local context

    (α : Type) (a : α)

 then, the following unification problem should fail

   ?m α =?= f α a

 type_context will try the type incorrect assignment

    ?m := λ α', f α' a
-/
def ex4 (α : Type) (a : α) : Type → Type :=
by do
  fail_if_success
  (do
    mvar1 ← mk_meta_var `(Type → Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(f α a),
    unify (mvar1 alpha) t semireducible tt, -- should fail
    exact mvar1),
  intros, assumption

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

def ex5b (α : Type) (a : α) : Π A : Type, A → Type :=
by do
    mvar1 ← mk_meta_var `(Π A : Type, A → Type),
    alpha ← to_expr ```(α),
    a     ← to_expr ```(a),
    t     ← to_expr ```(f' α a),
    unify (mvar1 alpha a) t semireducible tt, -- should work
    exact mvar1

/-
 Given metavariable ?m_1 and ?m_2 with local context

    (α : Type) (a : α)

 then, the following unification constrains should be solved

   ?m_1 α =?= id ?m_2
   ?m_2   =?= f α a

 The first constraint is solved using first-order unification.
 See option c) at workaround A2 described at type_context::process_assignment.
 Then, we get `?m_2 := α`. The second constraint succeeds
 because `f α a` is definitionally equal to `α`.
-/
def ex6 (α : Type) (a : α) : Type → Type :=
by do mvar1 ← mk_meta_var `(Type → Type),
    mvar2 ← mk_meta_var `(Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(id %%mvar2),
    unify (mvar1 alpha) t semireducible tt,
    t     ← to_expr ```(f α a),
    unify mvar2 t semireducible tt,
    exact mvar1

/-
 Given metavariable ?m_1 and ?m_2 with local context

    (α : Type) (a : α)

 then, the following unification constrains should be solved

   ?m_1 α =?= id ?m_2
   ?m_2   =?= f' α a

  Similar to previous example, but this one fails because
  `f' α a` is not definitionally equal to `α`.
-/
def ex6b (α : Type) (a : α) : Type → Type :=
by do
   fail_if_success
      (do mvar1 ← mk_meta_var `(Type → Type),
          mvar2 ← mk_meta_var `(Type),
          alpha ← to_expr ```(α),
          t     ← to_expr ```(id %%mvar2),
          unify (mvar1 alpha) t semireducible tt,
          t     ← to_expr ```(f' α a),
          unify mvar2 t semireducible tt,
          exact mvar1),
   intros, assumption

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
by do
  fail_if_success
  (do
    mvar1 ← mk_meta_var `(Type → Type),
    alpha ← to_expr ```(α),
    t     ← to_expr ```(g α a a),
    unify (mvar1 alpha) t semireducible tt, -- should fail
    exact mvar1),
  intros, assumption

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
by do
  fail_if_success
    (do
      mvar_type ← to_expr ```(C α a → Type),
      mvar_type ← to_expr ```(Type → %%mvar_type),
      mvar1 ← mk_meta_var mvar_type,
      alpha ← to_expr ```(α),
      x     ← to_expr ```(x),
      unify (mvar1 alpha x) alpha semireducible tt, -- should fail
      exact (mvar1 alpha x)),
  assumption

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
