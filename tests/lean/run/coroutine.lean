universes u v w r s

inductive coroutineResultCore (coroutine : Type (max u v w)) (α : Type u) (δ : Type v) (β : Type w) : Type (max u v w)
| done     {} : β → coroutineResultCore
| yielded {}  : δ → coroutine → coroutineResultCore

/--
   Asymmetric coroutines `coroutine α δ β` takes inputs of Type `α`, yields elements of Type `δ`,
   and produces an element of Type `β`.

   Asymmetric coroutines are so called because they involve two types of control transfer operations:
   one for resuming/invoking a coroutine and one for suspending it, the latter returning
   control to the coroutine invoker. An asymmetric coroutine can be regarded as subordinate
   to its caller, the relationship between them being similar to that between a called and
   a calling routine.
 -/
inductive coroutine (α : Type u) (δ : Type v) (β : Type w) : Type (max u v w)
| mk    {} : (α → coroutineResultCore coroutine α δ β) → coroutine

abbreviation coroutineResult (α : Type u) (δ : Type v) (β : Type w) : Type (max u v w) :=
coroutineResultCore (coroutine α δ β) α δ β

namespace coroutine
variables {α : Type u} {δ : Type v} {β γ : Type w}

export coroutineResultCore (done yielded)

/-- `resume c a` resumes/invokes the coroutine `c` with input `a`. -/
@[inline] def resume : coroutine α δ β → α → coroutineResult α δ β
| (mk k) a := k a

@[inline] protected def pure (b : β) : coroutine α δ β :=
mk $ λ _, done b

/-- Read the input argument passed to the coroutine.
    Remark: should we use a different Name? I added an instance [MonadReader] later. -/
@[inline] protected def read : coroutine α δ α :=
mk $ λ a, done a

/-- Run nested coroutine with transformed input argument. Like `ReaderT.adapt`, but
    cannot change the input Type. -/
@[inline] protected def adapt (f : α → α) (c : coroutine α δ β) : coroutine α δ β :=
mk $ λ a, c.resume (f a)

/-- Return the control to the invoker with Result `d` -/
@[inline] protected def yield (d : δ) : coroutine α δ PUnit :=
mk $ λ a : α, yielded d (coroutine.pure ⟨⟩)

/-
TODO(Leo): following relations have been commented because Lean4 is currently
accepting non-terminating programs.

/-- Auxiliary relation for showing that bind/pipe terminate -/
inductive directSubcoroutine : coroutine α δ β → coroutine α δ β → Prop
| mk : ∀ (k : α → coroutineResult α δ β) (a : α) (d : δ) (c : coroutine α δ β), k a = yielded d c → directSubcoroutine c (mk k)

theorem directSubcoroutineWf : WellFounded (@directSubcoroutine α δ β) :=
begin
  Constructor, intro c,
  apply @coroutine.ind _ _ _
          (λ c, Acc directSubcoroutine c)
          (λ r, ∀ (d : δ) (c : coroutine α δ β), r = yielded d c → Acc directSubcoroutine c),
  { intros k ih, dsimp at ih, Constructor, intros c' h, cases h, apply ih hA hD, assumption },
  { intros, contradiction },
  { intros d c ih d₁ c₁ Heq, injection Heq, subst c, assumption }
end

/-- Transitive closure of directSubcoroutine. It is not used here, but may be useful when defining
    more complex procedures. -/
def subcoroutine : coroutine α δ β → coroutine α δ β → Prop :=
Tc directSubcoroutine

theorem subcoroutineWf : WellFounded (@subcoroutine α δ β) :=
Tc.wf directSubcoroutineWf

-- Local instances for proving termination by well founded relation

def bindWfInst : HasWellFounded (Σ' a : coroutine α δ β, (β → coroutine α δ γ)) :=
{ r  := Psigma.Lex directSubcoroutine (λ _, emptyRelation),
  wf := Psigma.lexWf directSubcoroutineWf (λ _, emptyWf) }

def pipeWfInst : HasWellFounded (Σ' a : coroutine α δ β, coroutine δ γ β) :=
{ r  := Psigma.Lex directSubcoroutine (λ _, emptyRelation),
  wf := Psigma.lexWf directSubcoroutineWf (λ _, emptyWf) }

local attribute [instance] wfInst₁ wfInst₂

open wellFoundedTactics

-/

/- TODO: remove `unsafe` keyword after we restore well-founded recursion -/

@[inlineIfReduce] protected unsafe def bind : coroutine α δ β → (β → coroutine α δ γ) → coroutine α δ γ
| (mk k) f := mk $ λ a,
    match k a, rfl : ∀ (n : _), n = k a → _ with
    | done b, _      := coroutine.resume (f b) a
    | yielded d c, h :=
      -- have directSubcoroutine c (mk k), { apply directSubcoroutine.mk k a d, rw h },
      yielded d (bind c f)
--  usingWellFounded { decTac := unfoldWfRel >> processLex (tactic.assumption) }

unsafe def pipe : coroutine α δ β → coroutine δ γ β → coroutine α γ β
| (mk k₁) (mk k₂) := mk $ λ a,
  match k₁ a, rfl : ∀ (n : _), n = k₁ a → _ with
  | done b, h        := done b
  | yielded d k₁', h :=
    match k₂ d with
    | done b        := done b
    | yielded r k₂' :=
      -- have directSubcoroutine k₁' (mk k₁), { apply directSubcoroutine.mk k₁ a d, rw h },
      yielded r (pipe k₁' k₂')
-- usingWellFounded { decTac := unfoldWfRel >> processLex (tactic.assumption) }

private unsafe def finishAux (f : δ → α) : coroutine α δ β → α → List δ → List δ × β
| (mk k) a ds :=
  match k a with
  | done b       := (ds.reverse, b)
  | yielded d k' := finishAux k' (f d) (d::ds)

/-- Run a coroutine to completion, feeding back yielded items after transforming them with `f`. -/
unsafe def finish (f : δ → α) : coroutine α δ β → α → List δ × β :=
λ k a, finishAux f k a []

unsafe instance : Monad (coroutine α δ) :=
{ pure := @coroutine.pure _ _,
  bind := @coroutine.bind _ _ }

unsafe instance : MonadReader α (coroutine α δ) :=
{ read := @coroutine.read _ _ }

end coroutine

/-- Auxiliary class for lifiting `yield` -/
class monadCoroutine (α : outParam (Type u)) (δ : outParam (Type v)) (m : Type w → Type r) :=
(yield {} : δ → m PUnit)

instance (α : Type u) (δ : Type v) : monadCoroutine α δ (coroutine α δ) :=
{ yield  := coroutine.yield }

instance monadCoroutineTrans (α : Type u) (δ : Type v) (m : Type w → Type r) (n : Type w → Type s)
                               [HasMonadLift m n] [monadCoroutine α δ m] : monadCoroutine α δ n :=
{ yield := λ d, monadLift (monadCoroutine.yield d : m _) }

export monadCoroutine (yield)

open coroutine

namespace ex1

inductive tree (α : Type u)
| leaf {} : tree
| Node    : tree → α → tree → tree

/-- Coroutine as generators/iterators -/
unsafe def visit {α : Type v} : tree α → coroutine Unit α Unit
| tree.leaf         := pure ()
| (tree.Node l a r) := do
  visit l;
  yield a;
  visit r

unsafe def tst {α : Type} [HasToString α] (t : tree α) : ExceptT String IO Unit :=
do c  ← pure $ visit t;
   (yielded v₁ c) ← pure $ resume c ();
   (yielded v₂ c) ← pure $ resume c ();
   IO.println $ toString v₁;
   IO.println $ toString v₂;
   pure ()

-- #eval tst (tree.Node (tree.Node (tree.Node tree.leaf 5 tree.leaf) 10 (tree.Node tree.leaf 20 tree.leaf)) 30 tree.leaf)

end ex1

namespace ex2

unsafe def ex : StateT Nat (coroutine Nat String) Unit :=
do
  x ← read;
  y ← get;
  set (y+5);
  yield ("1) val: " ++ toString (x+y));
  x ← read;
  y ← get;
  yield ("2) val: " ++ toString (x+y));
  pure ()

unsafe def tst2 : ExceptT String IO Unit :=
do let c := StateT.run ex 5;
   (yielded r c₁) ← pure $ resume c 10;
   IO.println r;
   (yielded r c₂) ← pure $ resume c₁ 20;
   IO.println r;
   (done _) ← pure $ resume c₂ 30;
   (yielded r c₃) ← pure $ resume c₁ 100;
   IO.println r;
   IO.println "done";
   pure ()

-- #eval tst2

end ex2
