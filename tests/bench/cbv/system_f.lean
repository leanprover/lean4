import Lean

/-!
# System F - Ported from Coq/Rocq

This file is a translation of the Rocq case study from:

  *Definitional Proof Irrelevance Made Accessible*
  Thiago Felicissimo, Yann Leray, Loïc Pujet, Nicolas Tabareau, Éric Tanter,
  Théo Winterhalter

Used with permission of the authors.

It contains a formalization of System F, including substitution lemmas,
confluence of λ-calculus, and strong normalization proofs.
-/


/-- Binary trees with binders (using de Bruijn indices).
    The parameter `A` is a phantom type allowing different notations
    for λ-terms vs System F types. -/
inductive MakeTree (A : Type) : Type where
  | Leaf : Nat → MakeTree A
  | Bind : MakeTree A → MakeTree A
  | Node : MakeTree A → MakeTree A → MakeTree A
deriving Repr, DecidableEq

namespace MakeTree

variable {A : Type}

/-!
## Shifting

`shift d t` increases every free variable of `t` which has an
index >= `d`. This is used in the definition of substitution.
-/

/-- Shift free variables with index >= d by 1 -/
def shift (depth : Nat) : MakeTree A → MakeTree A
  | Leaf n => if depth ≤ n then Leaf (n + 1) else Leaf n
  | Bind t => Bind (shift (depth + 1) t)
  | Node t1 t2 => Node (shift depth t1) (shift depth t2)

-- Notation: we'll use ↑ for shift
scoped notation "↑[" d "]" t => shift d t

@[simp, grind =]
theorem shift_leaf_ge {d n : Nat} (h : n ≥ d) : shift d (Leaf n : MakeTree A) = Leaf (n + 1) := by
  grind [shift]

@[simp, grind =]
theorem shift_leaf_lt {d n : Nat} (h : n < d) : shift d (Leaf n : MakeTree A) = Leaf n := by
  grind [shift]

@[simp, grind =]
theorem shift_bind (d : Nat) (t : MakeTree A) : shift d (Bind t) = Bind (shift (d + 1) t) := rfl

@[simp, grind =]
theorem shift_node (d : Nat) (t t' : MakeTree A) : shift d (Node t t') = Node (shift d t) (shift d t') := rfl

/-- Shifting commutes in a specific way
    Coq: `shift_shift : forall (d d' : nat) (t : Tree), d' <= d -> ↑d'(↑d t) = ↑(S d)(↑d' t)` -/
@[grind _=_]
theorem shift_shift {d d' : Nat} (t : MakeTree A) (h : d' ≤ d) :
    shift d' (shift d t) = shift (d + 1) (shift d' t) := by
  induction t generalizing d d' <;> grind

/-!
## Substitution

`substitute n t t'` substitutes `t'` for the free variable of
index `n` in `t`, and decreases all free variables of `t`
which have an index > `n`.
-/

/-- Substitute t' for variable n in tree, decreasing variables > n -/
def substitute (n : Nat) (tree : MakeTree A) (tree' : MakeTree A) : MakeTree A :=
  match tree with
  | Leaf m =>
    if m = n then tree'
    else if m > n then Leaf (m - 1)
    else Leaf m
  | Bind t => Bind (substitute (n + 1) t (shift 0 tree'))
  | Node t1 t2 => Node (substitute n t1 tree') (substitute n t2 tree')

-- Notation for substitution
scoped notation t "[" n " ↦ " u "]" => substitute n t u

@[simp, grind =]
theorem substitute_leaf_eq (n : Nat) (t : MakeTree A) : substitute n (Leaf n) t = t := by
  grind [substitute]

@[simp, grind =]
theorem substitute_leaf_gt {n m : Nat} (t : MakeTree A) (h : m > n) :
    substitute n (Leaf m) t = Leaf (m - 1) := by
  grind [substitute]

@[simp, grind =]
theorem substitute_leaf_lt {n m : Nat} (t : MakeTree A) (h : m < n) :
    substitute n (Leaf m) t = Leaf m := by
  grind [substitute]

@[simp, grind =]
theorem substitute_bind (n : Nat) (t t' : MakeTree A) :
    substitute n (Bind t) t' = Bind (substitute (n + 1) t (shift 0 t')) := rfl

@[simp, grind =]
theorem substitute_node (n : Nat) (t1 t2 t' : MakeTree A) :
    substitute n (Node t1 t2) t' = Node (substitute n t1 t') (substitute n t2 t') := rfl

/-! ### Interaction between shift and substitute

Coq:
```
Lemma shift_substitute1 : forall (n d : nat) (t t' : Tree),
  d <= n -> (↑d t)[S n↦↑d t'] = ↑d (t[n↦t']).

Lemma shift_substitute2 : forall (n d : nat) (t t' : Tree),
  d >= n -> (↑(S d) t)[n↦↑d t'] = ↑d(t[n↦t']).

Lemma shift_substitute3 : forall (d : nat) (t t' : Tree),
  (↑d t)[d↦t'] = t.
```
-/

/-- Shifting a term and then substituting at a shifted position cancels out -/
@[grind =]
theorem shift_substitute3 (d : Nat) (t t' : MakeTree A) :
    substitute d (shift d t) t' = t := by
  induction t generalizing d t' <;> grind

/-- First shift-substitute interaction lemma -/
@[grind =]
theorem shift_substitute1 {n d : Nat} (t t' : MakeTree A) (h : d ≤ n) :
    substitute (n + 1) (shift d t) (shift d t') = shift d (substitute n t t') := by
  induction t generalizing n d t' <;> grind [shift, substitute]

/-- Second shift-substitute interaction lemma -/
@[grind =]
theorem shift_substitute2 {n d : Nat} (t t' : MakeTree A) (h : d ≥ n) :
    substitute n (shift (d + 1) t) (shift d t') = shift d (substitute n t t') := by
  induction t generalizing n d t' <;> grind

/-! ### Substitution composition

Coq:
```
Lemma substitute_substitute : forall (n n' : nat) (t t' t'' : Tree),
  n <= n' -> t[n↦t'][n'↦t''] = t[S n'↦↑n t''][n↦t'[n'↦t''] ].
```
-/

/-- Substitution composition lemma -/
theorem substitute_substitute {n n' : Nat} (t t' t'' : MakeTree A) (h : n ≤ n') :
    substitute n' (substitute n t t') t'' =
    substitute n (substitute (n' + 1) t (shift n t'')) (substitute n' t' t'') := by
  induction t generalizing n n' t' t'' <;> grind [substitute]

/-! ### Free variables

Coq:
```
Fixpoint free_var (tree : Tree) :=
  match tree with
    | Leaf n => S n
    | Bind t => pred (free_var t)
    | Node t1 t2 => max (free_var t1) (free_var t2)
  end.
```

`freeVar t` returns the least index n such that every free variable
appearing in `t` has index < n.
-/

/-- Returns the least upper bound on free variable indices (plus one) -/
def freeVar : MakeTree A → Nat
  | Leaf n => n + 1
  | Bind t => (freeVar t) - 1
  | Node t1 t2 => max (freeVar t1) (freeVar t2)

@[simp, grind =]
theorem freeVar_leaf (n : Nat) : freeVar (Leaf n : MakeTree A) = n + 1 := rfl

@[simp, grind =]
theorem freeVar_bind (t : MakeTree A) : freeVar (Bind t) = freeVar t - 1 := rfl

@[simp, grind =]
theorem freeVar_node (t1 t2 : MakeTree A) : freeVar (Node t1 t2) = max (freeVar t1) (freeVar t2) := rfl

/-- If d >= freeVar t, then shifting by d doesn't change t -/
@[grind =]
theorem shift_freeVar (t : MakeTree A) (d : Nat) (h : d ≥ freeVar t) :
    shift d t = t := by
  induction t generalizing d <;> grind [shift]

/-- If n >= freeVar t, then substituting for variable n doesn't change t -/
@[grind =]
theorem substitute_freeVar (t : MakeTree A) (n : Nat) (t' : MakeTree A) (h : n ≥ freeVar t) :
    substitute n t t' = t := by
  induction t generalizing n t' <;> grind

/-- Coq: Lemma id_substitute_shift_substitute : forall (t : Tree) (n p : nat),
      n >= free_var t -> (↑p (t[p↦#n]))[S n↦#p] = t.
    This states that substitution of a big enough variable can be reverted. -/
@[grind =]
theorem id_substitute_shift_substitute (t : MakeTree A) (n p : Nat) (h : n ≥ freeVar t) :
    substitute (n + 1) (shift p (substitute p t (Leaf n))) (Leaf p) = t := by
  induction t generalizing n p <;> grind

/-!
## Shift List (Parallel Shifting)

Coq:
```
Definition shift_list (depth : nat) (trees : list Tree) : list Tree :=
  map (fun tree : Tree => ↑depth tree) trees.
```
-/

/-- Shift all trees in a list by depth d -/
def shiftList (depth : Nat) (trees : List (MakeTree A)) : List (MakeTree A) :=
  trees.map (shift depth)

-- Notation: ⇑ for shiftList
scoped notation "⇑[" d "]" ts => shiftList d ts

-- Coq: Lemma shift_list_nil : forall (d : nat), ⇑d nil = nil.
@[simp, grind =]
theorem shiftList_nil (d : Nat) : shiftList d ([] : List (MakeTree A)) = [] := rfl

-- Coq: Lemma shift_list_cons : forall (d : nat) (t : Tree) (trees : list Tree),
--        ⇑d (t::trees) = ↑d t :: ⇑d trees.
@[simp, grind =]
theorem shiftList_cons (d : Nat) (t : MakeTree A) (trees : List (MakeTree A)) :
    shiftList d (t :: trees) = shift d t :: shiftList d trees := rfl

-- Coq: Lemma shift_list_length : forall (d : nat) (trees : list Tree),
--        length (⇑d trees) = length trees.
@[simp, grind =]
theorem shiftList_length (d : Nat) (trees : List (MakeTree A)) :
    (shiftList d trees).length = trees.length := by
  grind [shiftList]

-- Coq: Lemma shift_list_nth : forall (d : nat) (trees : list Tree) (n : nat) (t : Tree),
--        nth n (⇑d trees) (↑d t) = ↑d (nth n trees t).
@[grind =]
theorem shiftList_getD (d : Nat) (trees : List (MakeTree A)) (n : Nat) (t : MakeTree A) :
    (shiftList d trees).getD n (shift d t) = shift d (trees.getD n t) := by
  simp only [shiftList, List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

-- Coq: Lemma shift_list_shift_list : forall (d d' : nat) (trees : list Tree),
--        d' <= d -> ⇑d'(⇑d trees) = ⇑(S d)(⇑d' trees).
@[grind =]
theorem shiftList_shiftList {d d' : Nat} (trees : List (MakeTree A)) (h : d' ≤ d) :
    shiftList d' (shiftList d trees) = shiftList (d + 1) (shiftList d' trees) := by
  induction trees with
  | nil => rfl
  | cons t ts ih =>
    simp only [shiftList_cons, shift_shift _ h, ih]

/-!
## Substitute List (Parallel Substitution)

Coq:
```
Fixpoint substitute_list (n : nat) (tree : Tree) (subst : list Tree) : Tree :=
  match tree with
    | Leaf m => if n <=? m then nth (m - n) subst (#(m - (length subst))) else #m
    | Bind t => λ (substitute_list (S n) t (⇑0 subst))
    | Node t1 t2 => (substitute_list n t1 subst)@(substitute_list n t2 subst)
  end.
```
-/

/-- Parallel substitution: substitute the mth element of subst for free variable n+m,
    and decrease all free variables >= n + length subst by length subst -/
def substituteList (n : Nat) (tree : MakeTree A) (subst : List (MakeTree A)) : MakeTree A :=
  match tree with
  | Leaf m =>
    if n ≤ m then subst.getD (m - n) (Leaf (m - subst.length))
    else Leaf m
  | Bind t => Bind (substituteList (n + 1) t (shiftList 0 subst))
  | Node t1 t2 => Node (substituteList n t1 subst) (substituteList n t2 subst)

-- Notation for substituteList
scoped notation t "[[" n " ↦ " s "]]" => substituteList n t s

-- Coq: Lemma substitute_list_leaf1 : forall (n m : nat) (s : list Tree),
--        m >= n -> #m[[n↦s]] = nth (m - n) s (#(m - length s)).
@[simp, grind =]
theorem substituteList_leaf_ge {n m : Nat} (s : List (MakeTree A)) (h : m ≥ n) :
    substituteList n (Leaf m) s = s.getD (m - n) (Leaf (m - s.length)) := by
  grind [substituteList]

-- Coq: Lemma substitute_list_leaf2 : forall (n m : nat) (s : list Tree),
--        m < n -> #m[[n↦s]] = #m.
@[simp, grind =]
theorem substituteList_leaf_lt {n m : Nat} (s : List (MakeTree A)) (h : m < n) :
    substituteList n (Leaf m : MakeTree A) s = Leaf m := by
  grind [substituteList]

-- Coq: Lemma substitute_list_bind
@[simp, grind =]
theorem substituteList_bind (n : Nat) (t : MakeTree A) (s : List (MakeTree A)) :
    substituteList n (Bind t) s = Bind (substituteList (n + 1) t (shiftList 0 s)) := rfl

-- Coq: Lemma substitute_list_node
@[simp, grind =]
theorem substituteList_node (n : Nat) (t1 t2 : MakeTree A) (s : List (MakeTree A)) :
    substituteList n (Node t1 t2) s = Node (substituteList n t1 s) (substituteList n t2 s) := rfl

-- Coq: Lemma substitute_list_nil : forall (n : nat) (t : Tree), t[[n↦nil]] = t.
@[grind =]
theorem substituteList_nil (n : Nat) (t : MakeTree A) : substituteList n t [] = t := by
  induction t generalizing n <;> grind

-- Coq: Lemma substitute_list_cons : forall (n : nat) (t : Tree) (s : list Tree) (t' : Tree),
--        t[[n↦t'::s]] = t[[S n↦⇑n s]][n↦t'].
@[grind =]
theorem substituteList_cons (n : Nat) (t : MakeTree A) (s : List (MakeTree A)) (t' : MakeTree A) :
    substituteList n t (t' :: s) = substitute n (substituteList (n + 1) t (shiftList n s)) t' := by
  induction t generalizing n s t' <;> grind [shiftList]

-- Generalized version: substituteList at depth d with shifted identity list
-- This handles the case where we substitute at depth d with [Leaf d, Leaf (d+1), ..., Leaf (d+n-1)]
theorem substituteList_id_gen (t : MakeTree A) (d n : Nat) (h : freeVar t ≤ d + n) :
    substituteList d t (List.map (fun i => Leaf (A := A) (d + i)) (List.range n)) = t := by
  induction t generalizing d n with
  | Leaf m =>
    grind
  | Bind t ih =>
    congr 1
    -- shiftList 0 (map (fun i => Leaf (d + i)) (range n)) = map (fun i => Leaf (d + 1 + i)) (range n)
    have hshift : shiftList 0 (List.map (fun i => Leaf (A := A) (d + i)) (List.range n)) =
                  List.map (fun i => Leaf (A := A) ((d + 1) + i)) (List.range n) := by
      simp only [shiftList, List.map_map]
      congr 1
      grind
    grind [shiftList]
  | Node t1 t2 ih1 ih2 =>
    grind

-- Coq: Lemma id_subst : substituting identity (variables 0..n-1) gives back the same term
-- when free variables are bounded
theorem substituteList_id (t : MakeTree A) (n : Nat) (h : freeVar t ≤ n) :
    substituteList 0 t (List.map (Leaf (A := A)) (List.range n)) = t := by
  have hgen := substituteList_id_gen t 0 n (by grind)
  simp only [Nat.zero_add] at hgen
  exact hgen

end MakeTree

/-!
## Reflexive Transitive Closure and Confluence

Coq:
```
Definition confluent (R : A -> A -> Prop) : Prop :=
  forall (t t' t'' : A),
    R t t' ->  R t t'' -> exists t''' : A, R t' t''' /\ R t'' t'''.

Inductive refl_trans_closure (R : A -> A -> Prop) : A -> A -> Prop :=
  | Refl : forall (t : A), refl_trans_closure R t t
  | Trans : forall (t t' t'' : A), (R t t') -> refl_trans_closure R t' t'' -> refl_trans_closure R t t''.
```
-/

/-- A relation R is confluent if whenever t reduces to both t' and t'',
    there exists t''' such that both t' and t'' reduce to t''' -/
def Confluent {A : Type} (R : A → A → Prop) : Prop :=
  ∀ t t' t'', R t t' → R t t'' → ∃ t''', R t' t''' ∧ R t'' t'''

/-- Reflexive transitive closure of a relation -/
@[grind]
inductive ReflTransClosure {A : Type} (R : A → A → Prop) : A → A → Prop where
  | refl : ∀ t, ReflTransClosure R t t
  | trans : ∀ t t' t'', R t t' → ReflTransClosure R t' t'' → ReflTransClosure R t t''

namespace ReflTransClosure

variable {A : Type} {R : A → A → Prop}

-- Coq: Lemma refl_trans_refl : forall (t : A), t ≻* t.
theorem refl_trans_refl (t : A) : ReflTransClosure R t t := refl t

-- Coq: Lemma refl_trans_trans : forall (t t' t'' : A), t ≻* t' -> t' ≻* t'' -> t ≻* t''.
theorem refl_trans_trans {t t' t'' : A} (h1 : ReflTransClosure R t t') (h2 : ReflTransClosure R t' t'') :
    ReflTransClosure R t t'' := by
  induction h1 with
  | refl _ => exact h2
  | trans _ _ _ hstep _ ih => exact trans _ _ _ hstep (ih h2)

-- Coq: Lemma refl_trans_confluent : confluent R -> confluent (refl_trans_closure R).
theorem refl_trans_confluent (hconf : Confluent R) : Confluent (ReflTransClosure R) := by
  -- First prove auxiliary: if t ≻* t' and t ≻ t'', then ∃ t''', t' ≻ t''' ∧ t'' ≻* t'''
  have aux : ∀ t t' t'', ReflTransClosure R t t' → R t t'' → ∃ t''', R t' t''' ∧ ReflTransClosure R t'' t''' := by
    intro t t' t'' hred
    induction hred generalizing t'' with
    | refl _ =>
      intro hstep
      exact ⟨t'', hstep, refl _⟩
    | trans _ _ _ hstep0 _ ih =>
      intro hstep''
      obtain ⟨w, hredw1, hredw2⟩ := hconf _ _ _ hstep0 hstep''
      obtain ⟨u, hredu1, hredu2⟩ := ih _ hredw1
      exact ⟨u, hredu1, trans _ _ _ hredw2 hredu2⟩
  -- Now prove the main result
  intro t t' t'' hred' hred''
  induction hred'' generalizing t' with
  | refl _ =>
    exact ⟨t', refl _, hred'⟩
  | trans _ _ _ hstep0'' _ ih =>
    obtain ⟨w, hredw1, hredw2⟩ := aux _ _ _ hred' hstep0''
    obtain ⟨u, hredu1, hredu2⟩ := ih _ hredw2
    exact ⟨u, refl_trans_trans (trans _ _ _ hredw1 (refl _)) hredu1, hredu2⟩

-- Coq: Lemma refl_trans_incl : (forall t t', t ≻ t' -> t ≻'* t') -> (forall t t', t ≻* t' -> t ≻'* t').
theorem refl_trans_incl {R' : A → A → Prop}
    (hinc : ∀ t t', R t t' → ReflTransClosure R' t t')
    {t t' : A} (hred : ReflTransClosure R t t') : ReflTransClosure R' t t' := by
  induction hred with
  | refl _ => grind
  | trans _ _ _ hstep _ ih => apply refl_trans_trans (hinc _ _ hstep) <;> grind

end ReflTransClosure

/-!
## Lambda Terms and Parallel Reduction

We define a type alias for λ-terms and the parallel reduction relation (Krivine's ρ).

Coq:
```
Inductive TermParam :=.
Notation Term := (@MakeTree TermParam).
```
-/

/-- Phantom type for λ-terms -/
inductive TermParam : Type

/-- λ-terms are MakeTree with the TermParam phantom type -/
abbrev Term := MakeTree TermParam

namespace Term

open MakeTree

/-- Variable (de Bruijn index) -/
abbrev var (n : Nat) : Term := Leaf n

/-- Lambda abstraction -/
abbrev lam (t : Term) : Term := Bind t

/-- Application -/
abbrev app (t1 t2 : Term) : Term := Node t1 t2

/-!
### Parallel Reduction (red0)

Coq:
```
Inductive red0 : Term -> Term -> Prop :=
  | Ctx_Var0 : forall (n : nat), red0 (#n) (#n)
  | Beta0 : forall (t1 t1' t2 t2' : Term), red0 t1 t1' -> red0 t2 t2' -> red0 (λ t1@t2) (t1'[0↦t2'])
  | Ctx_Abs0 : forall (t t' : Term), red0 t t' -> red0 (λ t) (λ t')
  | Ctx_App0 : forall (t1 t1' t2 t2' : Term), red0 t1 t1' -> red0 t2 t2' -> red0 (t1@t2) (t1'@t2').
```
-/

/-- Parallel reduction relation (Krivine's ρ) -/
@[grind]
inductive red0 : Term → Term → Prop where
  | Var : ∀ n, red0 (var n) (var n)
  | Beta : ∀ t1 t1' t2 t2', red0 t1 t1' → red0 t2 t2' →
      red0 (app (lam t1) t2) (substitute 0 t1' t2')
  | Abs : ∀ t t', red0 t t' → red0 (lam t) (lam t')
  | App : ∀ t1 t1' t2 t2', red0 t1 t1' → red0 t2 t2' → red0 (app t1 t2) (app t1' t2')

-- Coq: Lemma red0_refl : forall (t : Term), t ≻₀ t.
@[refl, grind .]
theorem red0_refl : ∀ t : Term, red0 t t := by
  intro t
  induction t with grind

-- Coq: Lemma red0_shift : forall (t t' : Term) (d : nat), t ≻₀ t' -> ↑d t ≻₀ ↑d t'.
@[grind =>]
theorem red0_shift {t t' : Term} (d : Nat) (hred : red0 t t') : red0 (shift d t) (shift d t') := by
  induction hred generalizing d with
  | Var n => grind
  | Beta t1 t1' t2 t2' _ _ ih1 ih2 =>
    simp only [app, lam, shift_node, shift_bind]
    rw [← shift_substitute2 t1' t2' (Nat.zero_le d)]
    grind
  | Abs t t' _ ih =>
    grind
  | App t1 t1' t2 t2' _ _ ih1 ih2 =>
    grind

-- Coq: Lemma red0_subst : forall (t1 t1' t2 t2' : Term) (n : nat),
--        t1 ≻₀ t1' -> t2 ≻₀ t2' -> t1[n↦t2] ≻₀ t1'[n↦t2'].
@[grind =>]
theorem red0_subst {t1 t1' t2 t2' : Term} (n : Nat)
    (hred1 : red0 t1 t1') (hred2 : red0 t2 t2') :
    red0 (substitute n t1 t2) (substitute n t1' t2') := by
  induction hred1 generalizing t2 t2' n with
  | Var m => grind
  | Beta t11 t11' t12 t12' _ _ ih1 ih2 =>
    simp only [app, lam, substitute_node, substitute_bind]
    rw [substitute_substitute _ _ _ (Nat.zero_le n)]
    grind
  | Abs t t' _ ih =>
    simp only [lam, substitute_bind]
    exact red0.Abs _ _ (ih (n + 1) (red0_shift 0 hred2))
  | App t11 t11' t12 t12' _ _ ih1 ih2 =>
    simp only [app, substitute_node]
    exact red0.App _ _ _ _ (ih1 n hred2) (ih2 n hred2)

-- Coq: Lemma red0_confluent : confluent red0.
@[grind .]
theorem red0_confluent : Confluent red0 := by
  intro t
  induction t with
  | Leaf n =>
    intro t' t'' hred' hred''
    cases hred' with
    | Var => cases hred'' with
      | Var => exact ⟨var n, red0.Var n, red0.Var n⟩
  | Bind t ih =>
    intro t' t'' hred' hred''
    cases hred' with
    | Abs _ t0' hred0' => cases hred'' with
      | Abs _ t0'' hred0'' =>
        obtain ⟨t''', hred', hred''⟩ := ih t0' t0'' hred0' hred0''
        exact ⟨lam t''', red0.Abs _ _ hred', red0.Abs _ _ hred''⟩
  | Node t1 t2 ih1 ih2 =>
    intro t' t'' hred' hred''
    cases hred' with
    | Beta t01 t01' t02 t02' hred01' hred02' =>
      cases hred'' with
      | Beta t001 t01'' t002 t02'' hred01'' hred02'' =>
        -- Both are beta reductions
        obtain ⟨t1''', hred1', hred1''⟩ := ih1 (lam t01') (lam t01'') (red0.Abs _ _ hred01') (red0.Abs _ _ hred01'')
        cases hred1' with
        | Abs _ t001' hred001' =>
          cases hred1'' with
          | Abs _ t001'' hred001'' =>
            obtain ⟨t2''', hred2', hred2''⟩ := ih2 t02' t02'' hred02' hred02''
            exact ⟨substitute 0 t001' t2''', red0_subst 0 hred001' hred2', red0_subst 0 hred001'' hred2''⟩
      | App t01'' t1'' t02'' t2'' hred1'' hred2'' =>
        -- First is beta, second is app
        cases hred1'' with
        | Abs _ t001'' hred001'' =>
          obtain ⟨t1''', hred01'', hred1'''⟩ := ih1 (lam t01') (lam t001'') (red0.Abs _ _ hred01') (red0.Abs _ _ hred001'')
          cases hred01'' with
          | Abs _ tBody hredBody =>
            cases hred1''' with
            | Abs _ tBody' hredBody' =>
              obtain ⟨t2''', hred02'', hred2'''⟩ := ih2 t02' t2'' hred02' hred2''
              exact ⟨substitute 0 tBody t2''', red0_subst 0 hredBody hred02'', red0.Beta _ _ _ _ hredBody' hred2'''⟩
    | App t01' t1' t02' t2' hred1' hred2' =>
      cases hred'' with
      | Beta t01 t1'' t02 t2'' hred1'' hred2'' =>
        -- First is app, second is beta
        cases hred1' with
        | Abs _ t001' hred001' =>
          obtain ⟨t2''', hred02', hred02''⟩ := ih2 t2' t2'' hred2' hred2''
          obtain ⟨t1''', hred01', hred01''⟩ := ih1 (lam t001') (lam t1'') (red0.Abs _ _ hred001') (red0.Abs _ _ hred1'')
          cases hred01' with
          | Abs _ tBody hredBody =>
            cases hred01'' with
            | Abs _ tBody' hredBody' =>
              exact ⟨substitute 0 tBody t2''', red0.Beta _ _ _ _ hredBody hred02', red0_subst 0 hredBody' hred02''⟩
      | App t01 t1'' t02 t2'' hred1'' hred2'' =>
        -- Both are app
        obtain ⟨t1''', hred1', hred1''⟩ := ih1 t1' t1'' hred1' hred1''
        obtain ⟨t2''', hred2', hred2''⟩ := ih2 t2' t2'' hred2' hred2''
        exact ⟨app t1''' t2''', red0.App _ _ _ _ hred1' hred2', red0.App _ _ _ _ hred1'' hred2''⟩

/-!
### Single-step Beta Reduction

Coq:
```
Inductive beta : Term -> Term -> Prop :=
  | Beta : forall (t t' : Term), beta ((λ t)@t') (t[0↦t'])
  | Ctx_Abs : forall (t t' : Term), beta t t' -> beta (λ t) (λ t')
  | Ctx_App_l : forall (t1 t1' : Term) (t2 : Term), beta t1 t1' -> beta (t1@t2) (t1'@t2)
  | Ctx_App_r : forall (t1 t2 : Term) (t2' : Term), beta t2 t2' -> beta (t1@t2) (t1@t2').
```
-/

/-- Single-step beta reduction (Krivine's β₀) -/
@[grind]
inductive beta : Term → Term → Prop where
  | Beta : ∀ t t', beta (app (lam t) t') (substitute 0 t t')
  | Abs : ∀ t t', beta t t' → beta (lam t) (lam t')
  | AppL : ∀ t1 t1' t2, beta t1 t1' → beta (app t1 t2) (app t1' t2)
  | AppR : ∀ t1 t2 t2', beta t2 t2' → beta (app t1 t2) (app t1 t2')

-- Coq: Lemma beta_red0_incl : forall (t t' : Term), t ≻ t' -> t ≻₀ t'.
@[grind .]
theorem beta_red0_incl {t t' : Term} (hred : beta t t') : red0 t t' := by
  induction hred with
  | Beta t t' => exact red0.Beta t t t' t' (red0_refl t) (red0_refl t')
  | Abs _ _ _ ih => exact red0.Abs _ _ ih
  | AppL _ _ t2 _ ih => exact red0.App _ _ _ _ ih (red0_refl t2)
  | AppR t1 _ _ _ ih => exact red0.App _ _ _ _ (red0_refl t1) ih

-- Coq: Lemma beta_substitute : forall (t t' t'' : Term) (n : nat), t ≻ t' -> t[n↦t''] ≻ t'[n↦t''].
@[grind =>]
theorem beta_substitute {t t' : Term} (t'' : Term) (n : Nat) (hred : beta t t') :
    beta (substitute n t t'') (substitute n t' t'') := by
  induction hred generalizing t'' n with
  | Beta t1 t2 =>
    simp only [lam, substitute_node, substitute_bind]
    rw [substitute_substitute _ _ _ (Nat.zero_le n)]
    exact beta.Beta _ _
  | Abs _ _ _ ih =>
    simp only [lam, substitute_bind]
    exact beta.Abs _ _ (ih (shift 0 t'') (n + 1))
  | AppL _ _ _ _ ih =>
    simp only [substitute_node]
    exact beta.AppL _ _ _ (ih t'' n)
  | AppR _ _ _ _ ih =>
    simp only [substitute_node]
    exact beta.AppR _ _ _ (ih t'' n)

/-!
### Strong Normalization

Coq:
```
Inductive Normalizing (t : Term) : Prop :=
  | NormalizingInd : (forall (t' : Term), t ≻ t' -> Normalizing t') -> Normalizing t.
```
-/

/-- A term is normalizing if all its reducts are normalizing -/
inductive Normalizing : Term → Prop where
  | intro : (∀ t', beta t t' → Normalizing t') → Normalizing t

-- Coq: Lemma var_normalizing : forall (n : nat), Normalizing (#n).
@[grind .]
theorem var_normalizing (n : Nat) : Normalizing (var n) := by
  apply Normalizing.intro
  intro t' hred
  cases hred

-- Coq: Lemma abs_normalizing : forall (t : Term), Normalizing t -> Normalizing (λ t).
@[grind .]
theorem abs_normalizing {t : Term} (hnorm : Normalizing t) : Normalizing (lam t) := by
  induction hnorm with
  | intro _ ih =>
    apply Normalizing.intro
    intro t' hred
    cases hred with
    | Abs _ t'' hred' => exact ih t'' hred'

-- Coq: Lemma normalizing_abs : forall (t : Term), Normalizing (λ t) -> Normalizing t.
@[grind →]
theorem normalizing_abs {t : Term} (hnorm : Normalizing (lam t)) : Normalizing t := by
  -- Prove the more general statement: for any s, if Normalizing s and s = lam t, then Normalizing t
  suffices h : ∀ s t, Normalizing s → s = lam t → Normalizing t from h (lam t) t hnorm rfl
  intro s t hnorm heq
  induction hnorm generalizing t with
  | intro _ ih =>
    subst heq
    apply Normalizing.intro
    intro t' hred
    exact ih (lam t') (beta.Abs _ _ hred) t' rfl

@[grind →]
-- Coq: Lemma normalizing_app : forall (t1 t2 : Term), Normalizing (t1@t2) -> Normalizing t1 /\ Normalizing t2.
theorem normalizing_app {t1 t2 : Term} (hnorm : Normalizing (app t1 t2)) :
    Normalizing t1 ∧ Normalizing t2 := by
  -- Prove the more general statement
  suffices h : ∀ s t1 t2, Normalizing s → s = app t1 t2 → Normalizing t1 ∧ Normalizing t2
    from h (app t1 t2) t1 t2 hnorm rfl
  intro s t1 t2 hnorm heq
  induction hnorm generalizing t1 t2 with
  | intro _ ih =>
    subst heq
    constructor
    · apply Normalizing.intro
      intro t1' hred
      obtain ⟨hnorm1, _⟩ := ih (app t1' t2) (by grind) t1' t2 rfl
      grind
    · apply Normalizing.intro
      intro t2' hred
      obtain ⟨_, hnorm2⟩ := ih (app t1 t2') (by grind) t1 t2' rfl
      grind

/-!
### Inversion lemmas for beta through shift/substitute

Coq:
```
Lemma shift_beta : forall (t t' : Term) (d : nat),
  ↑d t ≻ t' -> exists t'' : Term, t ≻ t'' /\ t' = ↑d t''.
```
-/

/-- If a shifted term reduces, the reduction came from the original term -/
theorem shift_beta {t t' : Term} (d : Nat) (hred : beta (shift d t) t') :
    ∃ t'', beta t t'' ∧ t' = shift d t'' := by
  induction t generalizing t' d with
  | Leaf m =>
    simp only [shift] at hred
    split at hred <;> cases hred
  | Bind tbody ih =>
    simp only [shift_bind] at hred
    cases hred with
    | Abs _ t'' hred' =>
      obtain ⟨t''', hred''', heq⟩ := ih (d + 1) hred'
      exact ⟨lam t''', beta.Abs _ _ hred''', by simp [lam, shift_bind, heq]⟩
  | Node t1 t2 ih1 ih2 =>
    -- First case on t1 to handle the Beta case
    cases t1 with
    | Leaf m =>
      simp only [shift] at hred
      split at hred
      · -- d ≤ m, shift gives Leaf (m+1)
        cases hred with
        | AppL _ _ _ hred' => exact absurd hred' (by intro h; cases h)
        | AppR _ _ _ hred' =>
          obtain ⟨t2'', hred2'', heq2⟩ := ih2 d hred'
          exact ⟨app (Leaf m) t2'', beta.AppR _ _ _ hred2'', by simp [app, shift, *]⟩
      · -- m < d, shift gives Leaf m
        cases hred with
        | AppL _ _ _ hred' => exact absurd hred' (by intro h; cases h)
        | AppR _ _ _ hred' =>
          obtain ⟨t2'', hred2'', heq2⟩ := ih2 d hred'
          exact ⟨app (Leaf m) t2'', beta.AppR _ _ _ hred2'', by simp [app, shift, *]⟩
    | Bind t1body =>
      simp only [shift_node, shift_bind] at hred
      cases hred with
      | Beta _ _ =>
        refine ⟨substitute 0 t1body t2, beta.Beta _ _, ?_⟩
        exact shift_substitute2 t1body t2 (Nat.zero_le d)
      | AppL _ _ _ hred' =>
        -- hred' : beta (lam (shift (d+1) t1body)) t1'
        -- ih1 is for Bind t1body, so we apply it directly to hred'
        obtain ⟨t1'', hred1'', heq1⟩ := ih1 d hred'
        exact ⟨app t1'' t2, beta.AppL _ _ _ hred1'', by simp [app, shift_node, heq1]⟩
      | AppR _ _ _ hred' =>
        obtain ⟨t2'', hred2'', heq2⟩ := ih2 d hred'
        exact ⟨app (lam t1body) t2'', beta.AppR _ _ _ hred2'',
               by simp [app, lam, shift_node, shift_bind, heq2]⟩
    | Node t11 t12 =>
      simp only [shift_node] at hred
      cases hred with
      | AppL _ _ _ hred' =>
        obtain ⟨t1'', hred1'', heq1⟩ := ih1 d hred'
        exact ⟨app t1'' t2, beta.AppL _ _ _ hred1'', by simp [app, shift_node, heq1]⟩
      | AppR _ _ _ hred' =>
        obtain ⟨t2'', hred2'', heq2⟩ := ih2 d hred'
        exact ⟨app (Node t11 t12) t2'', beta.AppR _ _ _ hred2'', by simp [app, shift_node, heq2]⟩

-- Coq: Lemma shift_normalizing : forall (t : Term), Normalizing t -> Normalizing (↑0 t).
theorem shift_normalizing {t : Term} (hnorm : Normalizing t) : Normalizing (shift 0 t) := by
  induction hnorm with
  | intro _ ih =>
    apply Normalizing.intro
    intro t' hred
    obtain ⟨t'', hred'', heq⟩ := shift_beta 0 hred
    rw [heq]
    exact ih t'' hred''

/-- Coq: Lemma substitute_leaf_beta : forall (t t' : Term) (p q : nat),
      t[p↦#q] ≻ t' -> exists t'' : Term,  t ≻ t'' /\ t' = t''[p↦#q]. -/
theorem substitute_leaf_beta {t t' : Term} (p q : Nat) (hred : beta (substitute p t (var q)) t') :
    ∃ t'', beta t t'' ∧ t' = substitute p t'' (var q) := by
  induction t generalizing t' p q with
  | Leaf m =>
    -- substitute p (Leaf m) (var q) is always a Leaf, so beta reduction is impossible
    simp only [substitute, var] at hred
    generalize hs : (if m = p then Leaf q else if m > p then Leaf (m - 1) else Leaf m) = s at hred
    have hleaf : ∃ k, s = Leaf k := by
      split at hs
      · exact ⟨_, hs.symm⟩
      · split at hs <;> exact ⟨_, hs.symm⟩
    obtain ⟨k, hk⟩ := hleaf
    rw [hk] at hred
    cases hred
  | Bind tbody ih =>
    simp only [substitute_bind] at hred
    cases hred with
    | Abs _ t'' hred' =>
      -- shift 0 (var q) = var (q+1) when 0 ≤ q, which is always true
      simp only [var, shift_leaf_ge (Nat.zero_le q)] at hred'
      obtain ⟨t''', hred''', heq⟩ := ih (p + 1) (q + 1) hred'
      refine ⟨lam t''', beta.Abs _ _ hred''', ?_⟩
      simp only [lam, substitute_bind, var, shift_leaf_ge (Nat.zero_le q), heq]
  | Node t1 t2 ih1 ih2 =>
    simp only [substitute_node] at hred
    -- Handle each case of t1 separately to avoid dependent elimination issues
    cases t1 with
    | Leaf m =>
      -- substitute p (Leaf m) (var q) is always a Leaf, so Beta and non-trivial AppL are impossible
      simp only [substitute] at hred
      -- Use generalize to avoid dependent elimination issues
      generalize hs1 : (if m = p then var q else if m > p then Leaf (m - 1) else Leaf m) = s1 at hred
      -- First prove s1 is a Leaf
      have hleaf : ∃ k, s1 = Leaf k := by
        simp only [var] at hs1
        split at hs1
        · exact ⟨_, hs1.symm⟩
        · split at hs1 <;> exact ⟨_, hs1.symm⟩
      obtain ⟨k, hk⟩ := hleaf
      rw [hk] at hred
      -- Now hred : beta (app (Leaf k) s2) t', and Leaf can't be head of Beta or reduce via AppL
      match hred with
      | beta.AppL _ _ _ hred' => cases hred'
      | beta.AppR _ _ _ hred' =>
        obtain ⟨t2'', hred2'', heq2⟩ := ih2 p q hred'
        exact ⟨app (Leaf m) t2'', beta.AppR _ _ _ hred2'', by simp [app, substitute, *]⟩
    | Bind t1body =>
      simp only [substitute_bind] at hred
      match hred with
      | beta.Beta _ _ =>
        refine ⟨substitute 0 t1body t2, beta.Beta _ _, ?_⟩
        have h := substitute_substitute t1body t2 (var q) (Nat.zero_le p)
        simp only [var, shift_leaf_ge (Nat.zero_le q)] at h
        exact h.symm
      | beta.AppL _ _ _ hred' =>
        obtain ⟨t1'', hred1'', heq1⟩ := ih1 p q hred'
        exact ⟨app t1'' t2, beta.AppL _ _ _ hred1'', by simp [app, substitute_node, heq1]⟩
      | beta.AppR _ _ _ hred' =>
        obtain ⟨t2'', hred2'', heq2⟩ := ih2 p q hred'
        exact ⟨app (lam t1body) t2'', beta.AppR _ _ _ hred2'',
               by simp [app, lam, substitute_node, substitute_bind, heq2]⟩
    | Node t11 t12 =>
      simp only [substitute_node] at hred
      match hred with
      | beta.AppL _ _ _ hred' =>
        obtain ⟨t1'', hred1'', heq1⟩ := ih1 p q hred'
        exact ⟨app t1'' t2, beta.AppL _ _ _ hred1'', by simp [app, substitute_node, heq1]⟩
      | beta.AppR _ _ _ hred' =>
        obtain ⟨t2'', hred2'', heq2⟩ := ih2 p q hred'
        exact ⟨app (Node t11 t12) t2'', beta.AppR _ _ _ hred2'', by simp [app, substitute_node, heq2]⟩

-- Coq: Lemma substitute_leaf_normalizing : forall (t : Term) (p q : nat),
--        Normalizing t -> Normalizing (t[p↦#q]).
theorem substitute_leaf_normalizing {t : Term} (p q : Nat) (hnorm : Normalizing t) :
    Normalizing (substitute p t (var q)) := by
  induction hnorm with
  | intro _ ih =>
    apply Normalizing.intro
    intro t' hred
    obtain ⟨t'', hred'', heq⟩ := substitute_leaf_beta p q hred
    rw [heq]
    exact ih t'' hred''

/-- Coq: Lemma normalizing_substitute_leaf : forall (t : Term),
      (forall (n : nat), Normalizing (t[0↦#n])) -> Normalizing t. -/
theorem normalizing_substitute_leaf {t : Term}
    (h : ∀ n : Nat, Normalizing (substitute 0 t (var n))) : Normalizing t := by
  rw [← id_substitute_shift_substitute t (freeVar t) 0 (by grind)]
  apply substitute_leaf_normalizing
  apply shift_normalizing
  exact h (freeVar t)

grind_pattern normalizing_substitute_leaf => Normalizing (substitute 0 t (var _))

/-- Result of deciding whether a term is in normal form -/
inductive NormalDecResult (t : Term) : Type where
  | isNormal : (∀ t', ¬ beta t t') → NormalDecResult t
  | hasReduct : (t' : Term) → beta t t' → NormalDecResult t

/-- Coq: Lemma normal_dec : forall (t : Term), (forall (t' : Term), ~ t ≻ t') + {t' : Term | t ≻ t'}.
    Decides whether a term is in normal form, returning either a proof that no reduction exists,
    or a witness reduction. -/
def normal_dec : (t : Term) → NormalDecResult t
  | Leaf n => NormalDecResult.isNormal fun t' hred => nomatch hred
  | MakeTree.Bind t =>
    match normal_dec t with
    | NormalDecResult.isNormal hnorm =>
      NormalDecResult.isNormal fun t' hred =>
        match hred with
        | beta.Abs _ t'' hred' => hnorm t'' hred'
    | NormalDecResult.hasReduct t' hred =>
      NormalDecResult.hasReduct (lam t') (beta.Abs _ _ hred)
  | Node t1 t2 =>
    match normal_dec t1 with
    | NormalDecResult.hasReduct t1' hred1 =>
      NormalDecResult.hasReduct (app t1' t2) (beta.AppL _ _ _ hred1)
    | NormalDecResult.isNormal hnorm1 =>
      match normal_dec t2 with
      | NormalDecResult.hasReduct t2' hred2 =>
        NormalDecResult.hasReduct (app t1 t2') (beta.AppR _ _ _ hred2)
      | NormalDecResult.isNormal hnorm2 =>
        match t1 with
        | Leaf n =>
          NormalDecResult.isNormal fun t' hred =>
            match hred with
            | beta.AppL _ _ _ hred' => nomatch hred'
            | beta.AppR _ _ _ hred' => hnorm2 _ hred'
        | MakeTree.Bind t1body =>
          NormalDecResult.hasReduct (substitute 0 t1body t2) (beta.Beta _ _)
        | Node t11 t12 =>
          NormalDecResult.isNormal fun t' hred =>
            match hred with
            | beta.AppL _ _ _ hred' => hnorm1 _ hred'
            | beta.AppR _ _ _ hred' => hnorm2 _ hred'

/-- Result of computing a normal form -/
structure NormalFormResult (t : Term) : Type where
  normalForm : Term
  reduction : ReflTransClosure beta t normalForm
  isNormal : ∀ t'', ¬ beta normalForm t''

/-- Reducts of normalizing terms are normalizing -/
theorem normalizing_step : ∀ t, Normalizing t → ∀ t', beta t t' → Normalizing t' := by
  intro t hnorm t' hred
  cases hnorm with
  | intro h => exact h t' hred

/-- Well-founded relation on normalizing terms -/
instance : WellFoundedRelation { t : Term // Normalizing t } where
  rel := fun ⟨t', _⟩ ⟨t, _⟩ => beta t t'
  wf := ⟨fun ⟨t, hn⟩ =>
    hn.recOn (motive := fun t _ => Acc (fun (p' p : { t : Term // Normalizing t }) => beta p.1 p'.1) ⟨t, ‹_›⟩)
      (fun h ih => Acc.intro _ (fun ⟨t', _⟩ hred => ih t' hred))⟩

/-- Coq: Lemma normal_form : forall (t : Term), Normalizing t -> {t' : Term | t ≻* t' /\ forall t'', ~ t' ≻ t''}.
    Computes the normal form of a normalizing term. -/
def normal_form (t : Term) (hnorm : Normalizing t) : NormalFormResult t :=
  match normal_dec t with
  | NormalDecResult.isNormal hnorm' =>
    ⟨t, ReflTransClosure.refl t, hnorm'⟩
  | NormalDecResult.hasReduct t' hred =>
    let hnorm' := normalizing_step t hnorm t' hred
    let ⟨t'', red'', norm''⟩ := normal_form t' hnorm'
    ⟨t'', ReflTransClosure.trans t t' t'' hred red'', norm''⟩
termination_by (⟨t, hnorm⟩ : { t : Term // Normalizing t })

/-!
## Reducibility Candidates

Definition of closure under β-reduction, neutrality, saturation,
and reducibility candidates for proving strong normalization.
-/

/-- Coq: Definition RedClosed (X : Term -> Prop) : Prop := forall (t t' : Term), X t -> t ≻ t' -> X t'.
    A set of terms is closed under reduction if it is preserved by beta reduction. -/
def RedClosed (X : Term → Prop) : Prop :=
  ∀ t t', X t → beta t t' → X t'

/-- Coq: Inductive Neutral : Term -> Prop := | Var_Neutral | App_Neutral.
    A term is neutral if it is not an abstraction. -/
inductive Neutral : Term → Prop where
  | Var : ∀ n, Neutral (var n)
  | App : ∀ t1 t2, Neutral (app t1 t2)

/-- Coq: Definition Saturated (X : Term -> Prop) := forall (t : Term), Neutral t -> (forall (t' : Term), t ≻ t' -> X t') -> X t.
    A set of terms is saturated if a neutral term is in the set whenever all its reducts are. -/
def Saturated (X : Term → Prop) : Prop :=
  ∀ t, Neutral t → (∀ t', beta t t' → X t') → X t

/-- Coq: Definition RedCand (X : Term -> Prop) := (normalizing) /\ RedClosed /\ Saturated.
    A reducibility candidate is a reduction-closed saturated set of normalizing terms. -/
def RedCand (X : Term → Prop) : Prop :=
  (∀ t, X t → Normalizing t) ∧ RedClosed X ∧ Saturated X

-- Coq: Lemma RedCand_Normalizing
@[grind =>]
theorem RedCand_Normalizing {X : Term → Prop} (hrc : RedCand X) : ∀ t, X t → Normalizing t :=
  hrc.1

-- Coq: Lemma RedCand_RedClosed
@[grind =>]
theorem RedCand_RedClosed {X : Term → Prop} (hrc : RedCand X) : RedClosed X :=
  hrc.2.1

-- Coq: Lemma RedCand_Saturated
@[grind =>]
theorem RedCand_Saturated {X : Term → Prop} (hrc : RedCand X) : Saturated X :=
  hrc.2.2

/-- Coq: Lemma RedCandVar : forall (X : Term -> Prop) (n : nat), RedCand X -> X (#n).
    A reducibility candidate contains all variables. -/
@[grind =>]
theorem RedCandVar {X : Term → Prop} (n : Nat) (hrc : RedCand X) : X (var n) := by
  apply RedCand_Saturated hrc
  · exact Neutral.Var n
  · intro t' hred
    cases hred

/-- Coq: Lemma SNRedCand : RedCand Normalizing.
    The set of all normalizing terms is a reducibility candidate. -/
theorem SNRedCand : RedCand Normalizing := by
  refine ⟨fun _ h => h, ?_, ?_⟩
  · -- RedClosed
    intro t t' hnorm hred
    cases hnorm with
    | intro h => exact h t' hred
  · -- Saturated
    intro t _ ih
    exact Normalizing.intro ih

/-- Coq: Definition RedCandArrow (X Y : Term -> Prop) (t1 : Term) : Prop := forall (t2 : Term), X t2 -> Y (t1@t2).
    The arrow of two sets of terms. -/
def RedCandArrow (X Y : Term → Prop) (t1 : Term) : Prop :=
  ∀ t2, X t2 → Y (app t1 t2)

/-- Coq: Lemma red_cand_arrow_RedCand : The arrow of two reducibility candidates is a reducibility candidate. -/
@[grind .]
theorem red_cand_arrow_RedCand {X Y : Term → Prop} (hrcX : RedCand X) (hrcY : RedCand Y) :
    RedCand (RedCandArrow X Y) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Normalizing
    intro t1 ht1
    have h := ht1 (var 0) (RedCandVar 0 hrcX)
    exact (normalizing_app (RedCand_Normalizing hrcY _ h)).1
  · -- RedClosed
    intro t1 t1' ht1 hred t2 ht2
    apply RedCand_RedClosed hrcY
    · exact ht1 t2 ht2
    · exact beta.AppL _ _ _ hred
  · -- Saturated
    intro t1 hneutral ht1 t2 ht2
    have hnorm := RedCand_Normalizing hrcX _ ht2
    induction hnorm with
    | intro _ ih =>
      apply RedCand_Saturated hrcY
      · exact Neutral.App t1 _
      · intro t' hred
        match hred with
        | beta.Beta _ _ =>
          cases hneutral
        | beta.AppL _ t1' _ hred1 =>
          exact ht1 t1' hred1 _ ht2
        | beta.AppR _ _ t2' hred2 =>
          apply ih t2' hred2
          exact RedCand_RedClosed hrcX _ _ ht2 hred2

/-- Coq: Lemma red_cand_arrow_substitute : If for any t2∈X, t1[0↦t2]∈Y, then λt1 ∈ RedCandArrow X Y. -/
theorem red_cand_arrow_substitute {X Y : Term → Prop} {t1 : Term}
    (hrcX : RedCand X) (hrcY : RedCand Y)
    (hsub : ∀ t2, X t2 → Y (substitute 0 t1 t2)) :
    RedCandArrow X Y (lam t1) := by
  -- Use normalizing_substitute_leaf to get normalization of t1
  have ht1_norm : Normalizing t1 := by grind
  -- Now induct on normalization of t1
  induction ht1_norm with
  | intro h1 ih1 =>
    intro t2 ht2
    have hnorm2 := RedCand_Normalizing hrcX _ ht2
    induction hnorm2 with
    | intro h2 ih2 =>
      apply RedCand_Saturated hrcY
      · exact Neutral.App (lam _) _
      · intro t' hred
        match hred with
        | beta.Beta _ _ => exact hsub _ ht2
        | beta.AppL _ _ _ hred1 =>
          match hred1 with
          | beta.Abs _ t1' hred1' =>
            apply ih1 t1' hred1'
            · intro t2' ht2'
              exact RedCand_RedClosed hrcY _ _ (hsub t2' ht2') (beta_substitute t2' 0 hred1')
            · grind
        | beta.AppR _ _ t2' hred2 =>
          apply ih2 t2' hred2
          exact RedCand_RedClosed hrcX _ _ ht2 hred2

end Term

/-!
## System F Types

System F types are also represented using MakeTree, with a different phantom type.
- Leaf n = type variable &n
- Bind ty = universal type ∀ty
- Node ty1 ty2 = arrow type ty1 ⇒ ty2
-/

/-- Coq: Inductive TypeFParam :=. Phantom type for System F types. -/
inductive TypeFParam
deriving Repr

/-- System F types -/
abbrev TypeF := MakeTree TypeFParam

namespace TypeF

/-- Type variable -/
abbrev tvar (n : Nat) : TypeF := MakeTree.Leaf n

/-- Universal type -/
abbrev forallTy (ty : TypeF) : TypeF := MakeTree.Bind ty

/-- Arrow type -/
abbrev arrow (ty1 ty2 : TypeF) : TypeF := MakeTree.Node ty1 ty2

-- Convenient notations matching Coq
scoped notation:max "&." n:arg => tvar n
scoped notation:max "∀." ty:10 => forallTy ty
scoped infixr:30 " ⇒ " => arrow

end TypeF

/-!
## Type Contexts

A type context assigns a set of terms (reducibility candidate) to each type variable.
-/

/-- Coq: shift_t_ctx d t_ctx X shifts the type context, inserting X at position d. -/
def shift_t_ctx (d : Nat) (t_ctx : Nat → Term → Prop) (X : Term → Prop) : Nat → Term → Prop :=
  fun n =>
    match compare n d with
    | .eq => X
    | .lt => t_ctx n
    | .gt => t_ctx (n - 1)

-- Coq: Lemma shift_t_ctx1
@[grind =]
theorem shift_t_ctx_eq (d : Nat) (t_ctx : Nat → Term → Prop) (X : Term → Prop) :
    shift_t_ctx d t_ctx X d = X := by
  grind [shift_t_ctx]

-- Coq: Lemma shift_t_ctx2
@[grind =]
theorem shift_t_ctx_gt {d n : Nat} (t_ctx : Nat → Term → Prop) (X : Term → Prop)
    (h : n ≥ d) : shift_t_ctx d t_ctx X (n + 1) = t_ctx n := by
  grind [shift_t_ctx]

-- Coq: Lemma shift_t_ctx3
@[grind =]
theorem shift_t_ctx_lt {d n : Nat} (t_ctx : Nat → Term → Prop) (X : Term → Prop)
    (h : n < d) : shift_t_ctx d t_ctx X n = t_ctx n := by
  grind [shift_t_ctx]

/-!
## Reducibility Candidates for Types

For each System F type and type context, we define the corresponding reducibility candidate.
-/

open Term in
/-- Coq: red_cand t_ctx ty t - the term t is in the reducibility candidate for type ty. -/
def red_cand (t_ctx : Nat → Term → Prop) : TypeF → Term → Prop
  | MakeTree.Leaf n => t_ctx n
  | MakeTree.Bind ty => fun t => ∀ X, RedCand X → red_cand (shift_t_ctx 0 t_ctx X) ty t
  | MakeTree.Node ty1 ty2 => RedCandArrow (red_cand t_ctx ty1) (red_cand t_ctx ty2)

-- Helper for shift_t_ctx at 0
private theorem shift_t_ctx_0_RedCand {t_ctx : Nat → Term → Prop} {X : Term → Prop}
    (hrcX : Term.RedCand X) (hctx : ∀ n, Term.RedCand (t_ctx n)) :
    ∀ n, Term.RedCand (shift_t_ctx 0 t_ctx X n) := by
  intro n
  simp only [shift_t_ctx]
  cases n with
  | zero => simp; exact hrcX
  | succ m => simp [Nat.compare_eq_gt.mpr (Nat.zero_lt_succ m)]; exact hctx m

-- shift_t_ctx composition lemma
@[grind =]
private theorem shift_t_ctx_shift_t_ctx (d : Nat) (t_ctx : Nat → Term → Prop) (X Y : Term → Prop) :
    shift_t_ctx (d + 1) (shift_t_ctx 0 t_ctx Y) X = shift_t_ctx 0 (shift_t_ctx d t_ctx X) Y := by
  funext n t
  simp only [shift_t_ctx]
  rcases Nat.lt_trichotomy n (d + 1) with hlt | heq | hgt
  · simp only [Nat.compare_eq_lt.mpr hlt]
    rcases Nat.lt_trichotomy n 0 with hlt0 | heq0 | hgt0
    · exact absurd hlt0 (Nat.not_lt_zero n)
    · simp only [heq0, Nat.compare_eq_eq.mpr rfl]
    · simp only [Nat.compare_eq_gt.mpr hgt0, Nat.compare_eq_lt.mpr (by omega : n - 1 < d)]
  · simp only [heq, Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_gt.mpr (Nat.zero_lt_succ d), Nat.succ_sub_one]
  · simp only [Nat.compare_eq_gt.mpr hgt, Nat.compare_eq_gt.mpr (by omega : n > 0),
               Nat.compare_eq_gt.mpr (by omega : n - 1 > d), Nat.compare_eq_gt.mpr (by omega : n - 1 > 0),
               Nat.sub_sub]

-- Coq: Lemma red_cand_RedCand - red_cand always produces a reducibility candidate
open Term in
@[grind .]
theorem red_cand_RedCand (t_ctx : Nat → Term → Prop) (ty : TypeF)
    (hctx : ∀ n, RedCand (t_ctx n)) : RedCand (red_cand t_ctx ty) := by
  induction ty generalizing t_ctx with
  | Leaf n => exact hctx n
  | Bind ty ih =>
    refine ⟨?_, ?_, ?_⟩
    · -- Normalizing
      intro t ht
      have h := ht Normalizing SNRedCand
      exact RedCand_Normalizing (ih _ (shift_t_ctx_0_RedCand SNRedCand hctx)) _ h
    · -- RedClosed
      intro t t' ht hred X hrcX
      exact RedCand_RedClosed (ih _ (shift_t_ctx_0_RedCand hrcX hctx)) _ _ (ht X hrcX) hred
    · -- Saturated
      intro t hneutral ht X hrcX
      apply RedCand_Saturated (ih _ (shift_t_ctx_0_RedCand hrcX hctx))
      · exact hneutral
      · intro t' hred
        exact ht t' hred X hrcX
  | Node ty1 ty2 ih1 ih2 =>
    exact red_cand_arrow_RedCand (ih1 t_ctx hctx) (ih2 t_ctx hctx)

/-!
## System F Typing

Typing derivations for System F terms.
-/

/-- Coq: Inductive CompatSubst : compatible substitution between type context and term context.
    A substitution s is compatible with a typing context ctx in type context t_ctx if
    each term s[i] belongs to the reducibility candidate for ctx[i]. -/
@[grind]
inductive CompatSubst (t_ctx : Nat → Term → Prop) : List TypeF → List Term → Prop where
  | Nil : CompatSubst t_ctx [] []
  | Cons : ∀ ctx s ty t, CompatSubst t_ctx ctx s →
           red_cand t_ctx ty t → CompatSubst t_ctx (ty :: ctx) (t :: s)

open Term in
/-- Coq: Inductive TermF : list TypeF -> Term -> TypeF -> Type.
    System F typing derivation. ctx ⊢ t : ty means t has type ty in context ctx. -/
inductive TermF : List TypeF → Term → TypeF → Type where
  | VarF0 : TermF (ty :: ctx) (var 0) ty
  | VarFS : TermF ctx (var n) ty' → TermF (ty :: ctx) (var (n + 1)) ty'
  | AbsF : TermF (ty :: ctx) t ty' → TermF ctx (lam t) (TypeF.arrow ty ty')
  | AppF : TermF ctx t (TypeF.arrow ty ty') → TermF ctx t' ty → TermF ctx (app t t') ty'
  | TAbsF : TermF (ctx.map (MakeTree.shift 0)) t ty → TermF ctx t (TypeF.forallTy ty)
  | TAppF : TermF ctx t (TypeF.forallTy ty) → TermF ctx t (MakeTree.substitute 0 ty ty')

-- Coq: Lemma red_cand_shift - shifting preserves reducibility candidates
open Term in
theorem red_cand_shift (t_ctx : Nat → Term → Prop) (X : Term → Prop) (ty : TypeF) (d : Nat)
    (_hrcX : RedCand X) (hctx : ∀ n, RedCand (t_ctx n)) (t : Term) :
    red_cand t_ctx ty t ↔ red_cand (shift_t_ctx d t_ctx X) (MakeTree.shift d ty) t := by
  induction ty generalizing t_ctx d t with
  | Leaf n =>
    unfold red_cand MakeTree.shift
    split
    · -- d ≤ n: shift gives Leaf (n+1), shift_t_ctx (n+1) at d = t_ctx n
      rename_i h
      simp only
      rw [shift_t_ctx_gt t_ctx X h]
    · -- d > n: shift gives Leaf n, shift_t_ctx n at d = t_ctx n
      rename_i h
      simp only
      rw [shift_t_ctx_lt t_ctx X (Nat.not_le.mp h)]
  | Bind ty ih =>
    show (∀ Y, RedCand Y → red_cand (shift_t_ctx 0 t_ctx Y) ty t) ↔
         (∀ Y, RedCand Y → red_cand (shift_t_ctx 0 (shift_t_ctx d t_ctx X) Y) (MakeTree.shift (d+1) ty) t)
    constructor
    · intro ht Y hrcY
      have hih := ih (shift_t_ctx 0 t_ctx Y) (d + 1) (shift_t_ctx_0_RedCand hrcY hctx) t
      grind
    · intro ht Y hrcY
      have hih := ih (shift_t_ctx 0 t_ctx Y) (d + 1) (shift_t_ctx_0_RedCand hrcY hctx) t
      grind
  | Node ty1 ty2 ih1 ih2 =>
    show (∀ t2, red_cand t_ctx ty1 t2 → red_cand t_ctx ty2 (app t t2)) ↔
         (∀ t2, red_cand (shift_t_ctx d t_ctx X) (MakeTree.shift d ty1) t2 →
                red_cand (shift_t_ctx d t_ctx X) (MakeTree.shift d ty2) (app t t2))
    constructor <;> grind

-- Coq: Lemma red_cand_shift_substitute - substitution in types corresponds to shift_t_ctx
-- Uses well-founded recursion on ty.size since Bind case needs different ty'
open Term in
theorem red_cand_shift_substitute (t_ctx : Nat → Term → Prop) (ty ty' : TypeF) (n : Nat)
    (hctx : ∀ m, RedCand (t_ctx m)) (t : Term) :
    red_cand (shift_t_ctx n t_ctx (red_cand t_ctx ty')) ty t ↔
    red_cand t_ctx (MakeTree.substitute n ty ty') t := by
  match ty with
  | .Leaf m =>
    simp only [red_cand]
    rcases Nat.lt_trichotomy m n with hlt | heq | hgt
    · -- m < n
      simp [MakeTree.substitute_leaf_lt ty' hlt, red_cand, shift_t_ctx_lt _ _ hlt]
    · -- m = n
      simp [heq, MakeTree.substitute_leaf_eq n ty', shift_t_ctx_eq]
    · -- m > n
      simp [MakeTree.substitute_leaf_gt ty' hgt, red_cand, shift_t_ctx, Nat.compare_eq_gt.mpr hgt]
  | .Bind ty_inner =>
    simp only [MakeTree.substitute_bind, red_cand]
    constructor
    · intro ht Y hrcY
      have hctx' : ∀ m, RedCand (shift_t_ctx 0 t_ctx Y m) := shift_t_ctx_0_RedCand hrcY hctx
      have hrc_eq : ∀ t', red_cand t_ctx ty' t' ↔ red_cand (shift_t_ctx 0 t_ctx Y) (MakeTree.shift 0 ty') t' :=
        red_cand_shift t_ctx Y ty' 0 hrcY hctx
      have h_eq_pred : red_cand t_ctx ty' = red_cand (shift_t_ctx 0 t_ctx Y) (MakeTree.shift 0 ty') := by
        funext t'; exact propext (hrc_eq t')
      have hshift_ctx := shift_t_ctx_shift_t_ctx n t_ctx (red_cand t_ctx ty') Y
      have h1 : red_cand (shift_t_ctx (n + 1) (shift_t_ctx 0 t_ctx Y) (red_cand t_ctx ty')) ty_inner t := by
        rw [hshift_ctx]; exact ht Y hrcY
      -- Recursive call with smaller ty_inner and shifted ty'
      have ih := red_cand_shift_substitute (shift_t_ctx 0 t_ctx Y) ty_inner (MakeTree.shift 0 ty') (n + 1) hctx' t
      grind
    · intro ht Y hrcY
      have hctx' : ∀ m, RedCand (shift_t_ctx 0 t_ctx Y m) := shift_t_ctx_0_RedCand hrcY hctx
      have hrc_eq : ∀ t', red_cand t_ctx ty' t' ↔ red_cand (shift_t_ctx 0 t_ctx Y) (MakeTree.shift 0 ty') t' :=
        red_cand_shift t_ctx Y ty' 0 hrcY hctx
      have h_eq_pred : red_cand t_ctx ty' = red_cand (shift_t_ctx 0 t_ctx Y) (MakeTree.shift 0 ty') := by grind
      have hshift_ctx := shift_t_ctx_shift_t_ctx n t_ctx (red_cand t_ctx ty') Y
      have ih := red_cand_shift_substitute (shift_t_ctx 0 t_ctx Y) ty_inner (MakeTree.shift 0 ty') (n + 1) hctx' t
      grind
  | .Node ty1 ty2 =>
    simp only [MakeTree.substitute_node, red_cand, RedCandArrow]
    have ih1 := red_cand_shift_substitute t_ctx ty1 ty' n hctx
    have ih2 := red_cand_shift_substitute t_ctx ty2 ty' n hctx
    grind
termination_by ty

-- Helper: shifting preserves compatibility
open Term in
theorem compat_shift (t_ctx : Nat → Term → Prop) (ctx : List TypeF) (s : List Term)
    (X : Term → Prop) (hrcX : RedCand X) (hctx : ∀ n, RedCand (t_ctx n))
    (hcompat : CompatSubst t_ctx ctx s) :
    CompatSubst (shift_t_ctx 0 t_ctx X) (ctx.map (MakeTree.shift 0)) s := by
  induction hcompat with try grind
  | Cons ctx s ty t _ hrc ih =>
    apply CompatSubst.Cons
    · grind
    · rw [← red_cand_shift t_ctx X ty 0 hrcX hctx]
      grind

-- Coq: Lemma compat_id - identity substitution is compatible
-- Helper: identity substitution starting from index k
open Term in
theorem compat_id_aux (t_ctx : Nat → Term → Prop) (ctx : List TypeF) (k : Nat)
    (hctx : ∀ n, RedCand (t_ctx n)) :
    CompatSubst t_ctx ctx (List.map var (List.range' k ctx.length)) := by
  induction ctx generalizing k with try grind
  | cons ty ctx ih =>
    apply CompatSubst.Cons
    · grind
    · apply RedCandVar
      grind

open Term in
theorem compat_id (t_ctx : Nat → Term → Prop) (ctx : List TypeF)
    (hctx : ∀ n, RedCand (t_ctx n)) : CompatSubst t_ctx ctx (List.map var (List.range ctx.length)) := by
  grind [compat_id_aux, List.range_eq_range']

-- Coq: Lemma context_length - variable index < context length
theorem context_length_aux {ctx : List TypeF} {t : Term} {ty : TypeF}
    (hderiv : TermF ctx t ty) : ∀ n, t = Term.var n → ctx.length > n := by
  induction hderiv <;> grind

open Term in
theorem context_length {ctx : List TypeF} {n : Nat} {ty : TypeF}
    (hderiv : TermF ctx (var n) ty) : ctx.length > n :=
  context_length_aux hderiv n rfl

-- Coq: Lemma free_var_context_length - free variables bounded by context length
open Term MakeTree in
theorem free_var_context_length {ctx : List TypeF} {t : Term} {ty : TypeF}
    (hderiv : TermF ctx t ty) : freeVar t ≤ ctx.length := by
  induction hderiv <;> grind

-- Coq: Lemma termf_red_cand - fundamental theorem of logical relations
-- This is the key lemma: well-typed terms belong to their reducibility candidate
open Term MakeTree in
theorem termf_red_cand (t_ctx : Nat → Term → Prop) (ctx : List TypeF) (s : List Term)
    (t : Term) (ty : TypeF)
    (hctx : ∀ n, RedCand (t_ctx n))
    (hcompat : CompatSubst t_ctx ctx s)
    (hderiv : TermF ctx t ty) :
    red_cand t_ctx ty (substituteList 0 t s) := by
  induction hderiv generalizing t_ctx s with try grind
  | AbsF hderiv' ih =>
    simp only [lam, substituteList_bind]
    apply red_cand_arrow_substitute
    · grind
    · grind
    · intro t2 ht2
      have ih' := ih t_ctx (t2 :: s) hctx (CompatSubst.Cons _ s _ t2 hcompat ht2)
      grind
  | @AppF ctx' t1 ty' ty'' t2 _ _ ih1 ih2 =>
    simp only [app, substituteList_node]
    exact ih1 t_ctx s hctx hcompat _ (ih2 t_ctx s hctx hcompat)
  | TAbsF  _ ih =>
    intro X hrcX
    apply ih (shift_t_ctx 0 t_ctx X) s
    · intro n
      simp only [shift_t_ctx]
      match n with
      | 0 => grind
      | m + 1 => simp only [Nat.compare_eq_gt.mpr (Nat.zero_lt_succ m)]; grind
    · exact compat_shift t_ctx _ s X hrcX hctx hcompat
  | TAppF _ ih =>
    have h := ih t_ctx s hctx hcompat
    apply (red_cand_shift_substitute t_ctx _ _ 0 hctx _).mp
    apply h (red_cand t_ctx _) (red_cand_RedCand t_ctx _ hctx)

-- Coq: Lemma termf_norm : any well-typed term is normalizing
open Term MakeTree in
theorem termf_norm {ctx : List TypeF} {t : Term} {ty : TypeF}
    (hderiv : TermF ctx t ty) : Normalizing t := by
  -- Use substituteList with identity substitution (variables)
  have hfv := free_var_context_length hderiv
  have hid : substituteList 0 t (List.map var (List.range ctx.length)) = t :=
    substituteList_id t ctx.length hfv
  rw [← hid]
  have hrc := red_cand_RedCand (fun _ => Normalizing) ty (fun _ => SNRedCand)
  apply RedCand_Normalizing hrc
  exact termf_red_cand (fun _ => Normalizing) ctx _ t ty
    (fun _ => SNRedCand)
    (compat_id (fun _ => Normalizing) ctx (fun _ => SNRedCand))
    hderiv

-- Coq: Lemma compat_length - compatible substitution preserves length
theorem compat_length {t_ctx : Nat → Term → Prop} {ctx : List TypeF} {s : List Term}
    (hcompat : CompatSubst t_ctx ctx s) : ctx.length = s.length := by
  induction hcompat with
  | Nil => rfl
  | Cons _ _ _ _ _ _ ih => simp [ih]

-- Coq: Lemma omegaTypeF - example typing derivation for the omega combinator
-- nil ⊢ λ(#0@#0) : (∀α. α⇒α) ⇒ (∀α. α⇒α)
open Term in
example : TermF [] (lam (app (var 0) (var 0)))
    (TypeF.arrow (TypeF.forallTy (TypeF.arrow (TypeF.tvar 0) (TypeF.tvar 0)))
                 (TypeF.forallTy (TypeF.arrow (TypeF.tvar 0) (TypeF.tvar 0)))) :=
  .AbsF <| .AppF (.TAppF .VarF0) .VarF0

-- Coq: Lemma termf_normal_form - computes the normal form of any well-typed term
open Term MakeTree in
def termf_normal_form {ctx : List TypeF} {t : Term} {ty : TypeF}
    (hderiv : TermF ctx t ty) : NormalFormResult t :=
  normal_form t (termf_norm hderiv)

--------- Performance testing materials not ported from Rocq

-- Church numeral type: ∀α. (α → α) → α → α
open TypeF in
def fNatType : TypeF := ∀. &.0 ⇒ ( &.0 ⇒ &.0) ⇒ &.0

/--
info: MakeTree.Bind
  (MakeTree.Node
    (MakeTree.Leaf 0)
    (MakeTree.Node (MakeTree.Node (MakeTree.Leaf 0) (MakeTree.Leaf 0)) (MakeTree.Leaf 0)))
-/
#guard_msgs in
#eval fNatType

-- Church zero: λx. λf. x  (type: ∀α. α → (α → α) → α)
def fNatZero : Term := .lam (.lam (.var 1))

def fNatZeroTyped : TermF ctx fNatZero fNatType :=
  .TAbsF <| .AbsF <| .AbsF <| .VarFS <| .VarF0

-- Church successor: λn. λx. λf. f (n x f)  (swapped x and f)
def fNatSucc : Term := .lam (.lam (.lam (.app (.var 0) (.app (.app (.var 2) (.var 1)) (.var 0)))))

open TypeF in
def fNatSuccTyped : TermF ctx fNatSucc (fNatType ⇒ fNatType) :=
  -- λn : fNatType
  .AbsF <|
  -- ∀α introduction (shifts context)
  .TAbsF <|
  -- λx : α
  .AbsF <|
  -- λf : α → α
  .AbsF <|
  -- f (n x f) : apply f to (n x f)
  .AppF .VarF0  -- f : α → α (index 0)
  -- n x f : instantiate n at α, apply to x, apply to f
  (.AppF
    (.AppF
      (.TAppF <| .VarFS <| .VarFS <| .VarF0)  -- n at index 2, instantiated at α
      (.VarFS <| .VarF0))  -- x at index 1
    .VarF0)  -- f at index 0

-- Church addition: λm. λn. λx. λf. m (n x f) f  (swapped x and f)
def fNatAdd : Term := .lam (.lam (.lam (.lam
  (.app (.app (.var 3) (.app (.app (.var 2) (.var 1)) (.var 0))) (.var 0)))))

open TypeF in
def fNatAddTyped : TermF ctx fNatAdd (fNatType ⇒ fNatType ⇒ fNatType) :=
  -- λm : fNatType
  .AbsF <|
  -- λn : fNatType
  .AbsF <|
  -- ∀α introduction
  .TAbsF <|
  -- λx : α
  .AbsF <|
  -- λf : α → α
  .AbsF <|
  -- m (n x f) f
  .AppF
    (.AppF
      (.TAppF <| .VarFS <| .VarFS <| .VarFS <| .VarF0)  -- m at index 3, instantiated at α
      (.AppF
        (.AppF
          (.TAppF <| .VarFS <| .VarFS <| .VarF0)  -- n at index 2, instantiated at α
          (.VarFS <| .VarF0))  -- x at index 1
        .VarF0))  -- f at index 0
    .VarF0  -- f at index 0

open TypeF in
def fNatAddTyped' (x : TermF ctx t fNatType) (y : TermF ctx t' fNatType) : TermF ctx (.app (.app fNatAdd t) t') fNatType :=
  .AppF (.AppF fNatAddTyped x) y

-- Build f^n(x) = f (f (... (f x)...)) with n applications
-- In context where f is var 0 and x is var 1
def fNatBody : Nat → Term
  | 0 => .var 1      -- x
  | n + 1 => .app (.var 0) (fNatBody n)  -- f (f^n(x))

-- Church numeral for n in normal form: λx. λf. f^n(x)
def fNatOfNat (n : Nat) : Term := .lam (.lam (fNatBody n))

-- Helper: typing derivation for f^n(x) : α
-- Context is [α → α, α, ...] where f : α → α at index 0, x : α at index 1
open TypeF in
def fNatBodyTyped (n : Nat) :
    TermF ((&.0 ⇒ &.0) :: &.0 :: ctx) (fNatBody n) &.0 :=
  match n with
  | 0 => .VarFS <| .VarF0  -- x : α at index 1
  | n + 1 => .AppF .VarF0 (fNatBodyTyped n)  -- f (f^n(x))

-- Typing derivation: fNatOfNat n : fNatType
def fNatOfNatTyped (n : Nat) : TermF ctx (fNatOfNat n) fNatType :=
  .TAbsF <| .AbsF <| .AbsF <| fNatBodyTyped n

example : fNatOfNat 0 = fNatZero := rfl
example : fNatOfNat 3 = .lam (.lam (.app (.var 0) (.app (.var 0) (.app (.var 0) (.var 1))))) := rfl

-- Church multiplication: λm. λn. λx. λf. n x (λy. m y f)
-- Computes m*n by applying (λy. m y f) = "apply f m times" n times, starting from x
def fNatMult : Term := .lam (.lam (.lam (.lam (
  .app (.app (.var 2) (.var 1))
       (.lam (.app (.app (.var 4) (.var 0)) (.var 1)))))))

open TypeF in
def fNatMultTyped : TermF ctx fNatMult (fNatType ⇒ fNatType ⇒ fNatType) :=
  .AbsF <| .AbsF <| .TAbsF <| .AbsF <| .AbsF <|
  .AppF
    (.AppF (.TAppF <| .VarFS <| .VarFS <| .VarF0) (.VarFS <| .VarF0))
    (.AbsF <| .AppF (.AppF (.TAppF <| .VarFS <| .VarFS <| .VarFS <| .VarFS <| .VarF0) .VarF0) (.VarFS <| .VarF0))

-- Church exponentiation: exp b e = e 1 (mult b)
-- where 1 = λx.λf. f x, and (mult b) n = b * n
-- This iterates "multiply by b" e times, starting from 1
-- Note: uses higher-order instantiation (e at type fNatType → fNatType)
def fNatExp : Term :=
  -- λb. λe. e 1 (λn. mult b n)
  -- where 1 and mult are inlined
  .lam <| .lam <|  -- λb. λe.
    .app (.app (.var 0)  -- e applied to:
               (.lam (.lam (.app (.var 0) (.var 1)))))  -- Church 1 = λx.λf. f x
         (.lam <|  -- λn.
           .lam <| .lam <|  -- λx. λf.  (result of mult b n)
             .app (.app (.var 2) (.var 1))  -- n x applied to:
                  (.lam (.app (.app (.var 5) (.var 0)) (.var 1))))  -- λy. b y f

-- The typing requires instantiating e at type fNatType (higher-order instantiation)
-- e : ∀α. α → (α → α) → α  is instantiated at fNatType to get
-- e[fNatType] : fNatType → (fNatType → fNatType) → fNatType
-- Then applied to Church 1 : fNatType and (λn. mult b n) : fNatType → fNatType
open TypeF in
def fNatExpTyped : TermF ctx fNatExp (fNatType ⇒ fNatType ⇒ fNatType) :=
  -- λb : fNatType
  .AbsF <|
  -- λe : fNatType
  .AbsF <|
  -- e[fNatType] 1 (mult b)
  .AppF
    (.AppF
      -- e instantiated at fNatType (e is at index 0)
      (.TAppF <| .VarF0)
      -- Church 1 = λx.λf. f x : fNatType
      (.TAbsF <| .AbsF <| .AbsF <|
        .AppF .VarF0 (.VarFS <| .VarF0)))  -- f x
    -- λn. mult b n : fNatType → fNatType
    (.AbsF <|  -- λn : fNatType (now n=0, e=1, b=2)
      .TAbsF <|  -- introduces α
      .AbsF <|   -- λx : α (now x=0, n=1, e=2, b=3)
      .AbsF <|   -- λf : α → α (now f=0, x=1, n=2, e=3, b=4)
      -- body: (n x) (λy. (b y) f)
      .AppF
        (.AppF
          (.TAppF <| .VarFS <| .VarFS <| .VarF0)  -- n at index 2
          (.VarFS <| .VarF0))                       -- x at index 1
        (.AbsF <|  -- λy : α (now y=0, f=1, x=2, n=3, e=4, b=5)
          .AppF
            (.AppF
              (.TAppF <| .VarFS <| .VarFS <| .VarFS <| .VarFS <| .VarFS <| .VarF0)  -- b at index 5
              .VarF0)  -- y at index 0
            (.VarFS <| .VarF0)))  -- f at index 1

def testTerm (n : Nat) : Term :=
  .app (.app fNatExp (fNatOfNat 2)) (fNatOfNat n)

-- testTerm n computes 2^n and is always well-typed
def testTermTyped (n : Nat) : TermF ctx (testTerm n) fNatType :=
  .AppF (.AppF fNatExpTyped (fNatOfNatTyped 2)) (fNatOfNatTyped n)

-- 2^n + 2^n
def doublePow2 (n : Nat) : Term :=
  .app (.app fNatAdd (testTerm n)) (testTerm n)

def doublePow2Typed (n : Nat) : TermF ctx (doublePow2 n) fNatType :=
  .AppF (.AppF fNatAddTyped (testTermTyped n)) (testTermTyped n)

-- Proposition: normal form of 2^(n+1) equals normal form of 2^n + 2^n
abbrev pow2DoubleEq (n : Nat) : Prop :=
  (termf_normal_form (ctx := []) (testTermTyped (n + 1))).normalForm =
  (termf_normal_form (ctx := []) (fNatAddTyped' (testTermTyped n) (testTermTyped n))).normalForm

section
open Lean Meta
def runPow2DoubleTest (n : Nat) : MetaM Unit := do
  let goalType := mkApp (mkConst ``pow2DoubleEq) (mkNatLit n)
  let goalMVar ← Meta.mkFreshExprMVar goalType
  let mvarId := goalMVar.mvarId!
  let startTime ← IO.monoNanosNow
  let result ← Lean.Meta.Tactic.Cbv.cbvGoal mvarId
  let endTime ← IO.monoNanosNow
  let tacticMs := (endTime - startTime).toFloat / 1000000.0
  if result.isSome then
    throwError "cbv did not fully reduce pow2DoubleEq {n}"
  let startTime ← IO.monoNanosNow
  Meta.checkWithKernel goalMVar
  let endTime ← IO.monoNanosNow
  let kernelMs := (endTime - startTime).toFloat / 1000000.0
  IO.println s!"pow2DoubleEq {n}: cbv {tacticMs} ms, kernel {kernelMs} ms"


def runPow2DoubleTests : MetaM Unit := do
  IO.println "=== pow2DoubleEq Benchmark ==="
  for n in [0, 1, 2, 3, 4, 5, 6] do
    runPow2DoubleTest n

set_option maxRecDepth 10000 in
#eval runPow2DoubleTests
end
