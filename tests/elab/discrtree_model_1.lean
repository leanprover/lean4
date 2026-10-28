/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Simmons
-/
module
public import Lean.Expr
import all Init.Data.Array.BinSearch
import all Lean.Data.Name
import all Lean.Expr

open Lean

set_option doc.verso true

/-!
# Discrimination Trees

A discrimination tree is a map whose keys are structured expressions with wildcard matching
Consider a discrimination tree that has had the following key/value pairs inserted:

 - `g (s z) z ↦ a`
 - `g * (s *) ↦ b`
 - `g (s *) * ↦ c`

In such a tree,
looking up {lit}`g (s z) (s z)` should return the set {lit}`{b, c}`,
looking up {lit}`g z (s z)` should return the set {lit}`{b}`,
looking up {lit}`g (s (s z)) z` should return {lit}`{c}`, and
looking up {lit}`g (s z) z` should return {lit}`{a, c}`.

A discrimination tree also supports wildcards in the keys: looking up {lit}`g (s z) *`
returns the set {lit}`{a, b, c}`.
-/

/--
In Lean's actual implementation, keys are {name}`Expr` values and the implementation does
significant simplification (e.g. reduction to weak-head normal form) during both insertion and
lookup. Our simplified model assumes that expressions are already reduced to shapes.
-/
inductive ExprShape where
    /--
    Identical to {name}`Expr.lit`.
    -/
  | lit : Literal → ExprShape
    /--
    {given -show}`c, e1, e2, e3` The term
    {lit}`c e1 e2 e3` is represented as {lean (type := "ExprShape")}`.const c #[e3, e2, e1]`.
    -/
  | const (declName : Name) (args : Array ExprShape)
    /--
    {given -show}`x, e1, e2, e3` The term
    {lit}`x e1 e2 e3` is represented as {lean (type := "ExprShape")}`.fvar x #[e3, e2, e1]`.
    -/
  | fvar (fvarId : FVarId) (args : Array ExprShape)
    /- `e1 → _` or, equivalently, `∀ _ : e1, _`: only the domain of the forall is tracked. -/
  | arrow (domain : ExprShape)
    /- Anything else -/
  | other
    /- Wildcard -/
  | star
deriving BEq

/--
Two shapes _unify_ if their wildcards can be replaced in a way that makes the terms identical.
-/
inductive ExprShape.Unify : ExprShape → ExprShape → Prop where
  | star_left : Unify .star e
  | star_right : Unify e .star
  | lit : Unify (.lit l) (.lit l)
  | const : (h_len : args.size = args'.size) →
      (∀ i, ∀ h : i < args.size, Unify args[i] args'[i]) →
      Unify (.const c args) (.const c args')
  | fvar : (h_len : args.size = args'.size) →
      (∀ i, ∀ h : i < args.size, Unify args[i] args'[i]) →
      Unify (.fvar x args) (.fvar x args')
  | arrow : Unify e e' → Unify (.arrow e) (.arrow e')
  | other : Unify .other .other

/--
Discrimination trees are efficient ways of storing maps from expression shapes to values.
-/
structure KV (α : Type) where
  key : ExprShape
  value : α

abbrev KVMap (α : Type) := List (KV α)

open Classical in
/--
The key operation implemented by tries is unification-based lookup: we take a _query_, a specific
expression shape, find all the keys that unify with that query, and return all the corresponding
values.
-/
noncomputable def KVMap.getUnify (kvs : KVMap α) (query : ExprShape) : List α :=
  (kvs.filter fun kv => kv.key.Unify query).map KV.value

/-!
Ground queries — queries containing no wildcards — are an important special case. The simplification
of unification when queries are ground is called _matching_.
-/

def ExprShape.Ground : ExprShape → Prop
  | .star => False
  | .lit _ => True
  | .const _ args => ∀ e ∈ args, Ground e
  | .fvar _ args => ∀ e ∈ args, Ground e
  | .arrow domain => Ground domain
  | .other => True

/-!
# Trie Implementation

Discrimination trees can be efficiently implemented using a trie data structure, as described
in Peter Graf's "Term Indexing" (LNAI 1053).
-/

/--
{given -show}`g, s`
Tries linearize a structured term into a sequence of keys: the expression `g (s *) "hi"` can be
represented as a linear sequence of keys:
{lean (type := "List Key")}`[.const g 2, .const s 1, .star, .lit (.strVal "hi")]`
-/
inductive Key where
  | star  : Key
  | other : Key
  | lit   : Literal → Key
  | fvar  : FVarId → Nat → Key
  | const : Name → Nat → Key
  | arrow : Key
  deriving Inhabited, BEq, Repr

def Key.lt : Key → Key → Bool
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .fvar n₁ a₁,    .fvar n₂ a₂    => Name.quickLt n₁.name n₂.name || (n₁ == n₂ && a₁ < a₂)
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

def ExprShape.getKeyArgs : ExprShape → Key × Array ExprShape
  | .lit l => ⟨.lit l, #[]⟩
  | .const c args => ⟨.const c args.size, args⟩
  | .fvar x args => ⟨.fvar x args.size, args⟩
  | .arrow e => ⟨.arrow, #[e]⟩
  | .star => ⟨.star, #[]⟩
  | .other => ⟨.other, #[]⟩

/--
Transforms a shape into a sequence of keys.
The returned array is stack ordered, with the first key at the highest array index, to facilitate
an implementation that repeatedly pops from the array.
-/
def ExprShape.getKeyPath : ExprShape → Array Key
  | .lit l => #[.lit l]
  | .const c args => args.flatMap getKeyPath ++ #[.const c args.size]
  | .fvar x args => args.flatMap getKeyPath ++ #[.fvar x args.size]
  | .arrow e => getKeyPath e ++ #[.arrow]
  | .star => #[.star]
  | .other => #[.other]

inductive Trie (α : Type) : Type where
  | leaf (vs : Array α)
  | node (cs : Array (Key × Trie α))
    /-- Special case optimization: node with one (non-star) key -/
  | chain (k : Key) (t : Trie α)
    /-- Special case optimization: chain of _n_ nodes that all have the key .star -/
  | stars (n : Nat) (t : Trie α)

def Trie.empty : Trie α := Trie.node #[]

instance : Inhabited (Trie α) where
  default := Trie.empty

def Key.popStars (n : Nat) (args : Array Key) : Nat × Array Key :=
  match _h : args.back? with
  | .some .star => popStars (n + 1) args.pop
  | _ => ⟨n, args⟩
termination_by args.size
decreasing_by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 _h
  simp

/-- Adds {name}`n` stars to a trie, preserving trie well-formedness. -/
def Trie.mkStars (n : Nat) (t : Trie α) : Trie α :=
  if n = 0 then
    t
  else match t with
  | .stars m t => .stars (n + m) t
  | _ => .stars n t

/-!
## Vibe-Coded Termination Lemmas
-/

theorem Array.binSearchAux_spec {lt : α → α → Bool} {found : Option α → β} {as : Array α} {k : α}
    {lo : Fin (as.size + 1)} {hi : Fin as.size} {h : lo.1 ≤ hi.1} :
    as.binSearchAux lt found k lo hi h = found none ∨
      ∃ a, a ∈ as ∧ lt a k = false ∧ lt k a = false ∧ as.binSearchAux lt found k lo hi h = found (some a) := by
  fun_induction Array.binSearchAux lt found as k lo hi h
  case case5 =>
    rename_i hak hka _
    exact .inr ⟨_, Array.getElem_mem _, Bool.eq_false_iff.2 hak, Bool.eq_false_iff.2 hka, rfl⟩
  all_goals simp_all

theorem Array.binSearchAux_id_eq_some {lt : α → α → Bool} {as : Array α} {k : α}
    {lo : Fin (as.size + 1)} {hi : Fin as.size} {h : lo.1 ≤ hi.1}
    (hs : as.binSearchAux lt id k lo hi h = some a) : a ∈ as ∧ lt a k = false ∧ lt k a = false := by
  rcases Array.binSearchAux_spec (lt := lt) (found := id) (k := k) (h := h) with h' | ⟨_, h1, h2, h3, h4⟩ <;> simp_all

/-- Whatever {name}`Array.binSearch` finds is an element of the array that compares equal to the key. -/
theorem Array.mem_of_binSearch_eq_some {as : Array α} {k : α} {lt : α → α → Bool} {lo hi : Nat} {a : α}
    (hs : as.binSearch k lt lo hi = some a) : a ∈ as ∧ lt a k = false ∧ lt k a = false := by
  unfold Array.binSearch at hs
  dsimp only at hs
  repeat' split at hs
  all_goals first | contradiction | exact Array.binSearchAux_id_eq_some hs

/-- A child trie counts as a subtree for termination purposes. -/
theorem Trie.sizeOf_lt_of_mem {cs : Array (Key × Trie α)} (h : p ∈ cs) :
    sizeOf p.snd < sizeOf (Trie.node cs) := by
  have := Array.sizeOf_lt_of_mem h
  grind only [= Prod.mk.sizeOf_spec, = node.sizeOf_spec]

/-- Removing a star from a run makes the trie smaller. -/
theorem Trie.sizeOf_mkStars_pred_lt (n : Nat) (t : Trie α) :
    sizeOf (mkStars (n - 1) t) < sizeOf (Trie.stars n t) := by
  unfold mkStars
  split
  · simp; omega
  · split <;> simp <;> omega

theorem Key.size_of_popStars_eq (h : Key.popStars n path = (m, rest)) :
    rest.size + m = path.size + n := by
  fun_induction Key.popStars n path with
  | case1 n path hb ih =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    have := ih h
    simp at this ⊢
    omega
  | case2 => simp_all

/-!
## Trie Operations
-/

def Trie.singleton (path : Array Key) (v : α) : Trie α :=
  if path.size = 0 then
    .leaf #[v]
  else
    match _hr : Key.popStars 0 path with
    | ⟨nStars, path⟩ =>
      if _ : nStars > 0 then
        .stars nStars (singleton path v)
      else match _hb : path.back? with
      | .some key => .chain key (singleton path.pop v)
      | .none => .empty -- impossible for ill-formed tries
termination_by path.size
decreasing_by
  all_goals have := Key.size_of_popStars_eq _hr
  · omega
  · obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 _hb
    grind only [= Array.back?_eq_getElem?, = Array.size_pop, = getElem?_neg]

def Trie.insert (path : Array Key) (v : α) (t : Trie α) : Trie α :=
  match t, _h : path.back? with
  | .leaf vs, .none => .leaf (vs.push v)
  | .node cs, .some key =>
    .node <| Id.run $ cs.binInsertM (·.fst < ·.fst)
      (fun (_, c) => (key, insert path.pop v c))
      (fun _ => (key, singleton path.pop v))
      (key, .empty)
  | .chain k c, .some key =>
    if key == k then
      .chain k <| insert path.pop v c
    else
      .node <| #[(k, c)].binInsert (·.fst < ·.fst) (key, singleton path.pop v)
  | .stars n t, .some key =>
    if key == .star then
      .mkStars 1 (insert path.pop v (mkStars (n - 1) t))
    else
      .node #[(.star, .mkStars (n - 1) t), (key, singleton path.pop v)]
  | _, _ => panic! "impossible for well-formed tries"
termination_by path.size
decreasing_by
  all_goals
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 _h
    simp only [Array.pop_push, Array.size_push, Nat.lt_add_one]

/--
A key's _arity_ is a critical part of the relationship between tries and expressions.

 - If we have a trie we expect to act as a map from expression shapes to values, and we pass along
   an edge labeled {lean (type := "Key")}`.lit (.strVal "a")` to a sub-trie, we'd expect that
   sub-trie to contain the values associated with the key {lean}`"a"`.
 - If we pass along an edge labeled {lean (type := "Key")}```.const ``Nat.pred 1```, we'd expect that
   sub-trie to not contain values, but to itself be a trie from shapes to values.
 - If we pass along an edge labeled {lean (type := "Key")}```Key.const ``Prod.mk 2```, we'd expect
   the sub-trie to be a map from shapes to tries that themselves map from shapes to values.

It is the arity of a key that tells us, when we traverse a key-labeled edge to a sub-trie, how much
deeper that takes us in the (a map from shapes to (... (a map from shapes to values))) iteration.
-/
def Key.arity : Key → Nat
  | .lit _ => 0
  | .const _ n => n
  | .fvar _ n => n
  | .arrow => 1
  | .star => 0
  | .other => 0

def Trie.nodeValues : Trie α → Array α
  | .leaf vs => vs
  | _ => #[]

def Trie.getUnify {α} (skip : Nat) (args : Array ExprShape) (accum : Array α) (t : Trie α) : Array α :=
  match skip with
  | skip + 1 =>
    match t with
    | .leaf _ =>
      panic! "impossible for well-formed tries"
    | .node cs =>
      cs.foldl (init := accum) fun accum kc => getUnify (skip + kc.fst.arity) args accum kc.snd
    | .chain k c =>
      getUnify (skip + k.arity) args accum c
    | .stars n c =>
      if skip + 1 >= n then
        getUnify (skip + 1 - n) args accum c
      else
        getUnify 0 args accum (.stars (n - skip - 1) c)
  | 0 =>
    match _h : args.back?.map ExprShape.getKeyArgs with
    | .none =>
      accum ++ t.nodeValues
    | .some keyArgs =>
      if keyArgs.fst == .star then
        getUnify 1 args.pop accum t
      else match t with
        | .leaf _ =>
          panic! "impossible for well-formed tries"
        | .node cs =>
          let accum :=
            match _hs : cs[0]? with
            | .some (.star, t) => getUnify 0 args.pop accum t
            | _ => accum
          match _hf : cs.binSearch (keyArgs.fst, Trie.empty) (·.1 < ·.1) with
          | .none => accum
          | .some ⟨_, c⟩ => getUnify 0 (args.pop ++ keyArgs.snd) accum c
        | .chain k c =>
          if keyArgs.fst == k then
            getUnify 0 (args.pop ++ keyArgs.snd) accum c
          else
            accum
        | .stars n c =>
          getUnify 0 args.pop accum (.mkStars (n - 1) c)
termination_by (sizeOf t, args.size)
decreasing_by
  all_goals first
  | apply Prod.Lex.left
    first
    | exact Trie.sizeOf_lt_of_mem ‹_ ∈ cs›
    | exact Trie.sizeOf_lt_of_mem (Array.mem_of_getElem? _hs)
    | exact Trie.sizeOf_lt_of_mem (Array.mem_of_binSearch_eq_some _hf).1
    | exact Trie.sizeOf_mkStars_pred_lt n c
    | simp only [chain.sizeOf_spec, Nat.lt_add_left_iff_pos, stars.sizeOf_spec, sizeOf_nat, Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_left]; omega
  | apply Prod.Lex.right
    obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.1 _h
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 he
    simp only [Array.pop_push, Array.size_push, Nat.lt_add_one]

/-!
## Well-formed Tries
-/

def isStars : Trie α → Prop
  | .stars _ _ => True
  | _ => False

/--
A discrimination tree is a map from expression shapes to values, but as the arity discussion above
shows, a sub-trie might represent map from shapes to (a map from shapes to (... (a map from shapes
to values))).

This definition of well-formed tries captures how deep we are in that iteration: given
{given (type := "Trie α")}`t`,
{lit}`t.isWf 1` means {name}`t` is a map from expression shapes to values,
{lit}`t.isWf 0` means {name}`t` is a leaf node containing only values, and in general{given -show (type := "Nat")}`n`
{lit}`t.isWf (n+1)` means {name}`t` is a map from expression shapes to well formed tries that map
{name}`n` expressions to values.

Captures other properties of tries: standard {name}`Trie.node` nodes must have 2 children stored in
key-sorted order (one-element children must use {name}`Trie.chain`), chain nodes cannot hold stars,
and two {name}`Trie.stars` nodes cannot appear sequentially.
-/
def Trie.WF {α} : Nat → Trie α → Prop
  | 0, .leaf vs => vs.size > 0
  | 0, _ => False
  | _+1, .leaf _ => False
  | n+1, .node cs => cs.size > 1
      ∧ cs.toList.Pairwise (·.fst < ·.fst)
      ∧ ∀ c, ∀ _ : c ∈ cs, WF (n + c.fst.arity) c.snd
  | n+1, .chain k c => k != .star ∧ c.WF (n + k.arity)
  | n+1, .stars nStars c => nStars > 0
      ∧ n+1 >= nStars
      ∧ ¬isStars c
      ∧ c.WF (n + 1 - nStars)
termination_by _ t => sizeOf t
decreasing_by
  · exact Trie.sizeOf_lt_of_mem ‹c ∈ cs›
  · rw [chain.sizeOf_spec]; omega
  · rw [stars.sizeOf_spec]; omega

/-!
# Vibe-Coded Correctness Lemmas
-/

deriving instance ReflBEq, LawfulBEq for Lean.Literal
deriving instance ReflBEq, LawfulBEq for Lean.FVarId
deriving instance ReflBEq, LawfulBEq for Key


/-!
## Keys are strictly ordered
-/

theorem Name.quickCmpAux_swap : ∀ {n n' : Name}, n.quickCmpAux n' = (n'.quickCmpAux n).swap
  | .anonymous, n => by cases n <;> rfl
  | n, .anonymous => by cases n <;> rfl
  | .num .., .str .. => rfl
  | .str .., .num .. => rfl
  | .num p₁ n₁, .num p₂ n₂ => by
    simp only [Name.quickCmpAux]
    rw [Std.OrientedOrd.eq_swap (a := n₁)]
    cases compare n₂ n₁ <;> simp [Name.quickCmpAux_swap (n := p₁)]
  | .str p₁ s₁, .str p₂ s₂ => by
    simp only [Name.quickCmpAux]
    rw [Std.OrientedOrd.eq_swap (a := s₁)]
    cases compare s₂ s₁ <;> simp [Name.quickCmpAux_swap (n := p₁)]

theorem Name.quickCmpAux_eq_iff : ∀ {n n' : Name}, n.quickCmpAux n' = .eq ↔ n = n'
  | .anonymous, n => by cases n <;> simp [Name.quickCmpAux]
  | n, .anonymous => by cases n <;> simp [Name.quickCmpAux]
  | .num .., .str .. => by simp [Name.quickCmpAux]
  | .str .., .num .. => by simp [Name.quickCmpAux]
  | .num p₁ n₁, .num p₂ n₂ => by
    simp only [Name.quickCmpAux]; split <;> simp_all [Name.quickCmpAux_eq_iff]
  | .str p₁ s₁, .str p₂ s₂ => by
    simp only [Name.quickCmpAux]; split <;> simp_all [Name.quickCmpAux_eq_iff]

private theorem Name.quickCmpAux_num (p p' : Name) (n n' : Nat) :
    (Name.num p n).quickCmpAux (.num p' n') = (compare n n').then (p.quickCmpAux p') := by
  simp only [Name.quickCmpAux]; cases compare n n' <;> rfl

private theorem Name.quickCmpAux_str (p p' : Name) (s s' : String) :
    (Name.str p s).quickCmpAux (.str p' s') = (compare s s').then (p.quickCmpAux p') := by
  simp only [Name.quickCmpAux]; cases compare s s' <;> rfl

theorem Name.quickCmpAux_isLE_trans : ∀ {a b c : Name},
    (a.quickCmpAux b).isLE → (b.quickCmpAux c).isLE → (a.quickCmpAux c).isLE
  | .anonymous, b, c, _, _ => by cases c <;> simp [Name.quickCmpAux]
  | .num .., .anonymous, _, h, _ => by simp [Name.quickCmpAux] at h
  | .str .., .anonymous, _, h, _ => by simp [Name.quickCmpAux] at h
  | .num .., .num .., .anonymous, _, h => by simp [Name.quickCmpAux] at h
  | .num .., .str .., .anonymous, _, h => by simp [Name.quickCmpAux] at h
  | .str .., .str .., .anonymous, _, h => by simp [Name.quickCmpAux] at h
  | .str .., .num .., _, h, _ => by simp [Name.quickCmpAux] at h
  | .num .., .str .., .num .., _, h => by simp [Name.quickCmpAux] at h
  | .num .., .num .., .str .., _, _ => by simp [Name.quickCmpAux]
  | .num .., .str .., .str .., _, _ => by simp [Name.quickCmpAux]
  | .str .., .str .., .num .., _, h => by simp [Name.quickCmpAux] at h
  | .num p₁ n₁, .num p₂ n₂, .num p₃ n₃, hab, hbc => by
    simp only [Name.quickCmpAux_num, Ordering.isLE_then_iff_and] at *
    refine ⟨Std.TransOrd.isLE_trans hab.1 hbc.1, ?_⟩
    rcases hab.2 with h | h
    · exact .inl (Std.TransCmp.lt_of_lt_of_isLE h hbc.1)
    · rcases hbc.2 with h' | h'
      · exact .inl (Std.TransCmp.lt_of_isLE_of_lt hab.1 h')
      · exact .inr (Name.quickCmpAux_isLE_trans h h')
  | .str p₁ n₁, .str p₂ n₂, .str p₃ n₃, hab, hbc => by
    simp only [Name.quickCmpAux_str, Ordering.isLE_then_iff_and] at *
    refine ⟨Std.TransOrd.isLE_trans hab.1 hbc.1, ?_⟩
    rcases hab.2 with h | h
    · exact .inl (Std.TransCmp.lt_of_lt_of_isLE h hbc.1)
    · rcases hbc.2 with h' | h'
      · exact .inl (Std.TransCmp.lt_of_isLE_of_lt hab.1 h')
      · exact .inr (Name.quickCmpAux_isLE_trans h h')

instance : Std.TransCmp Name.quickCmpAux where
  eq_swap := Name.quickCmpAux_swap
  isLE_trans := Name.quickCmpAux_isLE_trans

theorem Name.quickCmp_eq_compareLex :
    Name.quickCmp = compareLex (compareOn Name.hash) Name.quickCmpAux := by
  funext a b
  simp only [Name.quickCmp, compareLex, compareOn]
  cases compare a.hash b.hash <;> rfl

instance : Std.TransCmp Name.quickCmp := by
  rw [Name.quickCmp_eq_compareLex]; infer_instance

theorem Name.quickLt_irrefl (n : Name) : n.quickLt n = false := by
  simp [Name.quickLt, Std.ReflCmp.compare_self]

theorem Name.quickLt_trans {a b c : Name} (h₁ : a.quickLt b) (h₂ : b.quickLt c) : a.quickLt c := by
  simp only [Name.quickLt, beq_iff_eq] at *
  exact Std.TransCmp.lt_trans h₁ h₂

theorem Name.quickCmp_swap {n n' : Name} : n.quickCmp n' = (n'.quickCmp n).swap :=
  Std.OrientedCmp.eq_swap

theorem Name.eq_of_not_quickLt {n n' : Name} (h₁ : n.quickLt n' = false) (h₂ : n'.quickLt n = false) : n = n' := by
  simp only [Name.quickLt, Name.quickCmp_swap (n := n'), beq_eq_false_iff_ne] at h₁ h₂
  have : n.quickCmp n' = .eq := by cases h : n.quickCmp n' <;> simp_all
  simp only [Name.quickCmp] at this
  split at this
  · exact Name.quickCmpAux_eq_iff.mp this
  · contradiction

theorem FVarId.beq_eq_name_beq {x y : FVarId} : (x == y) = (x.name == y.name) := by
  cases x; cases y; rfl

theorem String.eq_of_not_lt {s t : String} (h₁ : ¬ s < t) (h₂ : ¬ t < s) : s = t := by grind

theorem Literal.eq_of_not_lt {l l' : Literal} (h₁ : l.lt l' = false) (h₂ : l'.lt l = false) : l = l' := by
  cases l <;> cases l' <;> simp_all [Literal.lt]
  · omega
  · exact String.eq_of_not_lt h₁ h₂

theorem Literal.lt_irrefl (l : Literal) : l.lt l = false := by
  cases l <;> simp [Literal.lt, Std.lt_irrefl]

theorem Literal.lt_trans {a b c : Literal} (h₁ : a.lt b) (h₂ : b.lt c) : a.lt c := by
  cases a <;> cases b <;> cases c <;> simp_all [Literal.lt]
  · omega
  · exact Std.lt_trans h₁ h₂

theorem Key.eq_of_not_lt {k k' : Key} (h₁ : k.lt k' = false) (h₂ : k'.lt k = false) : k = k' := by
  cases k <;> cases k' <;> simp_all [Key.lt, Key.ctorIdx]
  case lit.lit l l' => exact Literal.eq_of_not_lt (by simpa [LT.lt] using h₁) (by simpa [LT.lt] using h₂)
  case fvar.fvar x a y b =>
    have h := Name.eq_of_not_quickLt h₁.1 h₂.1
    have hxy : x = y := by cases x; cases y; simp_all
    subst hxy
    have := h₁.2 (by simp); have := h₂.2 (by simp)
    exact ⟨rfl, by omega⟩
  case const.const x a y b =>
    have h := Name.eq_of_not_quickLt h₁.1 h₂.1
    have := h₁.2 h; have := h₂.2 h.symm; exact ⟨h, by omega⟩

theorem Key.lt_iff {a b : Key} : a < b ↔ Key.lt a b = true := Iff.rfl

private theorem Literal.lt_iff {a b : Literal} : a < b ↔ a.lt b = true := Iff.rfl

theorem Key.lt_irrefl (k : Key) : ¬ k < k := by
  rw [Key.lt_iff]
  cases k <;> simp [Key.lt, Name.quickLt_irrefl, Literal.lt_iff, Literal.lt_irrefl]

theorem Key.lt_trans {a b c : Key} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [Key.lt_iff] at *
  cases a <;> cases b <;> cases c <;> simp only [Key.lt, decide_eq_true_eq] at * <;>
    (try (simp only [Key.ctorIdx] at *; omega))
  case lit.lit.lit => simp only [Literal.lt_iff] at *; exact Literal.lt_trans h₁ h₂
  all_goals simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at *
  case fvar.fvar.fvar x a y b z c =>
    have hfv {u v : FVarId} : (u == v) = true ↔ u = v := by
      cases u; cases v; simp [FVarId.beq_eq_name_beq]
    simp only [hfv] at *
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · exact .inl (Name.quickLt_trans h₁ h₂)
    · exact .inl h₁
    · exact .inl h₂
    · exact .inr ⟨rfl, by omega⟩
  case const.const.const x a y b z c =>
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · exact .inl (Name.quickLt_trans h₁ h₂)
    · exact .inl h₁
    · exact .inl h₂
    · exact .inr ⟨rfl, by omega⟩

theorem Key.lt_asymm {a b : Key} (h : a < b) : ¬ b < a :=
  fun h' => Key.lt_irrefl a (Key.lt_trans h h')

theorem Key.not_lt_star (k : Key) : ¬ k < .star := by
  rw [Key.lt_iff]; cases k <;> simp [Key.lt, Key.ctorIdx]


/-!
## Sorted children
-/

theorem Trie.binSearch_key {cs : Array (Key × Trie α)}
    (h : cs.binSearch (key, d) (·.fst < ·.fst) = some c) : c ∈ cs ∧ c.fst = key := by
  have ⟨hmem, h₁, h₂⟩ := Array.mem_of_binSearch_eq_some h
  exact ⟨hmem, Key.eq_of_not_lt (by simpa only [Key.lt_iff, Bool.decide_eq_true] using h₁)
    (by simpa only [Key.lt_iff, Bool.decide_eq_true] using h₂)⟩

def Spec.KeysSorted (cs : Array (Key × Trie α)) : Prop :=
  (cs.toList.map Prod.fst).Pairwise (· < ·)

/--
The children are strictly sorted by key. {name}`Trie.insert` maintains this, and
{name}`Trie.getUnify` relies on it to find children with {name}`Array.binSearch` and the wildcard
child at index 0.
-/
theorem Spec.KeysSorted.lt {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i j : Nat}
    (hi : i < cs.size) (hj : j < cs.size) (hij : i < j) : cs[i].fst < cs[j].fst := by
  have := List.pairwise_iff_getElem.1 hs i j (by simpa using hi) (by simpa using hj) hij
  simpa using this

theorem Spec.KeysSorted.eq_of_mem {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    (ha : a ∈ cs) (hb : b ∈ cs) (h : a.fst = b.fst) : a = b := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hb
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact absurd (h ▸ hs.lt hi hj hij) (Key.lt_irrefl _)
  · rfl
  · exact absurd (h ▸ hs.lt hj hi hij) (Key.lt_irrefl _)

theorem Array.binSearchAux_complete {lt : α → α → Bool} {as : Array α} {k x : α}
    (h_sorted : ∀ i j (hi : i < as.size) (hj : j < as.size), i < j → lt as[i] as[j])
    (h_asymm : ∀ a b, lt a b → lt b a → False)
    (h_k : ∀ a, lt a k = lt a x ∧ lt k a = lt x a) (h_x : lt x x = false)
    {lo : Fin (as.size + 1)} {hi : Fin as.size} {h : lo.1 ≤ hi.1} {j : Nat} (hj : j < as.size)
    (h_lo : lo.1 ≤ j) (h_hi : j ≤ hi.1) (h_eq : as[j] = x) :
    ∃ y, as.binSearchAux lt id k lo hi h = some y := by
  have below {m : Nat} (hm : m < as.size) (hjm : j ≤ m) : lt as[m] k = false := by
    rw [(h_k _).1]
    rcases Nat.lt_or_eq_of_le hjm with hjm | rfl
    · grind
    · simpa [h_eq] using h_x
  have above {m : Nat} (hm : m < as.size) (hjm : m ≤ j) : lt k as[m] = false := by
    rw [(h_k _).2]
    rcases Nat.lt_or_eq_of_le hjm with hjm | rfl
    · grind
    · simpa [h_eq] using h_x
  fun_induction Array.binSearchAux lt id as k lo hi h with
  | case1 lo hi _ m a hlt _ _ ih =>
    refine ih ?_ h_hi
    show m + 1 ≤ j
    have : m < as.size := by omega
    have := below this
    by_cases hjm : j ≤ m
    · simp_all [a]
    · omega
  | case2 lo hi _ m a hlt _ _ =>
    have := below (m := m) (by omega) (by omega); simp_all [a]
  | case3 lo hi _ m a _ hgt h' _ =>
    have := above (m := m) (by omega) (by omega); simp_all [a]
  | case4 lo hi _ m a _ hgt _ _ ih =>
    refine ih h_lo ?_
    show j ≤ m - 1
    have : m < as.size := by omega
    have := above this
    by_cases hjm : m ≤ j
    · simp_all [a]
    · omega
  | case5 => exact ⟨_, rfl⟩

theorem Array.binSearch_complete {lt : α → α → Bool} {as : Array α} {k x : α}
    (h_sorted : ∀ i j (hi : i < as.size) (hj : j < as.size), i < j → lt as[i] as[j])
    (h_asymm : ∀ a b, lt a b → lt b a → False)
    (h_k : ∀ a, lt a k = lt a x ∧ lt k a = lt x a) (h_x : lt x x = false) (hx : x ∈ as) :
    ∃ y, as.binSearch k lt = some y := by
  obtain ⟨j, hj, h_eq⟩ := Array.mem_iff_getElem.1 hx
  unfold Array.binSearch
  simp only [show 0 < as.size by omega, ↓reduceDIte, show as.size - 1 < as.size by omega, ↓reduceIte,
    Nat.zero_le]
  exact Array.binSearchAux_complete h_sorted h_asymm h_k h_x hj (Nat.zero_le _) (by simp; omega) h_eq

/-- In a sorted node, binary search finds the child with a given key. -/
theorem Spec.KeysSorted.binSearch_eq {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    (hc : (k, c) ∈ cs) : cs.binSearch (k, d) (·.fst < ·.fst) = some (k, c) := by
  obtain ⟨y, hy⟩ := Array.binSearch_complete (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst)) (k := (k, d))
    (x := (k, c))
    (fun i j hi hj hij => by simpa using hs.lt hi hj hij)
    (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    (fun _ => ⟨rfl, rfl⟩) (by simpa using Key.lt_irrefl k) hc
  have ⟨hy_mem, hy_key⟩ := Trie.binSearch_key hy
  rw [hy, hs.eq_of_mem hy_mem hc hy_key]

/-- In a sorted node, the wildcard child, if any, comes first. -/
theorem Spec.KeysSorted.getElem?_zero {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    (hc : (.star, c) ∈ cs) : cs[0]? = some (.star, c) := by
  obtain ⟨j, hj, h_eq⟩ := Array.mem_iff_getElem.1 hc
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [Array.getElem?_eq_getElem hj, h_eq]
  · have := hs.lt (by omega) hj hj0
    rw [h_eq] at this
    exact absurd this (Key.not_lt_star _)


/-!
## Binary insertion
-/

theorem Array.modifyM_id_run {xs : Array α} {i : Nat} {f : α → Id α} (hi : i < xs.size) :
    (xs.modifyM i f).run = xs.set i (f xs[i]).run := by
  simp [modifyM, hi]

theorem Array.binInsertAux_id_cases {lt : α → α → Bool} {merge : α → Id α} {add : Unit → Id α}
    {as : Array α} {k : α} (h_asymm : ∀ a b, lt a b → lt b a → False)
    (lo hi : Fin as.size) (h : lo.1 ≤ hi.1) (w : lt as[lo] k) (whi : lt k as[hi]) :
    (∃ i, ∃ hj : i < as.size, lt as[i] k = false ∧ lt k as[i] = false ∧
        (binInsertAux lt merge add as k lo hi h w).run = as.set i (merge as[i]).run) ∨
    (∃ i, ∃ hj : i ≤ as.size, (binInsertAux lt merge add as k lo hi h w).run = as.insertIdx i (add ()).run ∧
        (∀ h : 0 < i, lt as[i - 1] k) ∧ (∀ h : i < as.size, lt k as[i])) := by
  fun_induction binInsertAux lt merge add as k lo hi h w with
  | case1 lo hi _ w mid midVal hlt hmid =>
    simp only [Id.run_bind, Id.run_pure]
    refine .inr ⟨lo + 1, by omega, rfl, fun _ => by simpa using w, fun h' => ?_⟩
    have : hi.1 = lo.1 + 1 ∨ hi.1 = lo.1 := by omega
    rcases this with h_eq | h_eq
    · simpa [← h_eq] using whi
    · exact (h_asymm _ _ w (by simpa [Fin.ext_iff, h_eq] using whi)).elim
  | case2 lo hi _ w mid midVal hlt hmid _ _ ih =>
    exact ih whi
  | case3 lo hi _ w mid midVal hlt hgt _ _ _ ih =>
    exact ih hgt
  | case4 lo hi _ w mid midVal hlt hgt =>
    exact .inl ⟨mid, by omega, by simpa using hlt, by simpa using hgt, Array.modifyM_id_run _⟩

/--
{name}`Array.binInsertM` either merges into an element equivalent to the key, or inserts the new
element at a position whose neighbors are ordered around the key.
-/
theorem Array.binInsertM_id_cases {lt : α → α → Bool} {merge : α → Id α} {add : Unit → Id α}
    {as : Array α} {k : α} (h_asymm : ∀ a b, lt a b → lt b a → False) :
    (∃ i, ∃ hj : i < as.size, lt as[i] k = false ∧ lt k as[i] = false ∧
        (as.binInsertM lt merge add k).run = as.set i (merge as[i]).run) ∨
    (∃ i, ∃ hj : i ≤ as.size, (as.binInsertM lt merge add k).run = as.insertIdx i (add ()).run ∧
        (∀ h : 0 < i, lt as[i - 1] k) ∧ (∀ h : i < as.size, lt k as[i])) := by
  have push_eq : as.push (add ()).run = as.insertIdx as.size (add ()).run := by
    simp
  unfold binInsertM
  split
  · grind
  split
  · grind
  split
  · rename_i h0 hlt hgt
    exact .inl ⟨0, by omega, by simpa using hgt, by simpa using hlt, Array.modifyM_id_run _⟩
  split
  · grind
  split
  · rename_i h0 _ _ hlt hgt
    exact .inl ⟨as.size - 1, by omega, by simpa using hlt, by simpa using hgt, Array.modifyM_id_run _⟩
  · rename_i h0 _ _ _ hgt
    exact Array.binInsertAux_id_cases h_asymm _ _ _ _ (by simpa using hgt)


theorem Array.eq_empty_or_eq_push (xs : Array α) : xs = #[] ∨ ∃ (ys : Array α) (y : α), xs = ys.push y := by
  rcases Nat.eq_zero_or_pos xs.size with h | h
  · exact .inl (Array.eq_empty_of_size_eq_zero h)
  · obtain ⟨ys, y, rfl⟩ := Array.exists_push_of_size_pos h
    exact .inr ⟨ys, y, rfl⟩

/-- A stack is determined by the stack left after consuming its top shape, plus that shape's key. -/

theorem List.map_insertIdx' {f : β → γ} {l : List β} {i : Nat} {x : β} :
    (l.insertIdx i x).map f = (l.map f).insertIdx i (f x) := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons y l ih => cases i <;> simp [List.insertIdx_succ_cons, ih]

/-- Inserting between two neighbors that are ordered around the new element keeps a list sorted. -/
theorem List.pairwise_insertIdx_of_neighbors {R : β → β → Prop}
    (h_trans : ∀ {a b c}, R a b → R b c → R a c)
    {l : List β} {i : Nat} {x : β} (hi : i ≤ l.length) (hl : l.Pairwise R)
    (hprev : ∀ h : 0 < i, R (l[i - 1]'(by omega)) x) (hnext : ∀ h : i < l.length, R x l[i]) :
    (l.insertIdx i x).Pairwise R := by
  induction l generalizing i with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hi; subst hi; simp
  | cons y l ih =>
    have hl' := List.pairwise_cons.1 hl
    cases i with
    | zero =>
      rw [List.insertIdx_zero]
      refine List.Pairwise.cons (fun z hz => ?_) hl
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hnext (by simp)
      · exact h_trans (hnext (by simp)) (hl'.1 z hz)
    | succ i =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hi
      rw [List.insertIdx_succ_cons]
      refine List.Pairwise.cons (fun z hz => ?_) (ih hi hl'.2 (fun h => ?_) (fun h => ?_))
      · rcases (List.mem_insertIdx hi).1 hz with rfl | hz
        · grind
        · exact hl'.1 z hz
      · grind
      · grind

theorem Spec.KeysSorted.set {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat} (hi : i < cs.size)
    {y : Key × Trie α} (hy : y.fst = cs[i].fst) : KeysSorted (cs.set i y) := by
  unfold KeysSorted at *
  rw [Array.toList_set, List.map_set, hy]
  have : cs[i].fst = (cs.toList.map Prod.fst)[i]'(by simpa using hi) := by simp
  rwa [this, List.set_getElem_self]

theorem Spec.KeysSorted.insertIdx {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat}
    (hi : i ≤ cs.size) {y : Key × Trie α}
    (hprev : ∀ h : 0 < i, cs[i - 1].fst < y.fst) (hnext : ∀ h : i < cs.size, y.fst < cs[i].fst) :
    KeysSorted (cs.insertIdx i y) := by
  unfold KeysSorted at *
  rw [Array.toList_insertIdx, List.map_insertIdx']
  refine List.pairwise_insertIdx_of_neighbors (R := (· < ·)) Key.lt_trans
    (by simp only [List.length_map, Array.length_toList]; exact hi) hs (fun h => ?_) (fun h => ?_)
  · simp only [List.getElem_map, Array.getElem_toList]; exact hprev h
  · grind


theorem Array.foldl_eq_append_flatMap {xs : Array β} {f : Array α → β → Array α} {g : β → Array α}
    (h : ∀ acc, ∀ x ∈ xs, f acc x = acc ++ g x) (init : Array α) :
    xs.foldl f init = init ++ xs.flatMap g := by
  rcases xs with ⟨l⟩
  simp only [List.foldl_toArray', List.flatMap_toArray, List.mem_toArray] at h ⊢
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, h _ x (by simp), ih _ (fun acc y hy => h acc y (by simp [hy]))]
    simp only [List.flatMap_cons, ← List.append_toArray, Array.toArray_toList, Array.append_assoc]


/-!
## Key paths
-/

/--
{lit}`Spec.ValidPath n p` holds when the stack-ordered key path {lit}`p` encodes exactly {lit}`n`
complete terms: popping a key {lit}`k` from a path of {lit}`n + 1` terms leaves a path of
{lit}`n + k.arity` terms.
-/
inductive Spec.ValidPath : Nat → Array Key → Prop where
  | nil : ValidPath 0 #[]
  | push : ValidPath (n + k.arity) p → ValidPath (n + 1) (p.push k)

theorem Spec.ValidPath.append (hp : ValidPath m p) (hq : ValidPath n q) : ValidPath (m + n) (p ++ q) := by
  induction hq with
  | nil => simpa using hp
  | @push n k q _ ih =>
    rw [← Array.push_append, show m + (n + 1) = (m + n) + 1 by omega]
    exact .push (by rwa [Nat.add_assoc])

theorem Spec.validPath_flatMap_of_forall :
    ∀ (l : List ExprShape), (∀ e ∈ l, ValidPath 1 e.getKeyPath) →
      ValidPath l.length (l.toArray.flatMap ExprShape.getKeyPath)
  | [], _ => by simpa using ValidPath.nil
  | e :: l, h => by
    have := (h e (by simp)).append (validPath_flatMap_of_forall l (fun x hx => h x (by simp [hx])))
    rw [List.flatMap_toArray_cons, List.length_cons, Nat.add_comm]
    exact this

theorem Spec.validPath_getKeyPath : (e : ExprShape) → ValidPath 1 e.getKeyPath
  | .lit l => by rw [ExprShape.getKeyPath]; exact ValidPath.push (n := 0) (k := .lit l) (p := #[]) .nil
  | .star => by rw [ExprShape.getKeyPath]; exact ValidPath.push (n := 0) (k := .star) (p := #[]) .nil
  | .other => by rw [ExprShape.getKeyPath]; exact ValidPath.push (n := 0) (k := .other) (p := #[]) .nil
  | .const c args => by
    rw [ExprShape.getKeyPath]
    have := validPath_flatMap_of_forall args.toList (fun x hx => validPath_getKeyPath x)
    simpa using ValidPath.push (n := 0) (k := .const c args.size) (by simpa [Key.arity] using this)
  | .fvar x args => by
    rw [ExprShape.getKeyPath]
    have := validPath_flatMap_of_forall args.toList (fun x hx => validPath_getKeyPath x)
    simpa using ValidPath.push (n := 0) (k := .fvar x args.size) (by simpa [Key.arity] using this)
  | .arrow e => by
    rw [ExprShape.getKeyPath]
    simpa using ValidPath.push (n := 0) (k := .arrow) (by simpa [Key.arity] using validPath_getKeyPath e)
termination_by e => sizeOf e
decreasing_by
  all_goals first
  | (have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.1 ‹_›); simp +arith; omega)
  | simp +arith

theorem Spec.validPath_empty_iff : ValidPath n #[] ↔ n = 0 := by
  constructor
  · intro h
    generalize hz : (#[] : Array Key) = z at h
    cases h with
    | nil => rfl
    | push => exact absurd hz.symm Array.push_ne_empty
  · rintro rfl; exact .nil

theorem Spec.validPath_zero_iff : ValidPath 0 p ↔ p = #[] := by
  constructor
  · intro h
    generalize hz : 0 = z at h
    cases h with
    | nil => rfl
    | push => omega
  · rintro rfl; exact .nil

theorem Spec.validPath_push_iff : ValidPath n (p.push k) ↔ ∃ m, n = m + 1 ∧ ValidPath (m + k.arity) p := by
  constructor
  · intro h
    generalize hz : p.push k = z at h
    cases h with
    | nil => exact absurd hz Array.push_ne_empty
    | push hv =>
      obtain ⟨rfl, rfl⟩ := Array.push_eq_push.1 hz
      exact ⟨_, rfl, hv⟩
  · rintro ⟨m, rfl, hv⟩; exact .push hv

theorem Key.popStars_of_back {p : Array Key} (h : p.back? ≠ some .star) : Key.popStars n p = (n, p) := by
  rw [Key.popStars]
  split <;> simp_all

theorem Spec.validPath_popStars (h : Key.popStars j p = (m, rest)) (hv : ValidPath n p) :
    j ≤ m ∧ m - j ≤ n ∧ ValidPath (n - (m - j)) rest ∧ rest.back? ≠ some .star := by
  fun_induction Key.popStars j p generalizing n with
  | case1 j p hb ih =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨n', rfl, hv'⟩ := validPath_push_iff.1 hv
    simp only [Array.pop_push, Key.arity, Nat.add_zero] at ih hv' h
    obtain ⟨h1, h2, h3, h4⟩ := ih h hv'
    refine ⟨by omega, by omega, ?_, h4⟩
    rwa [show n' + 1 - (m - j) = n' - (m - (j + 1)) by omega]
  | case2 j p hb =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ h
    simpa using ⟨hv, hb⟩

/-! ## Well-formedness by constructor -/

theorem Trie.wf_leaf : (Trie.leaf vs : Trie α).WF n ↔ n = 0 ∧ vs.size > 0 := by
  cases n <;> simp [Trie.WF]

theorem Trie.wf_node {cs : Array (Key × Trie α)} : (Trie.node cs).WF n ↔
    ∃ m, n = m + 1 ∧ cs.size > 1 ∧ Spec.KeysSorted cs ∧ ∀ c ∈ cs, c.snd.WF (m + c.fst.arity) := by
  cases n <;> simp [Trie.WF, Spec.KeysSorted, List.pairwise_map]

theorem Trie.wf_chain : (Trie.chain k c : Trie α).WF n ↔ ∃ m, n = m + 1 ∧ k ≠ .star ∧ c.WF (m + k.arity) := by
  cases n <;> simp [Trie.WF]

theorem Trie.wf_stars : (Trie.stars j c : Trie α).WF n ↔
    ∃ m, n = m + 1 ∧ j > 0 ∧ m + 1 ≥ j ∧ ¬ isStars c ∧ c.WF (m + 1 - j) := by
  cases n <;> simp [Trie.WF]

theorem Trie.singleton_not_isStars {p : Array Key} (h : p.back? ≠ some .star) (v : α) :
    ¬ isStars (singleton p v) := by
  unfold Trie.singleton
  split
  · simp [isStars]
  · split
    rename_i hr
    rw [Key.popStars_of_back h] at hr
    cases hr
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    split <;> simp [isStars, Trie.empty]

theorem Trie.wf_singleton (hv : Spec.ValidPath n path) (v : α) : (singleton path v).WF n := by
  fun_induction Trie.singleton path v generalizing n with
  | case1 path h0 =>
    obtain rfl := Array.eq_empty_of_size_eq_zero h0
    obtain rfl := Spec.validPath_empty_iff.1 hv
    simp [wf_leaf]
  | case2 path _ m rest hr hm ih =>
    obtain ⟨-, hle, hv', hb⟩ := Spec.validPath_popStars hr hv
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact wf_stars.2 ⟨n', rfl, hm, by omega, singleton_not_isStars hb v, by simpa using ih hv'⟩
  | case3 path _ m rest hr hm key hb ih =>
    obtain ⟨-, -, hv', hns⟩ := Spec.validPath_popStars hr hv
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨n', rfl, hv''⟩ := Spec.validPath_push_iff.1 (by simpa [show m = 0 by omega] using hv')
    refine wf_chain.2 ⟨n', rfl, fun h => hns (by simp [h]), ?_⟩
    exact ih (by simpa using hv'')
  | case4 path h0 m rest hr hm hb =>
    have := Key.size_of_popStars_eq hr
    obtain rfl := Array.back?_eq_none_iff.1 hb
    simp at this
    omega

/-! ## Inserting into sorted children -/

theorem Spec.KeysSorted.binInsertM {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    {merge : Key × Trie α → Id (Key × Trie α)} {add : Unit → Id (Key × Trie α)} {y : Key × Trie α}
    (hmerge : ∀ x ∈ cs, x.fst = y.fst → (merge x).run.fst = y.fst) (hadd : (add ()).run.fst = y.fst) :
    KeysSorted (cs.binInsertM (·.fst < ·.fst) merge add y).run ∧
      cs.size ≤ (cs.binInsertM (·.fst < ·.fst) merge add y).run.size ∧
      (∀ x ∈ (cs.binInsertM (·.fst < ·.fst) merge add y).run,
        x ∈ cs ∨ x = (add ()).run ∨ ∃ x' ∈ cs, x'.fst = y.fst ∧ x = (merge x').run) ∧
      ((∀ x ∈ cs, x.fst ≠ y.fst) → (cs.binInsertM (·.fst < ·.fst) merge add y).run.size = cs.size + 1) := by
  rcases Array.binInsertM_id_cases (as := cs) (k := y) (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst))
      (merge := merge) (add := add)
      (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    with ⟨i, hi, hlt, hgt, hr⟩ | ⟨i, hi, hr, hprev, hnext⟩
  · have hk : cs[i].fst = y.fst :=
      Key.eq_of_not_lt (by simpa [Key.lt_iff] using hlt) (by simpa [Key.lt_iff] using hgt)
    have hm := hmerge _ (Array.getElem_mem hi) hk
    rw [hr]
    refine ⟨hs.set hi (by rw [hm, hk]), by simp, fun x hx => ?_, fun h => absurd hk (h _ (Array.getElem_mem hi))⟩
    rcases Array.mem_or_eq_of_mem_set hx with hx | rfl
    · exact .inl hx
    · exact .inr (.inr ⟨_, Array.getElem_mem hi, hk, rfl⟩)
  · rw [hr]
    refine ⟨hs.insertIdx hi (fun h => by simpa [hadd] using hprev h) (fun h => by simpa [hadd] using hnext h),
      by simp, fun x hx => ?_, fun _ => by simp⟩
    rcases Array.mem_insertIdx.1 hx with rfl | hx
    · exact .inr (.inl rfl)
    · exact .inl hx

theorem Key.star_lt {k : Key} (h : k ≠ .star) : Key.star < k := by
  cases k <;> simp_all [Key.lt_iff, Key.lt, Key.ctorIdx]

theorem Trie.mkStars_of_not_isStars (ht : ¬ isStars t) (hn : n ≠ 0) : mkStars n t = .stars n t := by
  unfold mkStars
  split
  · omega
  · split
    · simp [isStars] at ht
    · rfl

theorem Trie.wf_mkStars_pred (h : (Trie.stars j t : Trie α).WF (m + 1)) : (mkStars (j - 1) t).WF m := by
  obtain ⟨m', hm, hj, hle, hns, ht⟩ := wf_stars.1 h
  obtain rfl : m = m' := by omega
  by_cases h1 : j = 1
  · subst h1; simpa [mkStars] using ht
  · rw [mkStars_of_not_isStars hns (by omega)]
    obtain ⟨m'', rfl⟩ : ∃ m'', m = m'' + 1 := ⟨m - 1, by omega⟩
    exact wf_stars.2 ⟨m'', rfl, by omega, by omega, hns, by rwa [show m'' + 1 - (j - 1) = m'' + 1 + 1 - j by omega]⟩

theorem Trie.wf_mkStars_one (h : (t : Trie α).WF m) : (mkStars 1 t).WF (m + 1) := by
  unfold mkStars
  simp only [Nat.one_ne_zero, ↓reduceIte]
  split
  · rename_i j t'
    obtain ⟨m', rfl, hj, hle, hns, ht⟩ := wf_stars.1 h
    exact wf_stars.2 ⟨m' + 1, rfl, by omega, by omega, hns, by rwa [show m' + 1 + 1 - (1 + j) = m' + 1 - j by omega]⟩
  · rename_i hne
    exact wf_stars.2 ⟨m, rfl, by omega, by omega, fun hs => by cases t <;> simp_all [isStars], by simpa using h⟩

theorem Trie.WF.insert (ht : t.WF n) (hv : Spec.ValidPath n path) (v : α) : (insert path v t).WF n := by
  fun_induction Trie.insert path v t generalizing n with
  | case1 path vs hb =>
    obtain ⟨rfl, hvs⟩ := wf_leaf.1 ht
    exact wf_leaf.2 ⟨rfl, by simp⟩
  | case2 path cs key hb ih =>
    obtain ⟨m, rfl, hsz, hks, hch⟩ := wf_node.1 ht
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := Spec.validPath_push_iff.1 hv
    cases hm
    obtain ⟨hks', hsz', hmem, -⟩ := hks.binInsertM (y := (key, .empty))
      (merge := fun x => match x with | (_, c) => (key, Trie.insert (ys.push key).pop v c))
      (add := fun _ => (key, singleton (ys.push key).pop v)) (fun x _ _ => rfl) rfl
    have hv'' : Spec.ValidPath (m + key.arity) (ys.push key).pop := by simpa using hv'
    refine wf_node.2 ⟨m, rfl, by omega, hks', fun x hx => ?_⟩
    rcases hmem x hx with hx | rfl | ⟨x', hx', hk, rfl⟩
    · exact hch x hx
    · exact wf_singleton hv'' v
    · have := hch x' hx'
      rw [hk] at this
      exact ih x'.snd this hv''
  | case3 path k c key hb hk ih =>
    obtain ⟨m, rfl, hns, hc⟩ := wf_chain.1 ht
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := Spec.validPath_push_iff.1 hv
    cases hm
    obtain rfl := beq_iff_eq.1 hk
    exact wf_chain.2 ⟨m, rfl, hns, ih hc (by simpa using hv')⟩
  | case4 path k c key hb hk =>
    obtain ⟨m, rfl, hns, hc⟩ := wf_chain.1 ht
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := Spec.validPath_push_iff.1 hv
    cases hm
    have hne : k ≠ key := fun h => hk (by simp [h])
    obtain ⟨hks', -, hmem, hsize⟩ := (show Spec.KeysSorted #[(k, c)] by simp [Spec.KeysSorted]).binInsertM
      (y := (key, singleton (ys.push key).pop v))
      (merge := fun _ => pure (key, singleton (ys.push key).pop v))
      (add := fun _ => pure (key, singleton (ys.push key).pop v)) (fun _ _ _ => rfl) rfl
    simp only [Array.binInsert]
    refine wf_node.2 ⟨m, rfl, by rw [hsize (by simpa using hne)]; simp, hks', fun x hx => ?_⟩
    rcases hmem x hx with hx | rfl | ⟨x', -, -, rfl⟩
    · simp only [Array.mem_singleton] at hx; subst hx; exact hc
    · exact wf_singleton (by simpa using hv') v
    · exact wf_singleton (by simpa using hv') v
  | case5 path j t key hb hk ih =>
    obtain rfl := beq_iff_eq.1 hk
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := Spec.validPath_push_iff.1 hv
    cases hm
    have hx := wf_mkStars_pred ht
    exact wf_mkStars_one (ih hx (by simpa [Key.arity] using hv'))
  | case6 path j t key hb hk =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := Spec.validPath_push_iff.1 hv
    cases hm
    have hne : key ≠ .star := fun h => hk (by simp [h])
    refine wf_node.2 ⟨m', rfl, by simp, by simpa [Spec.KeysSorted] using Key.star_lt hne, fun x hx => ?_⟩
    simp at hx
    rcases hx with rfl | rfl
    · simpa [Key.arity] using wf_mkStars_pred ht
    · exact wf_singleton (by simpa using hv') v
  | case7 path t h1 h2 h3 h4 =>
    exfalso
    cases hb : path.back? with
    | none =>
      obtain rfl := Array.back?_eq_none_iff.1 hb
      obtain rfl := Spec.validPath_empty_iff.1 hv
      cases t with
      | leaf vs => exact h1 vs rfl hb
      | node cs => simpa using wf_node.1 ht
      | chain k c => simpa using wf_chain.1 ht
      | stars j c => simpa using wf_stars.1 ht
    | some key =>
      obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
      obtain ⟨m', rfl, -⟩ := Spec.validPath_push_iff.1 hv
      cases t with
      | leaf vs => simpa using wf_leaf.1 ht
      | node cs => exact h2 cs key rfl hb
      | chain k c => exact h3 k c key rfl hb
      | stars j c => exact h4 j c key rfl hb

section
variable {α : Type}

/-!
## Well-formed tries are built by insertion
-/

/-- One edge labelled {lit}`k` above {lit}`t`, in canonical form. -/
def Spec.wrap (k : Key) (t : Trie α) : Trie α :=
  if k == .star then Trie.mkStars 1 t else .chain k t

theorem Key.popStars_of_back_star {p : Array Key} (h : p.back? = some .star) :
    Key.popStars n p = Key.popStars (n + 1) p.pop := by
  rw [Key.popStars]
  split <;> simp_all

theorem Key.popStars_succ (j : Nat) (p : Array Key) :
    Key.popStars (j + 1) p = ((Key.popStars j p).1 + 1, (Key.popStars j p).2) := by
  fun_induction Key.popStars j p with
  | case1 j p hb ih => rw [popStars_of_back_star hb]; exact ih
  | case2 j p hb => rw [popStars_of_back (fun h => hb h)]

theorem Key.popStars_zero_eq (h : (Key.popStars 0 p).1 = 0) : (Key.popStars 0 p).2 = p := by
  by_cases hb : p.back? = some .star
  · rw [popStars_of_back_star hb, popStars_succ] at h; omega
  · rw [popStars_of_back hb]

theorem Key.back_ne_star_of_popStars_zero (h : (Key.popStars 0 p).1 = 0) : p.back? ≠ some .star := by
  intro hb
  rw [popStars_of_back_star hb, popStars_succ] at h
  omega

theorem Trie.singleton_push (p : Array Key) (k : Key) (v : α) :
    singleton (p.push k) v = Spec.wrap k (singleton p v) := by
  rw [singleton]
  simp only [Array.size_push, Nat.add_one_ne_zero, ↓reduceIte]
  by_cases hk : k = .star
  · subst hk
    rw [Key.popStars_of_back_star (by simp), Array.pop_push, Key.popStars_succ]
    simp only [Nat.zero_lt_succ, ↓reduceDIte, Spec.wrap, BEq.rfl, ↓reduceIte]
    by_cases h0 : p.size = 0
    · obtain rfl := Array.eq_empty_of_size_eq_zero h0
      rw [Key.popStars_of_back (by simp)]
      rw [mkStars_of_not_isStars (singleton_not_isStars (by simp) v) (by omega)]
    · conv => rhs; rw [singleton]
      simp only [h0, ↓reduceIte]
      by_cases hm : (Key.popStars 0 p).1 > 0
      · simp only [hm, ↓reduceDIte, mkStars, Nat.one_ne_zero, ↓reduceIte]
        congr 1
        omega
      · simp only [hm, ↓reduceDIte]
        have hm0 : (Key.popStars 0 p).1 = 0 := by omega
        rw [hm0, Key.popStars_zero_eq hm0]
        have := singleton_not_isStars (Key.back_ne_star_of_popStars_zero hm0) v
        rw [singleton] at this
        simp only [h0, ↓reduceIte, hm, ↓reduceDIte] at this
        rw [Key.popStars_zero_eq hm0] at this
        rw [mkStars_of_not_isStars this (by omega)]
        congr 1
        rw [singleton]
        simp only [h0, ↓reduceIte, hm, ↓reduceDIte]
        rw [Key.popStars_zero_eq hm0]
  · rw [Key.popStars_of_back (by simpa using hk)]
    simp only [Nat.lt_irrefl, ↓reduceDIte, Spec.wrap, beq_iff_eq, hk, ↓reduceIte]
    split <;> simp_all

theorem Trie.insert_leaf (h : path.back? = none) (v : α) : insert path v (.leaf vs) = .leaf (vs.push v) := by
  conv => lhs; unfold Trie.insert
  split <;> simp_all <;> (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; subst_vars; rfl)

theorem Trie.insert_node (h : path.back? = some key) (v : α) (cs : Array (Key × Trie α)) :
    insert path v (.node cs) = .node (Id.run <| cs.binInsertM (·.fst < ·.fst)
      (fun (_, c) => (key, insert path.pop v c)) (fun _ => (key, singleton path.pop v)) (key, .empty)) := by
  conv => lhs; unfold Trie.insert
  split <;> simp_all <;> (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; subst_vars; rfl)

theorem Trie.insert_chain (h : path.back? = some key) (v : α) (k : Key) (c : Trie α) :
    insert path v (.chain k c) = if key == k then .chain k (insert path.pop v c)
      else .node (#[(k, c)].binInsert (·.fst < ·.fst) (key, singleton path.pop v)) := by
  conv => lhs; unfold Trie.insert
  split <;> simp_all <;> (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; subst_vars; rfl)

theorem Trie.insert_stars (h : path.back? = some key) (v : α) (n : Nat) (t : Trie α) :
    insert path v (.stars n t) = if key == .star then mkStars 1 (insert path.pop v (mkStars (n - 1) t))
      else .node #[(.star, mkStars (n - 1) t), (key, singleton path.pop v)] := by
  conv => lhs; unfold Trie.insert
  split <;> simp_all <;> (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; subst_vars; rfl)

theorem Trie.mkStars_one_eq (hc : (c : Trie α).WF m) :
    ∃ j t, mkStars 1 c = .stars j t ∧ j > 0 ∧ mkStars (j - 1) t = c := by
  match c, hc with
  | .stars j c', hc =>
    obtain ⟨m', -, hj, -, hns, -⟩ := wf_stars.1 hc
    refine ⟨1 + j, c', by simp [mkStars], by omega, ?_⟩
    rw [show 1 + j - 1 = j by omega, mkStars_of_not_isStars hns (by omega)]
  | .leaf vs, _ => exact ⟨1, .leaf vs, by simp [mkStars], by omega, by simp [mkStars]⟩
  | .node cs, _ => exact ⟨1, .node cs, by simp [mkStars], by omega, by simp [mkStars]⟩
  | .chain k c, _ => exact ⟨1, .chain k c, by simp [mkStars], by omega, by simp [mkStars]⟩

theorem Trie.insert_wrap (hc : (c : Trie α).WF m) (p : Array Key) (k : Key) (v : α) :
    insert (p.push k) v (Spec.wrap k c) = Spec.wrap k (insert p v c) := by
  by_cases hk : k = .star
  · subst hk
    simp only [Spec.wrap, BEq.rfl, ↓reduceIte]
    obtain ⟨j, t, he, -, hc'⟩ := mkStars_one_eq hc
    rw [he, insert_stars (key := .star) (by simp) v]
    simp [hc']
  · simp only [Spec.wrap, beq_iff_eq, hk, ↓reduceIte]
    rw [insert_chain (key := k) (by simp) v]
    simp

theorem Trie.binInsert_singleton_lt {k k' : Key} (hlt : k < k') (c d : Trie α) :
    #[(k, c)].binInsert (·.fst < ·.fst) (k', d) = #[(k, c), (k', d)] := by
  rcases Array.binInsertM_id_cases (as := #[(k, c)]) (k := (k', d))
      (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst))
      (merge := fun _ => pure (k', d)) (add := fun _ => pure (k', d))
      (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    with ⟨i, hi, hlt', -, -⟩ | ⟨i, hi, hr, -, hnext⟩
  · have : i = 0 := by simpa using hi
    subst this
    simp at hlt'
    exact absurd hlt hlt'
  · simp only [Array.binInsert]
    rw [hr]
    obtain rfl : i = 1 := by
      simp at hi
      rcases Nat.lt_or_ge i 1 with h | h
      · have := hnext (by simp; omega)
        simp [show i = 0 by omega] at this
        exact absurd this (Key.lt_asymm hlt)
      · omega
    exact Array.insertIdx_size_self

theorem Trie.insert_wrap_lt (hc : (c : Trie α).WF m) {k k' : Key} (hlt : k < k') (p : Array Key) (v : α) :
    insert (p.push k') v (Spec.wrap k c) = .node #[(k, c), (k', singleton p v)] := by
  have hne : k' ≠ k := fun h => Key.lt_irrefl _ (h ▸ hlt)
  by_cases hk : k = .star
  · subst hk
    simp only [Spec.wrap, BEq.rfl, ↓reduceIte]
    obtain ⟨j, t, he, -, hc'⟩ := mkStars_one_eq hc
    rw [he, insert_stars (key := k') (by simp) v]
    simp [hne, hc']
  · simp only [Spec.wrap, beq_iff_eq, hk, ↓reduceIte]
    rw [insert_chain (key := k') (by simp) v]
    simp [hne, binInsert_singleton_lt hlt]

theorem Trie.insert_node_push_new {k : Key} {cs : Array (Key × Trie α)} (hlt : ∀ q ∈ cs, q.fst < k)
    (p : Array Key) (v : α) : insert (p.push k) v (.node cs) = .node (cs.push (k, singleton p v)) := by
  rw [insert_node (key := k) (by simp) v]
  rcases Array.binInsertM_id_cases (as := cs) (k := (k, Trie.empty))
      (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst))
      (merge := fun x => (k, insert (p.push k).pop v x.snd)) (add := fun _ => (k, singleton (p.push k).pop v))
      (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    with ⟨i, hi, hlt', hgt, -⟩ | ⟨i, hi, hr, -, hnext⟩
  · have := Key.eq_of_not_lt (by simpa [Key.lt_iff] using hlt') (by simpa [Key.lt_iff] using hgt)
    exact absurd (this ▸ hlt _ (Array.getElem_mem hi)) (Key.lt_irrefl _)
  · simp only [Id.run] at hr ⊢
    rw [hr]
    obtain rfl : i = cs.size := by
      refine Nat.le_antisymm hi (Nat.not_lt.1 fun h => ?_)
      exact Key.lt_asymm (by simpa using hnext h) (hlt _ (Array.getElem_mem h))
    simp [Array.insertIdx_size_self]

theorem Trie.insert_node_push_last {k : Key} {cs : Array (Key × Trie α)} (hlt : ∀ q ∈ cs, q.fst < k)
    (p : Array Key) (v : α) (c : Trie α) :
    insert (p.push k) v (.node (cs.push (k, c))) = .node (cs.push (k, insert p v c)) := by
  rw [insert_node (key := k) (by simp) v]
  rcases Array.binInsertM_id_cases (as := cs.push (k, c)) (k := (k, Trie.empty))
      (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst))
      (merge := fun x => (k, insert (p.push k).pop v x.snd)) (add := fun _ => (k, singleton (p.push k).pop v))
      (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    with ⟨i, hi, hlt', hgt, hr⟩ | ⟨i, hi, hr, hprev, hnext⟩
  · simp only [Id.run] at hr ⊢
    rw [hr]
    obtain rfl : i = cs.size := by
      simp only [Array.size_push] at hi
      refine Nat.le_antisymm (by omega) (Nat.not_lt.1 fun h => ?_)
      have := hlt _ (Array.getElem_mem h)
      have hk' := Key.eq_of_not_lt (by simpa [Key.lt_iff] using hlt') (by simpa [Key.lt_iff] using hgt)
      simp only [Array.getElem_push_lt h] at hk'
      exact Key.lt_irrefl _ (hk' ▸ this)
    simp [Array.set_push]
  · exfalso
    simp only [Array.size_push] at hi
    rcases Nat.lt_or_ge i (cs.push (k, c)).size with h | h
    · rcases Nat.lt_or_ge i cs.size with h' | h'
      · have := hnext h
        simp only [Array.getElem_push_lt h'] at this
        exact Key.lt_asymm (by simpa using this) (hlt _ (Array.getElem_mem h'))
      · have := hnext h
        simp only [show i = cs.size by simp at h; omega, Array.getElem_push_eq] at this
        exact Key.lt_irrefl _ (by simpa using this)
    · have := hprev (by simp at h; omega)
      simp only [show i - 1 = cs.size by simp at h; omega, Array.getElem_push_eq] at this
      exact Key.lt_irrefl _ (by simpa using this)

/-! ### Building tries from lists of paths -/

/-- The trie obtained by inserting {lit}`L` after starting from {lit}`singleton p v`. -/
def Spec.build (p : Array Key) (v : α) (L : List (Array Key × α)) : Trie α :=
  L.foldl (fun t q => t.insert q.1 q.2) (Trie.singleton p v)

/-- Every path is valid at level {lit}`n`. -/
def Spec.AllValid {α : Type} (n : Nat) (p : Array Key) (L : List (Array Key × α)) : Prop :=
  ValidPath n p ∧ ∀ q ∈ L, ValidPath n q.1

theorem Spec.wf_foldl_insert {L : List (Array Key × α)} (hL : ∀ q ∈ L, ValidPath n q.1)
    (ht : (t : Trie α).WF n) : (L.foldl (fun t q => t.insert q.1 q.2) t).WF n := by
  induction L generalizing t with
  | nil => exact ht
  | cons q L ih => exact ih (fun q hq => hL q (by simp [hq])) (ht.insert (hL q (by simp)) q.2)

theorem Spec.wf_build (h : AllValid n p L) (v : α) : (build p v L).WF n :=
  wf_foldl_insert h.2 (Trie.wf_singleton h.1 v)

/-- Wrapping a built trie in one edge is a built trie, with every path extended by the edge. -/
theorem Spec.wrap_build (h : AllValid m p L) (k : Key) (v : α) :
    wrap k (build p v L) = build (p.push k) v (L.map fun q => (q.1.push k, q.2)) := by
  unfold build
  rw [Trie.singleton_push]
  have hs := Trie.wf_singleton h.1 v
  generalize Trie.singleton p v = s at hs
  induction L generalizing s with
  | nil => rfl
  | cons q L ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [Trie.insert_wrap hs]
    exact ih ⟨h.1, fun q hq => h.2 q (by simp [hq])⟩ _ (hs.insert (h.2 q (by simp)) q.2)

theorem Trie.mkStars_succ {c : Trie α} (hc : ¬ isStars c) (j : Nat) :
    mkStars (j + 1) c = mkStars 1 (mkStars j c) := by
  by_cases hj : j = 0
  · subst hj; simp [mkStars]
  · rw [mkStars_of_not_isStars hc hj, mkStars_of_not_isStars hc (by omega)]
    simp [mkStars, Nat.add_comm]

/-- Prefixing a built trie with a run of stars is a built trie. -/
theorem Spec.mkStars_build (h : AllValid m p L) (hc : ¬ isStars (build p v L)) (j : Nat) :
    ∃ p' L', AllValid (m + j) p' L' ∧ Trie.mkStars j (build p v L) = build p' v L' := by
  induction j with
  | zero => exact ⟨p, L, h, by simp [Trie.mkStars]⟩
  | succ j ih =>
    obtain ⟨p', L', h', he⟩ := ih
    refine ⟨p'.push .star, L'.map fun q => (q.1.push .star, q.2), ⟨.push (by simpa [Key.arity] using h'.1),
      fun q hq => ?_⟩, ?_⟩
    · simp only [List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      exact .push (by simpa [Key.arity] using h'.2 q' hq')
    · rw [Trie.mkStars_succ hc, he, ← wrap_build h']
      simp [wrap]

/-- A node built so far: a single child is stored as a wrapped edge, several as a {name}`Trie.node`. -/
def Spec.mkNode (cs : Array (Key × Trie α)) : Trie α :=
  if h : cs.size = 1 then wrap cs[0].1 cs[0].2 else .node cs

/-- Adding the stacks of a child whose key is larger than every existing child's appends that child. -/
theorem Spec.foldl_insert_child {pre : Array (Key × Trie α)} (hpre : 0 < pre.size)
    (hlt : ∀ q ∈ pre, q.fst < k) (hwf : ∀ q ∈ pre, ∃ m, q.snd.WF m) (p : Array Key) (v : α)
    (L : List (Array Key × α)) :
    ((p.push k, v) :: L.map fun q => (q.1.push k, q.2)).foldl (fun t q => t.insert q.1 q.2) (mkNode pre) =
      mkNode (pre.push (k, build p v L)) := by
  have hfirst : (mkNode pre).insert (p.push k) v = .node (pre.push (k, Trie.singleton p v)) := by
    by_cases h1 : pre.size = 1
    · rcases pre with ⟨_ | ⟨x, _ | _⟩⟩ <;> simp at h1
      obtain ⟨m, hm⟩ := hwf x (by simp)
      simp only [mkNode, List.size_toArray, List.length_singleton, ↓reduceDIte]
      change Trie.insert (p.push k) v (wrap x.fst x.snd) = _
      rw [Trie.insert_wrap_lt hm (hlt x (by simp))]
      rfl
    · simp only [mkNode, h1, ↓reduceDIte]
      exact Trie.insert_node_push_new hlt p v
  simp only [List.foldl_cons, hfirst]
  unfold build
  generalize Trie.singleton p v = s
  have hnode : ∀ c, mkNode (pre.push (k, c)) = .node (pre.push (k, c)) := fun c => by
    unfold mkNode
    split
    · rename_i h; rw [Array.size_push] at h; omega
    · rfl
  induction L generalizing s with
  | nil => simp [hnode]
  | cons q L ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [Trie.insert_node_push_last hlt]
    exact ih _

theorem Spec.exists_build_children {n : Nat} :
    ∀ (l : List (Key × Trie α)) (pre : Array (Key × Trie α)) (p : Array Key) (v : α) (L : List (Array Key × α)),
      0 < pre.size → (pre.toList ++ l).Pairwise (·.fst < ·.fst) → (∀ q ∈ pre, ∃ m, q.snd.WF m) →
      (∀ q ∈ l, q.snd.WF (n + q.fst.arity) ∧ ∃ p' v' L', AllValid (n + q.fst.arity) p' L' ∧ q.snd = build p' v' L') →
      AllValid (n + 1) p L → build p v L = mkNode pre →
      ∃ L', AllValid (n + 1) p L' ∧ build p v L' = mkNode (pre ++ l.toArray)
  | [], pre, p, v, L, _, _, _, _, hv, he => ⟨L, hv, by simpa using he⟩
  | q :: l, pre, p, v, L, hpos, hs, hwf, hch, hv, he => by
    obtain ⟨hq, p', v', L', hv', hq'⟩ := hch q (by simp)
    have hlt : ∀ x ∈ pre, x.fst < q.fst := fun x hx =>
      (List.pairwise_append.1 hs).2.2 x (by simpa using hx) q (by simp)
    let L₁ := L ++ ((p'.push q.fst, v') :: L'.map fun r => (r.1.push q.fst, r.2))
    have hv₁ : AllValid (n + 1) p L₁ := by
      refine ⟨hv.1, fun r hr => ?_⟩
      simp only [L₁, List.mem_append, List.mem_cons, List.mem_map] at hr
      rcases hr with hr | rfl | ⟨r', hr', rfl⟩
      · exact hv.2 r hr
      · exact .push hv'.1
      · exact .push (hv'.2 r' hr')
    have he₁ : build p v L₁ = mkNode (pre.push q) := by
      simp only [build, L₁, List.foldl_append] at he ⊢
      rw [he, foldl_insert_child hpos hlt hwf p' v' L', ← hq']
    obtain ⟨L₂, hv₂, he₂⟩ := exists_build_children l (pre.push q) p v L₁ (by simp)
      (by simpa using hs) (fun x hx => by
        rcases Array.mem_push.1 hx with hx | rfl
        · exact hwf x hx
        · exact ⟨_, hq⟩)
      (fun x hx => hch x (by simp [hx])) hv₁ he₁
    exact ⟨L₂, hv₂, by simpa using he₂⟩

/-- Every well-formed trie is built by inserting a nonempty list of valid paths. -/
theorem Trie.WF.exists_build : ∀ (n : Nat) (t : Trie α), t.WF n →
    ∃ p v L, Spec.AllValid n p L ∧ t = Spec.build p v L
  | 0, .leaf vs, h => by
    obtain ⟨-, hvs⟩ := wf_leaf.1 h
    obtain ⟨l⟩ := vs
    obtain ⟨v, l, rfl⟩ := List.exists_cons_of_ne_nil (l := l) (by rintro rfl; simp at hvs)
    refine ⟨#[], v, l.map ((#[], ·)), ⟨.nil, by simp [Spec.ValidPath.nil]⟩, ?_⟩
    clear h hvs
    unfold Spec.build
    rw [singleton]
    simp only [List.size_toArray, List.length_nil, ↓reduceIte]
    suffices ∀ (us : Array α), (l.map ((#[], ·))).foldl (fun t q => t.insert q.1 q.2) (Trie.leaf us) =
        .leaf (us ++ l.toArray) by
      rw [this]; simp
    intro us
    induction l generalizing us with
    | nil => simp
    | cons w l ih => simp only [List.map_cons, List.foldl_cons]; rw [insert_leaf (by simp), ih]; simp
  | 0, .node _, h | 0, .chain _ _, h | 0, .stars _ _, h => by
    first | simpa using wf_node.1 h | simpa using wf_chain.1 h | simpa using wf_stars.1 h
  | n+1, .leaf _, h => by simpa using wf_leaf.1 h
  | n+1, .node cs, h => by
    obtain ⟨m, hm, hsz, hks, hch⟩ := wf_node.1 h
    cases hm
    have hl : cs.toList ≠ [] := by simpa [← Array.toList_eq_nil_iff] using Array.ne_empty_of_size_pos (by omega)
    obtain ⟨q, l, hql⟩ := List.exists_cons_of_ne_nil hl
    have hmem : ∀ x ∈ cs.toList, x.snd.WF (n + x.fst.arity) := fun x hx => hch x (Array.mem_toList_iff.1 hx)
    have hq := hmem q (by simp [hql])
    obtain ⟨p, v, L, hv, hq'⟩ := WF.exists_build _ q.snd hq
    have hs : (cs.toList).Pairwise (·.fst < ·.fst) := by simpa [Spec.KeysSorted, List.pairwise_map] using hks
    rw [hql] at hs
    obtain ⟨L', hv', he⟩ := Spec.exists_build_children (n := n) l #[q] (p.push q.fst) v
      (L.map fun r => (r.1.push q.fst, r.2)) (by simp) (by simpa using hs) (fun x hx => by
        simp only [Array.mem_singleton] at hx; subst hx; exact ⟨_, hq⟩)
      (fun x hx => ⟨hmem x (by simp [hql, hx]), WF.exists_build _ x.snd (hmem x (by simp [hql, hx]))⟩)
      ⟨.push hv.1, fun r hr => by
        simp only [List.mem_map] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        exact .push (hv.2 r' hr')⟩
      (by rw [← Spec.wrap_build hv, ← hq']; simp [Spec.mkNode])
    refine ⟨p.push q.fst, v, L', hv', ?_⟩
    rw [he]
    have : (#[q] ++ l.toArray) = cs := by
      apply Array.toList_inj.1
      simp [hql]
    rw [this]
    simp only [Spec.mkNode, show cs.size ≠ 1 by omega, ↓reduceDIte]
  | n+1, .chain k c, h => by
    obtain ⟨m, hm, hns, hc⟩ := wf_chain.1 h
    cases hm
    obtain ⟨p, v, L, hv, rfl⟩ := WF.exists_build _ c hc
    refine ⟨p.push k, v, L.map fun r => (r.1.push k, r.2), ⟨.push hv.1, fun r hr => ?_⟩, ?_⟩
    · simp only [List.mem_map] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      exact .push (hv.2 r' hr')
    · rw [← Spec.wrap_build hv]
      simp [Spec.wrap, hns]
  | n+1, .stars j c, h => by
    obtain ⟨m, hm, hj, hle, hns, hc⟩ := wf_stars.1 h
    cases hm
    obtain ⟨p, v, L, hv, rfl⟩ := WF.exists_build _ c hc
    obtain ⟨p', L', hv', he⟩ := Spec.mkStars_build hv hns j
    refine ⟨p', v, L', by rwa [show n + 1 - j + j = n + 1 by omega] at hv', ?_⟩
    rw [← he, mkStars_of_not_isStars hns (by omega)]
termination_by _ t => sizeOf t
decreasing_by
  · exact Trie.sizeOf_lt_of_mem (Array.mem_toList_iff.1 (by rw [hql]; simp))
  · exact Trie.sizeOf_lt_of_mem (Array.mem_toList_iff.1 (by rw [hql]; simp [hx]))
  · simp; omega
  · simp; omega

/-! ### Paths come from shapes -/

/-- The shape whose key is {lit}`k` and whose arguments are {lit}`args`. -/
def Spec.toShape : Key → Array ExprShape → ExprShape
  | .lit l, _ => .lit l
  | .const c _, args => .const c args
  | .fvar x _, args => .fvar x args
  | .arrow, args => .arrow (args[0]?.getD .star)
  | .star, _ => .star
  | .other, _ => .other

theorem Spec.getKeyPath_toShape {k : Key} {args : Array ExprShape} (h : args.size = k.arity) :
    (toShape k args).getKeyPath = args.flatMap ExprShape.getKeyPath ++ #[k] := by
  cases k <;> simp only [Key.arity] at h
  case const c n => subst h; simp [toShape, ExprShape.getKeyPath]
  case fvar x n => subst h; simp [toShape, ExprShape.getKeyPath]
  case arrow =>
    rcases args with ⟨_ | ⟨e, _ | _⟩⟩ <;> simp at h
    simp [toShape, ExprShape.getKeyPath]
  all_goals
    obtain rfl := Array.eq_empty_of_size_eq_zero h
    simp [toShape, ExprShape.getKeyPath]

theorem Array.extract_zero_append_extract {es : Array α} (h : n ≤ es.size) :
    es.extract 0 n ++ es.extract n es.size = es := by
  rw [Array.extract_append_extract, Nat.zero_min, Nat.max_eq_right h, Array.extract_size]

theorem Spec.ValidPath.exists_shapes (h : ValidPath n p) :
    ∃ es : Array ExprShape, es.size = n ∧ es.flatMap ExprShape.getKeyPath = p := by
  induction h with
  | nil => exact ⟨#[], rfl, rfl⟩
  | @push n p k _ ih =>
    obtain ⟨es, hsz, rfl⟩ := ih
    refine ⟨(es.extract 0 n).push (toShape k (es.extract n es.size)), by simp; omega, ?_⟩
    rw [Array.flatMap_push, getKeyPath_toShape (by simp; omega), ← Array.append_assoc, ← Array.flatMap_append,
      Array.extract_zero_append_extract (by omega)]
    simp

theorem Spec.exists_getKeyPath (h : ValidPath 1 p) : ∃ e : ExprShape, e.getKeyPath = p := by
  obtain ⟨⟨_ | ⟨e, _ | _⟩⟩, hsz, rfl⟩ := h.exists_shapes <;> simp at hsz
  exact ⟨e, by simp⟩

end

/-!
## Unification of stacks
-/

/-- Pointwise {name}`ExprShape.Unify` of a stack of keys with a stack of queries. -/
def Spec.UnifyMany (es qs : Array ExprShape) : Prop :=
  ∃ _ : es.size = qs.size, ∀ i, ∀ hi : i < es.size, ExprShape.Unify es[i] qs[i]

theorem Spec.unifyMany_empty : UnifyMany #[] #[] := ⟨rfl, fun _ h => by simp at h⟩

theorem Spec.UnifyMany.size_eq (h : UnifyMany es qs) : es.size = qs.size := h.1

theorem Spec.unifyMany_push :
    UnifyMany (es.push e) (qs.push q) ↔ UnifyMany es qs ∧ ExprShape.Unify e q := by
  constructor
  · rintro ⟨h_len, h⟩
    simp only [Array.size_push, Nat.add_right_cancel_iff] at h_len
    refine ⟨⟨h_len, fun i hi => ?_⟩, ?_⟩
    · have := h i (by simp; omega)
      simpa [Array.getElem_push, hi, h_len ▸ hi] using this
    · have := h es.size (by simp)
      simpa [Array.getElem_push, h_len] using this
  · rintro ⟨⟨h_len, h⟩, hq⟩
    refine ⟨by simp [h_len], fun i hi => ?_⟩
    simp only [Array.size_push] at hi
    rw [Array.getElem_push, Array.getElem_push]
    split
    · grind
    · grind

theorem Spec.unifyMany_append (hs : es.size = qs.size) :
    UnifyMany (es ++ es') (qs ++ qs') ↔ UnifyMany es qs ∧ UnifyMany es' qs' := by
  constructor
  · rintro ⟨h_len, h⟩
    simp only [Array.size_append] at h_len
    refine ⟨⟨hs, fun i hi => ?_⟩, ⟨by omega, fun i hi => ?_⟩⟩
    · have := h i (by simp; omega)
      simpa [Array.getElem_append_left hi, Array.getElem_append_left (hs ▸ hi)] using this
    · have := h (es.size + i) (by simp; omega)
      simpa [Array.getElem_append_right, hs] using this
  · rintro ⟨⟨_, h⟩, ⟨h_len', h'⟩⟩
    refine ⟨by simp [hs, h_len'], fun i hi => ?_⟩
    simp only [Array.size_append] at hi
    by_cases hlt : i < es.size
    · rw [Array.getElem_append_left hlt, Array.getElem_append_left (hs ▸ hlt)]
      exact h i hlt
    · rw [Array.getElem_append_right (by omega), Array.getElem_append_right (by omega)]
      have := h' (i - es.size) (by omega)
      simpa [hs] using this

theorem ExprShape.getKeyArgs_inj {e e' : ExprShape} (h : e.getKeyArgs = e'.getKeyArgs) : e = e' := by
  cases e <;> cases e' <;> simp_all [getKeyArgs]

theorem ExprShape.size_getKeyArgs_snd {e : ExprShape} : e.getKeyArgs.snd.size = e.getKeyArgs.fst.arity := by
  cases e <;> simp [getKeyArgs, Key.arity]

theorem ExprShape.getKeyArgs_fst_eq_star {e : ExprShape} : e.getKeyArgs.fst = .star ↔ e = .star := by
  cases e <;> simp [getKeyArgs]

/-- Unification works key by key: the key is a wildcard, or the keys agree and the arguments unify. -/
theorem Spec.unify_iff_of_ne_star {e q : ExprShape} (hq : q ≠ .star) :
    ExprShape.Unify e q ↔ e = .star ∨
      (e.getKeyArgs.fst = q.getKeyArgs.fst ∧ UnifyMany e.getKeyArgs.snd q.getKeyArgs.snd) := by
  constructor
  · intro h
    cases h with
    | star_left => exact .inl rfl
    | star_right => exact absurd rfl hq
    | lit => exact .inr ⟨rfl, unifyMany_empty⟩
    | const h_len h => exact .inr ⟨by simp [ExprShape.getKeyArgs, h_len], h_len, h⟩
    | fvar h_len h => exact .inr ⟨by simp [ExprShape.getKeyArgs, h_len], h_len, h⟩
    | arrow h =>
      refine .inr ⟨rfl, ?_⟩
      simp only [ExprShape.getKeyArgs]
      exact (unifyMany_push (es := #[]) (qs := #[])).2 ⟨unifyMany_empty, h⟩
    | other => exact .inr ⟨rfl, unifyMany_empty⟩
  · rintro (rfl | ⟨hk, hargs⟩)
    · exact .star_left
    · cases e <;> cases q <;> simp only [ExprShape.getKeyArgs, Key.const.injEq, Key.fvar.injEq,
        Key.lit.injEq, reduceCtorEq] at hk
      case lit.lit => exact hk ▸ .lit
      case const.const => obtain ⟨rfl, -⟩ := hk; exact .const hargs.1 hargs.2
      case fvar.fvar => obtain ⟨rfl, -⟩ := hk; exact .fvar hargs.1 hargs.2
      case arrow.arrow =>
        simp only [ExprShape.getKeyArgs] at hargs
        exact .arrow ((unifyMany_push (es := #[]) (qs := #[])).1 hargs).2
      case other.other => exact .other
      case star.star => exact .star_left

/-! ## Key paths of shapes -/

theorem ExprShape.getKeyPath_eq (e : ExprShape) :
    e.getKeyPath = e.getKeyArgs.snd.flatMap getKeyPath ++ #[e.getKeyArgs.fst] := by
  cases e <;> simp [getKeyPath, getKeyArgs]

theorem Spec.getKeyArgs_toShape {k : Key} {args : Array ExprShape} (h : args.size = k.arity) :
    (toShape k args).getKeyArgs = (k, args) := by
  cases k <;> simp only [Key.arity] at h
  case const c n => subst h; simp [toShape, ExprShape.getKeyArgs]
  case fvar x n => subst h; simp [toShape, ExprShape.getKeyArgs]
  case arrow =>
    rcases args with ⟨_ | ⟨e, _ | _⟩⟩ <;> simp at h
    simp [toShape, ExprShape.getKeyArgs]
  all_goals
    obtain rfl := Array.eq_empty_of_size_eq_zero h
    simp [toShape, ExprShape.getKeyArgs]

/-- Skipping one term whose key is {lit}`k` uses up that key and leaves its arguments to skip. -/
theorem Spec.exists_push_iff {X Z : Array Key} {k : Key} {s : Nat} :
    (∃ ds : Array ExprShape, ds.size = s + 1 ∧ X ++ ds.flatMap ExprShape.getKeyPath = Z.push k) ↔
      ∃ ds : Array ExprShape, ds.size = s + k.arity ∧ X ++ ds.flatMap ExprShape.getKeyPath = Z := by
  constructor
  · rintro ⟨ds, hsz, he⟩
    obtain ⟨ds0, d, rfl⟩ := Array.exists_push_of_size_pos (by omega : 0 < ds.size)
    rw [Array.flatMap_push, ExprShape.getKeyPath_eq d, ← Array.append_assoc, ← Array.append_assoc,
      Array.append_singleton, Array.push_eq_push] at he
    obtain ⟨hk, he⟩ := he
    refine ⟨ds0 ++ d.getKeyArgs.snd, ?_, by rw [Array.flatMap_append, ← Array.append_assoc]; exact he⟩
    simp only [Array.size_push, Nat.add_right_cancel_iff] at hsz
    simp [ExprShape.size_getKeyArgs_snd, hsz, hk]
  · rintro ⟨ds, hsz, rfl⟩
    refine ⟨(ds.extract 0 s).push (toShape k (ds.extract s ds.size)), by simp; omega, ?_⟩
    rw [Array.flatMap_push, getKeyPath_toShape (by simp; omega)]
    conv => rhs; rw [← Array.extract_zero_append_extract (es := ds) (n := s) (by omega), Array.flatMap_append]
    simp

/-- Skipping a run of stars uses up one term per star. -/
theorem Spec.exists_replicate_iff {X q : Array Key} : ∀ (j s : Nat),
    (∃ ds : Array ExprShape, ds.size = s + j ∧
        X ++ ds.flatMap ExprShape.getKeyPath = q ++ Array.replicate j .star) ↔
      ∃ ds : Array ExprShape, ds.size = s ∧ X ++ ds.flatMap ExprShape.getKeyPath = q
  | 0, s => by simp
  | j + 1, s => by
    rw [Array.replicate_succ, ← Array.push_append, show s + (j + 1) = (s + j) + 1 by omega, exists_push_iff]
    simpa [Key.arity] using exists_replicate_iff j s

/-- Key paths determine the stack of shapes they came from. -/
theorem Spec.flatMap_getKeyPath_inj {xs ys : Array ExprShape}
    (h : xs.flatMap ExprShape.getKeyPath = ys.flatMap ExprShape.getKeyPath) (hs : xs.size = ys.size) : xs = ys := by
  rcases Array.eq_empty_or_eq_push xs with rfl | ⟨xs', x, rfl⟩
  · exact (Array.eq_empty_of_size_eq_zero (by simpa using hs.symm)).symm
  · obtain ⟨ys', y, rfl⟩ := Array.exists_push_of_size_pos (by simp at hs; omega : 0 < ys.size)
    rw [Array.flatMap_push, Array.flatMap_push, ExprShape.getKeyPath_eq x, ExprShape.getKeyPath_eq y,
      ← Array.append_assoc, ← Array.append_assoc, Array.append_singleton, Array.append_singleton,
      Array.push_eq_push, ← Array.flatMap_append, ← Array.flatMap_append] at h
    obtain ⟨hk, h⟩ := h
    have hsz : (xs' ++ x.getKeyArgs.snd).size = (ys' ++ y.getKeyArgs.snd).size := by
      simp only [Array.size_append, ExprShape.size_getKeyArgs_snd, hk]
      simp at hs; omega
    have := flatMap_getKeyPath_inj h hsz
    obtain ⟨rfl, ha⟩ := Array.append_inj this (by simp at hs; omega)
    rw [ExprShape.getKeyArgs_inj (Prod.ext hk ha)]
termination_by (xs.flatMap ExprShape.getKeyPath).size
decreasing_by
  subst_vars
  rw [Array.flatMap_push, Array.flatMap_append, ExprShape.getKeyPath_eq x]
  simp

section
variable {α : Type}

/-!
## What a trie stores
-/

/-- {lit}`Spec.Mem t p w`: the trie {lit}`t` stores the value {lit}`w` under the stack-ordered key path {lit}`p`. -/
inductive Spec.Mem : Trie α → Array Key → α → Prop where
  | leaf : w ∈ vs → Mem (.leaf vs) #[] w
  | node : (k, c) ∈ cs → Mem c p w → Mem (.node cs) (p.push k) w
  | chain : Mem c p w → Mem (.chain k c) (p.push k) w
  | stars : Mem c p w → Mem (.stars n c) (p ++ Array.replicate n .star) w

theorem Spec.mem_leaf_iff : Mem (.leaf vs) p w ↔ p = #[] ∧ w ∈ vs := by
  constructor
  · intro h; cases h; exact ⟨rfl, by assumption⟩
  · rintro ⟨rfl, h⟩; exact .leaf h

theorem Spec.mem_node_iff {cs : Array (Key × Trie α)} :
    Mem (.node cs) p w ↔ ∃ q k c, p = q.push k ∧ (k, c) ∈ cs ∧ Mem c q w := by
  constructor
  · intro h; cases h; exact ⟨_, _, _, rfl, by assumption, by assumption⟩
  · rintro ⟨q, k, c, rfl, hc, h⟩; exact .node hc h

theorem Spec.mem_chain_iff : Mem (.chain k c) p w ↔ ∃ q, p = q.push k ∧ Mem c q w := by
  constructor
  · intro h; cases h; exact ⟨_, rfl, by assumption⟩
  · rintro ⟨q, rfl, h⟩; exact .chain h

theorem Spec.mem_stars_iff : Mem (.stars n c) p w ↔ ∃ q, p = q ++ Array.replicate n .star ∧ Mem c q w := by
  constructor
  · intro h; cases h; exact ⟨_, rfl, by assumption⟩
  · rintro ⟨q, rfl, h⟩; exact .stars h

theorem Spec.mem_mkStars_iff : Mem (Trie.mkStars n c) p w ↔ ∃ q, p = q ++ Array.replicate n .star ∧ Mem c q w := by
  unfold Trie.mkStars
  split
  · subst_vars; simp
  · split
    · rename_i m t
      simp only [mem_stars_iff]
      constructor
      · rintro ⟨q, rfl, h⟩
        exact ⟨q ++ Array.replicate m .star, by
          rw [Array.append_assoc, Array.replicate_append_replicate, Nat.add_comm], q, rfl, h⟩
      · rintro ⟨_, rfl, q, rfl, h⟩
        exact ⟨q, by rw [Array.append_assoc, Array.replicate_append_replicate, Nat.add_comm], h⟩
    · exact mem_stars_iff

theorem Spec.mem_wrap_iff : Mem (wrap k t) p w ↔ ∃ q, p = q.push k ∧ Mem t q w := by
  unfold wrap
  split
  · rename_i hk
    obtain rfl := beq_iff_eq.1 hk
    rw [mem_mkStars_iff]
    simp only [Array.replicate_one, Array.append_singleton]
  · exact mem_chain_iff

theorem Trie.singleton_empty (v : α) : singleton #[] v = .leaf #[v] := by
  rw [singleton]; simp

theorem Spec.mem_singleton_iff (path : Array Key) (v : α) :
    Mem (Trie.singleton path v) p w ↔ p = path ∧ w = v := by
  rcases Array.eq_empty_or_eq_push path with rfl | ⟨ys, k, rfl⟩
  · simp [Trie.singleton_empty, mem_leaf_iff]
  · rw [Trie.singleton_push, mem_wrap_iff]
    constructor
    · rintro ⟨q, rfl, h⟩
      obtain ⟨rfl, rfl⟩ := (mem_singleton_iff ys v).1 h
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨ys, rfl, (mem_singleton_iff ys _).2 ⟨rfl, rfl⟩⟩
termination_by path.size
decreasing_by all_goals (subst_vars; simp)

theorem Spec.mem_stars_iff_pred (hj : 0 < j) :
    Mem (.stars j t) p w ↔ ∃ q, p = q.push .star ∧ Mem (Trie.mkStars (j - 1) t) q w := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [mem_stars_iff]
  simp only [mem_mkStars_iff, Nat.add_sub_cancel, Array.replicate_succ]
  constructor
  · rintro ⟨q, rfl, h⟩
    exact ⟨q ++ Array.replicate j .star, by simp, q, rfl, h⟩
  · rintro ⟨_, rfl, q, rfl, h⟩
    exact ⟨q, by simp, h⟩

/-- In sorted children, replacing the child with a given key replaces exactly that child. -/
theorem Spec.KeysSorted.mem_set_iff {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat} (hi : i < cs.size)
    (hk : cs[i].fst = key) : (k, c) ∈ cs.set i (key, x) ↔ (k = key ∧ c = x) ∨ ((k, c) ∈ cs ∧ k ≠ key) := by
  constructor
  · intro h
    obtain ⟨j, hj, hjeq⟩ := Array.mem_iff_getElem.1 h
    simp only [Array.size_set] at hj
    by_cases hji : j = i
    · subst hji
      simp only [Array.getElem_set_self, Prod.mk.injEq] at hjeq
      exact .inl ⟨hjeq.1.symm, hjeq.2.symm⟩
    · rw [Array.getElem_set_ne hi hj (Ne.symm hji)] at hjeq
      refine .inr ⟨hjeq ▸ Array.getElem_mem hj, fun hkk => ?_⟩
      have h1 : cs[j].fst = cs[i].fst := by rw [hjeq, hk, hkk]
      rcases Nat.lt_or_gt_of_ne hji with h2 | h2
      · exact Key.lt_irrefl _ (h1 ▸ hs.lt hj hi h2)
      · exact Key.lt_irrefl _ (h1 ▸ hs.lt hi hj h2)
  · rintro (⟨rfl, rfl⟩ | ⟨h, hkk⟩)
    · exact Array.mem_iff_getElem.2 ⟨i, by simpa using hi, by simp⟩
    · obtain ⟨j, hj, hjeq⟩ := Array.mem_iff_getElem.1 h
      have hji : i ≠ j := fun hij => hkk (by subst hij; rw [← hk, hjeq])
      exact Array.mem_iff_getElem.2 ⟨j, by simpa using hj, by rw [Array.getElem_set_ne hi hj hji, hjeq]⟩

/-- A key inserted between its neighbours was not already present. -/
theorem Spec.KeysSorted.fst_ne_of_between {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat}
    (hi : i ≤ cs.size) (hprev : ∀ h : 0 < i, cs[i - 1].fst < key) (hnext : ∀ h : i < cs.size, key < cs[i].fst) :
    ∀ x ∈ cs, x.fst ≠ key := by
  intro x hx hxk
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
  rcases Nat.lt_or_ge j i with h | h
  · have hp := hprev (by omega)
    by_cases hje : j = i - 1
    · subst hje; exact Key.lt_irrefl _ (hxk ▸ hp)
    · exact Key.lt_irrefl _ (hxk ▸ Key.lt_trans (hs.lt hj (by omega) (by omega)) hp)
  · have hn := hnext (by omega)
    by_cases hje : j = i
    · subst hje; exact Key.lt_irrefl _ (hxk ▸ hn)
    · exact Key.lt_irrefl _ (hxk ▸ Key.lt_trans hn (hs.lt (by omega) hj (by omega)))

theorem Spec.mem_binInsert_singleton {k key : Key} (hne : k ≠ key) (c s : Trie α) :
    x ∈ #[(k, c)].binInsert (·.fst < ·.fst) (key, s) ↔ x = (k, c) ∨ x = (key, s) := by
  simp only [Array.binInsert]
  rcases Array.binInsertM_id_cases (as := #[(k, c)]) (k := (key, s))
      (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst))
      (merge := fun _ => pure (key, s)) (add := fun _ => pure (key, s))
      (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    with ⟨i, hi, hlt, hgt, -⟩ | ⟨i, hi, hr, -, -⟩
  · have : i = 0 := by simpa using hi
    subst this
    exact absurd (Key.eq_of_not_lt (by simpa [Key.lt_iff] using hlt) (by simpa [Key.lt_iff] using hgt)) hne
  · rw [hr, Array.mem_insertIdx]
    simp [or_comm]

theorem Spec.mem_insert_iff (ht : t.WF n) (hv : ValidPath n path) (v : α) :
    Mem (t.insert path v) p w ↔ Mem t p w ∨ (p = path ∧ w = v) := by
  fun_induction Trie.insert path v t generalizing n p with
  | case1 path vs hb =>
    obtain rfl := Array.back?_eq_none_iff.1 hb
    simp only [mem_leaf_iff, Array.mem_push]
    grind
  | case2 path cs key hb ih =>
    obtain ⟨m, rfl, hsz, hks, hch⟩ := Trie.wf_node.1 ht
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := validPath_push_iff.1 hv
    cases hm
    have hv'' : ValidPath (m + key.arity) (ys.push key).pop := by simpa using hv'
    rcases Array.binInsertM_id_cases (as := cs) (k := (key, Trie.empty))
        (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst))
        (merge := fun x => (key, Trie.insert (ys.push key).pop v x.snd))
        (add := fun _ => (key, Trie.singleton (ys.push key).pop v))
        (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
      with ⟨i, hi, hlt, hgt, hr⟩ | ⟨i, hi, hr, hprev, hnext⟩
    · have hk : cs[i].fst = key :=
        Key.eq_of_not_lt (by simpa [Key.lt_iff] using hlt) (by simpa [Key.lt_iff] using hgt)
      have hci := hch _ (Array.getElem_mem hi)
      rw [hk] at hci
      have hmemi : (key, cs[i].snd) ∈ cs := by rw [← hk]; exact Array.getElem_mem hi
      simp only [Id.run] at hr
      rw [hr, mem_node_iff, mem_node_iff]
      constructor
      · rintro ⟨q, k, c, rfl, hc, h⟩
        rcases (hks.mem_set_iff hi hk).1 hc with ⟨rfl, rfl⟩ | ⟨hc, -⟩
        · rcases (ih cs[i].snd hci hv'').1 h with h | ⟨rfl, rfl⟩
          · exact .inl ⟨q, k, cs[i].snd, rfl, hmemi, h⟩
          · exact .inr ⟨by simp, rfl⟩
        · exact .inl ⟨q, k, c, rfl, hc, h⟩
      · rintro (⟨q, k, c, rfl, hc, h⟩ | ⟨rfl, rfl⟩)
        · by_cases hkk : k = key
          · subst hkk
            have := hks.eq_of_mem hc hmemi rfl
            simp only [Prod.mk.injEq, true_and] at this
            subst this
            exact ⟨q, k, _, rfl, (hks.mem_set_iff hi hk).2 (.inl ⟨rfl, rfl⟩), (ih _ hci hv'').2 (.inl h)⟩
          · exact ⟨q, k, c, rfl, (hks.mem_set_iff hi hk).2 (.inr ⟨hc, hkk⟩), h⟩
        · exact ⟨ys, key, _, rfl, (hks.mem_set_iff hi hk).2 (.inl ⟨rfl, rfl⟩),
            (ih _ hci hv'').2 (.inr ⟨by simp, rfl⟩)⟩
    · have hfresh := hks.fst_ne_of_between hi (fun h => by simpa using hprev h) (fun h => by simpa using hnext h)
      simp only [Id.run] at hr
      rw [hr, mem_node_iff, mem_node_iff]
      constructor
      · rintro ⟨q, k, c, rfl, hc, h⟩
        rcases Array.mem_insertIdx.1 hc with h' | hc
        · simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          obtain ⟨rfl, rfl⟩ := (mem_singleton_iff _ _).1 h
          exact .inr ⟨by simp, rfl⟩
        · exact .inl ⟨q, k, c, rfl, hc, h⟩
      · rintro (⟨q, k, c, rfl, hc, h⟩ | ⟨rfl, rfl⟩)
        · exact ⟨q, k, c, rfl, Array.mem_insertIdx.2 (.inr hc), h⟩
        · exact ⟨ys, key, _, rfl, Array.mem_insertIdx.2 (.inl rfl), (mem_singleton_iff _ _).2 ⟨by simp, rfl⟩⟩
  | case3 path k c key hb hk ih =>
    obtain ⟨m, rfl, hns, hc⟩ := Trie.wf_chain.1 ht
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := validPath_push_iff.1 hv
    cases hm
    obtain rfl := beq_iff_eq.1 hk
    rw [mem_chain_iff, mem_chain_iff]
    constructor
    · rintro ⟨q, rfl, h⟩
      rcases (ih hc (by simpa using hv')).1 h with h | ⟨rfl, rfl⟩
      · exact .inl ⟨q, rfl, h⟩
      · exact .inr ⟨by simp, rfl⟩
    · rintro (⟨q, rfl, h⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, rfl, (ih hc (by simpa using hv')).2 (.inl h)⟩
      · exact ⟨ys, rfl, (ih hc (by simpa using hv')).2 (.inr ⟨by simp, rfl⟩)⟩
  | case4 path k c key hb hk =>
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    have hne : k ≠ key := fun h => hk (by simp [h])
    rw [mem_node_iff, mem_chain_iff]
    constructor
    · rintro ⟨q, k', c', rfl, hc, h⟩
      rcases (mem_binInsert_singleton hne _ _).1 hc with h' | h'
      · simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact .inl ⟨q, rfl, h⟩
      · simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        obtain ⟨rfl, rfl⟩ := (mem_singleton_iff _ _).1 h
        exact .inr ⟨by simp, rfl⟩
    · rintro (⟨q, rfl, h⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, k, c, rfl, (mem_binInsert_singleton hne _ _).2 (.inl rfl), h⟩
      · exact ⟨ys, key, _, rfl, (mem_binInsert_singleton hne _ _).2 (.inr rfl),
          (mem_singleton_iff _ _).2 ⟨by simp, rfl⟩⟩
  | case5 path j t key hb hk ih =>
    obtain rfl := beq_iff_eq.1 hk
    obtain ⟨m, rfl, hj, -, -, -⟩ := Trie.wf_stars.1 ht
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    obtain ⟨m', hm, hv'⟩ := validPath_push_iff.1 hv
    cases hm
    have hx := Trie.wf_mkStars_pred ht
    have ih' := fun {q} => ih hx (p := q) (by simpa [Key.arity] using hv')
    rw [mem_mkStars_iff, mem_stars_iff_pred hj]
    simp only [Array.replicate_one, Array.append_singleton]
    constructor
    · rintro ⟨q, rfl, h⟩
      rcases ih'.1 h with h | ⟨rfl, rfl⟩
      · exact .inl ⟨q, rfl, h⟩
      · exact .inr ⟨by simp, rfl⟩
    · rintro (⟨q, rfl, h⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, rfl, ih'.2 (.inl h)⟩
      · exact ⟨ys, rfl, ih'.2 (.inr ⟨by simp, rfl⟩)⟩
  | case6 path j t key hb hk =>
    obtain ⟨m, rfl, hj, -, -, -⟩ := Trie.wf_stars.1 ht
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
    have hne : key ≠ .star := fun h => hk (by simp [h])
    rw [mem_node_iff, mem_stars_iff_pred hj]
    constructor
    · rintro ⟨q, k, c, rfl, hc, h⟩
      simp only [List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl ⟨q, rfl, h⟩
      · obtain ⟨rfl, rfl⟩ := (mem_singleton_iff _ _).1 h
        exact .inr ⟨by simp, rfl⟩
    · rintro (⟨q, rfl, h⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, .star, _, rfl, by simp, h⟩
      · exact ⟨ys, key, Trie.singleton (ys.push key).pop _, rfl, by simp, (mem_singleton_iff _ _).2 ⟨by simp, rfl⟩⟩
  | case7 path t h1 h2 h3 h4 =>
    exfalso
    cases hb : path.back? with
    | none =>
      obtain rfl := Array.back?_eq_none_iff.1 hb
      obtain rfl := validPath_empty_iff.1 hv
      cases t with
      | leaf vs => exact h1 vs rfl hb
      | node cs => simpa using Trie.wf_node.1 ht
      | chain k c => simpa using Trie.wf_chain.1 ht
      | stars j c => simpa using Trie.wf_stars.1 ht
    | some key =>
      obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hb
      obtain ⟨m', rfl, -⟩ := validPath_push_iff.1 hv
      cases t with
      | leaf vs => simpa using Trie.wf_leaf.1 ht
      | node cs => exact h2 cs key rfl hb
      | chain k c => exact h3 k c key rfl hb
      | stars j c => exact h4 j c key rfl hb

/-!
## Lookup
-/

local notation "P" xs => Array.flatMap ExprShape.getKeyPath xs

theorem Spec.mem_node_push_iff {cs : Array (Key × Trie α)} :
    Mem (.node cs) (Y.push k) w ↔ ∃ c, (k, c) ∈ cs ∧ Mem c Y w := by
  rw [mem_node_iff]
  constructor
  · rintro ⟨q, k', c, he, hc, h⟩
    obtain ⟨rfl, rfl⟩ := Array.push_eq_push.1 he
    exact ⟨c, hc, h⟩
  · rintro ⟨c, hc, h⟩; exact ⟨Y, k, c, rfl, hc, h⟩

theorem Spec.mem_chain_push_iff : Mem (.chain k c) (Y.push k') w ↔ k' = k ∧ Mem c Y w := by
  rw [mem_chain_iff]
  constructor
  · rintro ⟨q, he, h⟩
    obtain ⟨rfl, rfl⟩ := Array.push_eq_push.1 he
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨Y, rfl, h⟩

/-! ### Skipping a term -/

theorem Spec.skip_node_iff {cs : Array (Key × Trie α)} :
    (∃ ds : Array ExprShape, ds.size = s + 1 ∧ Mem (.node cs) (X ++ P ds) w) ↔
      ∃ kc ∈ cs, ∃ ds : Array ExprShape, ds.size = s + kc.fst.arity ∧ Mem kc.snd (X ++ P ds) w := by
  constructor
  · rintro ⟨ds, hsz, h⟩
    obtain ⟨q, k, c, he, hc, h⟩ := mem_node_iff.1 h
    obtain ⟨ds', hsz', rfl⟩ := exists_push_iff.1 ⟨ds, hsz, he⟩
    exact ⟨(k, c), hc, ds', hsz', h⟩
  · rintro ⟨⟨k, c⟩, hc, ds', hsz', h⟩
    obtain ⟨ds, hsz, he⟩ := exists_push_iff.2 ⟨ds', hsz', rfl⟩
    exact ⟨ds, hsz, he ▸ .node hc h⟩

theorem Spec.skip_chain_iff :
    (∃ ds : Array ExprShape, ds.size = s + 1 ∧ Mem (.chain k c) (X ++ P ds) w) ↔
      ∃ ds : Array ExprShape, ds.size = s + k.arity ∧ Mem c (X ++ P ds) w := by
  constructor
  · rintro ⟨ds, hsz, h⟩
    obtain ⟨q, he, h⟩ := mem_chain_iff.1 h
    obtain ⟨ds', hsz', rfl⟩ := exists_push_iff.1 ⟨ds, hsz, he⟩
    exact ⟨ds', hsz', h⟩
  · rintro ⟨ds', hsz', h⟩
    obtain ⟨ds, hsz, he⟩ := exists_push_iff.2 ⟨ds', hsz', rfl⟩
    exact ⟨ds, hsz, he ▸ .chain h⟩

theorem Spec.skip_stars_le_iff (hn : n ≤ s + 1) :
    (∃ ds : Array ExprShape, ds.size = s + 1 ∧ Mem (.stars n c) (X ++ P ds) w) ↔
      ∃ ds : Array ExprShape, ds.size = s + 1 - n ∧ Mem c (X ++ P ds) w := by
  have hr := fun q => exists_replicate_iff (X := X) (q := q) n (s + 1 - n)
  rw [show s + 1 - n + n = s + 1 by omega] at hr
  constructor
  · rintro ⟨ds, hsz, h⟩
    obtain ⟨q, he, h⟩ := mem_stars_iff.1 h
    obtain ⟨ds', hsz', rfl⟩ := (hr q).1 ⟨ds, hsz, he⟩
    exact ⟨ds', hsz', h⟩
  · rintro ⟨ds', hsz', h⟩
    obtain ⟨ds, hsz, he⟩ := (hr _).2 ⟨ds', hsz', rfl⟩
    exact ⟨ds, hsz, he ▸ .stars h⟩

theorem Spec.skip_stars_gt_iff (hn : s + 1 < n) :
    (∃ ds : Array ExprShape, ds.size = s + 1 ∧ Mem (.stars n c) (X ++ P ds) w) ↔
      Mem (.stars (n - s - 1) c) X w := by
  have hsplit : ∀ q : Array Key, q ++ Array.replicate n .star =
      (q ++ Array.replicate (n - s - 1) .star) ++ Array.replicate (s + 1) .star := fun q => by
    rw [Array.append_assoc, Array.replicate_append_replicate, show n - s - 1 + (s + 1) = n by omega]
  have hr := fun q => exists_replicate_iff (X := X) (q := q ++ Array.replicate (n - s - 1) .star) (s + 1) 0
  simp only [Nat.zero_add] at hr
  constructor
  · rintro ⟨ds, hsz, h⟩
    obtain ⟨q, he, h⟩ := mem_stars_iff.1 h
    rw [hsplit] at he
    obtain ⟨ds', hsz', he'⟩ := (hr q).1 ⟨ds, hsz, he⟩
    obtain rfl := Array.eq_empty_of_size_eq_zero hsz'
    simp only [Array.flatMap_empty, Array.append_empty] at he'
    exact he' ▸ .stars h
  · intro h
    obtain ⟨q, rfl, hc⟩ := mem_stars_iff.1 h
    obtain ⟨ds, hsz, he⟩ := (hr q).2 ⟨#[], rfl, by simp⟩
    exact ⟨ds, hsz, by rw [he, ← hsplit]; exact .stars hc⟩

/-! ### Matching a query whose top is not a wildcard -/

theorem Spec.unify_top_iff {qs : Array ExprShape} {t : Trie α} (hq : q ≠ .star) :
    (∃ es : Array ExprShape, UnifyMany es (qs.push q) ∧ Mem t (P es) w) ↔
      (∃ es, UnifyMany es qs ∧ Mem t ((P es).push .star) w) ∨
      (∃ es, UnifyMany es (qs ++ q.getKeyArgs.snd) ∧ Mem t ((P es).push q.getKeyArgs.fst) w) := by
  constructor
  · rintro ⟨es, hu, h⟩
    obtain ⟨es', e, rfl⟩ := Array.exists_push_of_size_pos (by simp [hu.size_eq] : 0 < es.size)
    obtain ⟨hu', he⟩ := unifyMany_push.1 hu
    rw [Array.flatMap_push, ExprShape.getKeyPath_eq e] at h
    rcases (unify_iff_of_ne_star hq).1 he with rfl | ⟨hk, ha⟩
    · exact .inl ⟨es', hu', by simpa [ExprShape.getKeyArgs] using h⟩
    · refine .inr ⟨es' ++ e.getKeyArgs.snd, (unifyMany_append hu'.size_eq).2 ⟨hu', ha⟩, ?_⟩
      rw [← hk, Array.flatMap_append]
      simpa [Array.append_assoc] using h
  · rintro (⟨es, hu, h⟩ | ⟨es, hu, h⟩)
    · exact ⟨es.push .star, unifyMany_push.2 ⟨hu, .star_left⟩, by simpa [ExprShape.getKeyPath] using h⟩
    · have hsz := hu.size_eq
      simp only [Array.size_append] at hsz
      have hsplit := Array.extract_zero_append_extract (es := es) (n := qs.size) (by omega)
      have hargs : (es.extract qs.size es.size).size = q.getKeyArgs.fst.arity := by
        simp [← ExprShape.size_getKeyArgs_snd]; omega
      rw [← hsplit] at hu h
      obtain ⟨hu₁, hu₂⟩ := (unifyMany_append (by simp; omega)).1 hu
      refine ⟨(es.extract 0 qs.size).push (toShape q.getKeyArgs.fst (es.extract qs.size es.size)),
        unifyMany_push.2 ⟨hu₁, (unify_iff_of_ne_star hq).2 (.inr ?_)⟩, ?_⟩
      · rw [getKeyArgs_toShape hargs]; exact ⟨rfl, hu₂⟩
      · rw [Array.flatMap_push, getKeyPath_toShape hargs, ← Array.append_assoc, Array.append_singleton]
        rwa [Array.flatMap_append] at h

theorem Spec.mem_foldl_list_iff {β : Type} {f : Array α → β → Array α} {R : β → Prop} (l : List β)
    (h : ∀ acc x, x ∈ l → (w ∈ f acc x ↔ w ∈ acc ∨ R x)) (acc : Array α) :
    w ∈ l.foldl f acc ↔ w ∈ acc ∨ ∃ x ∈ l, R x := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp]
    rw [ih (fun acc y hy => h acc y (by simp [hy])), h acc x (by simp)]
    grind

theorem Spec.mem_foldl_iff {β : Type} {cs : Array β} {f : Array α → β → Array α} {R : β → Prop}
    (h : ∀ acc x, x ∈ cs → (w ∈ f acc x ↔ w ∈ acc ∨ R x)) (acc : Array α) :
    w ∈ cs.foldl f acc ↔ w ∈ acc ∨ ∃ x ∈ cs, R x := by
  rw [← Array.foldl_toList, mem_foldl_list_iff _ (fun acc x hx => h acc x (Array.mem_toList_iff.1 hx))]
  simp only [Array.mem_toList_iff]

theorem Spec.exists_empty_iff {R : Array ExprShape → Prop} {t : Trie α} :
    (∃ es ds : Array ExprShape, ds.size = 0 ∧ R es ∧ Mem t ((P es) ++ (P ds)) w) ↔ ∃ es, R es ∧ Mem t (P es) w := by
  constructor
  · rintro ⟨es, ds, hds, hr, hm⟩
    obtain rfl := Array.eq_empty_of_size_eq_zero hds
    exact ⟨es, hr, by simpa using hm⟩
  · rintro ⟨es, hr, hm⟩
    exact ⟨es, #[], rfl, hr, by simpa using hm⟩

theorem Spec.mem_getUnify_iff {t : Trie α} (ht : t.WF (skip + qs.size)) :
    w ∈ t.getUnify skip qs accum ↔ w ∈ accum ∨
      ∃ es ds : Array ExprShape, ds.size = skip ∧ UnifyMany es qs ∧ Mem t ((P es) ++ (P ds)) w := by
  fun_induction Trie.getUnify skip qs accum t with
  | case1 qs accum skip vs =>
    simpa using Trie.wf_leaf.1 ht
  | case2 qs accum skip cs ih =>
    obtain ⟨m, hm, -, -, hch⟩ := Trie.wf_node.1 ht
    rw [mem_foldl_iff (R := fun kc => ∃ es ds : Array ExprShape, ds.size = skip + kc.fst.arity ∧
        UnifyMany es qs ∧ Mem kc.snd ((P es) ++ (P ds)) w)
      (fun acc kc hkc => ih acc kc hkc (by have := hch kc hkc; rwa [show m = skip + qs.size by omega,
        Nat.add_right_comm] at this))]
    apply or_congr_right
    constructor
    · rintro ⟨kc, hkc, es, ds, hds, hu, hm⟩
      obtain ⟨ds', hds', hm'⟩ := skip_node_iff.2 ⟨kc, hkc, ds, hds, hm⟩
      exact ⟨es, ds', hds', hu, hm'⟩
    · rintro ⟨es, ds, hds, hu, hm⟩
      obtain ⟨kc, hkc, ds', hds', hm'⟩ := skip_node_iff.1 ⟨ds, hds, hm⟩
      exact ⟨kc, hkc, es, ds', hds', hu, hm'⟩
  | case3 qs accum skip k c ih =>
    obtain ⟨m, hm, -, hc⟩ := Trie.wf_chain.1 ht
    rw [ih (by rwa [show m = skip + qs.size by omega, Nat.add_right_comm] at hc)]
    apply or_congr_right
    constructor
    · rintro ⟨es, ds, hds, hu, hm⟩
      obtain ⟨ds', hds', hm'⟩ := skip_chain_iff.2 ⟨ds, hds, hm⟩
      exact ⟨es, ds', hds', hu, hm'⟩
    · rintro ⟨es, ds, hds, hu, hm⟩
      obtain ⟨ds', hds', hm'⟩ := skip_chain_iff.1 ⟨ds, hds, hm⟩
      exact ⟨es, ds', hds', hu, hm'⟩
  | case4 qs accum skip n c hn ih =>
    obtain ⟨m, hm, -, -, -, hc⟩ := Trie.wf_stars.1 ht
    rw [ih (by rwa [show m + 1 - n = skip + 1 - n + qs.size by omega] at hc)]
    apply or_congr_right
    constructor
    · rintro ⟨es, ds, hds, hu, hm⟩
      obtain ⟨ds', hds', hm'⟩ := (skip_stars_le_iff hn).2 ⟨ds, hds, hm⟩
      exact ⟨es, ds', hds', hu, hm'⟩
    · rintro ⟨es, ds, hds, hu, hm⟩
      obtain ⟨ds', hds', hm'⟩ := (skip_stars_le_iff hn).1 ⟨ds, hds, hm⟩
      exact ⟨es, ds', hds', hu, hm'⟩
  | case5 qs accum skip n c hn ih =>
    obtain ⟨m, hm, hn0, hle, hns, hc⟩ := Trie.wf_stars.1 ht
    have hwf : (Trie.stars (n - skip - 1) c).WF (0 + qs.size) := by
      obtain ⟨q', hq'⟩ : ∃ q', qs.size = q' + 1 := ⟨qs.size - 1, by omega⟩
      rw [Nat.zero_add, hq']
      exact Trie.wf_stars.2 ⟨q', rfl, by omega, by omega, hns, by
        rwa [show q' + 1 - (n - skip - 1) = m + 1 - n by omega]⟩
    rw [ih hwf]
    simp only [exists_empty_iff]
    apply or_congr_right
    constructor
    · rintro ⟨es, hu, hm⟩
      obtain ⟨ds, hds, hm'⟩ := (skip_stars_gt_iff (by omega)).2 hm
      exact ⟨es, ds, hds, hu, hm'⟩
    · rintro ⟨es, ds, hds, hu, hm⟩
      exact ⟨es, hu, (skip_stars_gt_iff (by omega)).1 ⟨ds, hds, hm⟩⟩
  | case6 qs accum t hb =>
    obtain rfl : qs = #[] := by simpa using hb
    obtain ⟨vs, rfl⟩ : ∃ vs, t = .leaf vs := by
      cases t with
      | leaf vs => exact ⟨vs, rfl⟩
      | node _ => simpa using Trie.wf_node.1 ht
      | chain _ _ => simpa using Trie.wf_chain.1 ht
      | stars _ _ => simpa using Trie.wf_stars.1 ht
    simp only [exists_empty_iff, Array.mem_append]
    apply or_congr_right
    constructor
    · intro h; exact ⟨#[], unifyMany_empty, mem_leaf_iff.2 ⟨by simp, h⟩⟩
    · rintro ⟨es, hu, hm⟩
      obtain rfl := Array.eq_empty_of_size_eq_zero hu.size_eq
      exact (mem_leaf_iff.1 hm).2
  | case7 qs accum t keyArgs hb hk ih =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    obtain rfl : q = .star := ExprShape.getKeyArgs_fst_eq_star.1 (beq_iff_eq.1 hk)
    simp only [Array.pop_push] at ih ⊢
    rw [ih (by simpa [Nat.add_comm] using ht)]
    simp only [exists_empty_iff]
    apply or_congr_right
    constructor
    · rintro ⟨es, ds, hds, hu, hm⟩
      obtain ⟨d, rfl⟩ : ∃ d, ds = #[d] := by
        rcases ds with ⟨_ | ⟨d, _ | _⟩⟩ <;> simp at hds
        exact ⟨d, rfl⟩
      exact ⟨es.push d, unifyMany_push.2 ⟨hu, .star_right⟩, by simpa using hm⟩
    · rintro ⟨es, hu, hm⟩
      obtain ⟨es', e, rfl⟩ := Array.exists_push_of_size_pos (by simp [hu.size_eq] : 0 < es.size)
      exact ⟨es', #[e], rfl, (unifyMany_push.1 hu).1, by simpa using hm⟩
  | case8 qs accum keyArgs hb hk vs =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    simpa using Trie.wf_leaf.1 ht
  | case9 qs accum keyArgs hb hk cs accum1 hf ih =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    have hqs : q ≠ .star := fun h => hk (by simp [h, ExprShape.getKeyArgs])
    obtain ⟨m, hm, -, hks, hch⟩ := Trie.wf_node.1 ht
    simp only [Array.size_push, Nat.zero_add, Nat.add_right_cancel_iff] at hm
    subst hm
    simp only [Array.pop_push] at ih ⊢
    have hacc : w ∈ accum1 ↔ w ∈ accum ∨ ∃ es, UnifyMany es qs' ∧ Mem (.node cs) ((P es).push .star) w := by
      simp only [accum1, Array.pop_push]
      split
      · rename_i t0 h0
        have hmem := Array.mem_of_getElem? h0
        rw [ih t0 h0 (by simpa [Key.arity] using hch _ hmem)]
        simp only [exists_empty_iff, mem_node_push_iff]
        apply or_congr_right
        constructor
        · rintro ⟨es, hu, hm⟩; exact ⟨es, hu, t0, hmem, hm⟩
        · rintro ⟨es, hu, c, hc, hm⟩
          obtain rfl := congrArg Prod.snd (hks.eq_of_mem hc hmem rfl)
          exact ⟨es, hu, hm⟩
      · rename_i hne
        simp only [mem_node_push_iff]
        constructor
        · exact .inl
        · rintro (h | ⟨es, hu, c, hc, hm⟩)
          · exact h
          · exact absurd (hks.getElem?_zero hc) (hne c)
    rw [hacc, exists_empty_iff, unify_top_iff hqs]
    simp only [mem_node_push_iff]
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact .inr (.inl h)
    · rintro (h | h | ⟨es, hu, c, hc, hm⟩)
      · exact .inl h
      · exact .inr h
      · exact absurd (hf ▸ hks.binSearch_eq hc (d := Trie.empty)) (by simp)
  | case10 qs accum keyArgs hb hk cs accum1 k' c hf ih2 ih1 =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    have hqs : q ≠ .star := fun h => hk (by simp [h, ExprShape.getKeyArgs])
    obtain ⟨m, hm, -, hks, hch⟩ := Trie.wf_node.1 ht
    simp only [Array.size_push, Nat.zero_add, Nat.add_right_cancel_iff] at hm
    subst hm
    simp only [Array.pop_push] at ih1 ih2 ⊢
    obtain ⟨hcmem, hk'⟩ := Trie.binSearch_key hf
    simp only at hk'
    subst hk'
    have hacc : w ∈ accum1 ↔ w ∈ accum ∨ ∃ es, UnifyMany es qs' ∧ Mem (.node cs) ((P es).push .star) w := by
      simp only [accum1, Array.pop_push]
      split
      · rename_i t0 h0
        have hmem := Array.mem_of_getElem? h0
        rw [ih2 t0 h0 (by simpa [Key.arity] using hch _ hmem)]
        simp only [exists_empty_iff, mem_node_push_iff]
        apply or_congr_right
        constructor
        · rintro ⟨es, hu, hm⟩; exact ⟨es, hu, t0, hmem, hm⟩
        · rintro ⟨es, hu, c, hc, hm⟩
          obtain rfl := congrArg Prod.snd (hks.eq_of_mem hc hmem rfl)
          exact ⟨es, hu, hm⟩
      · rename_i hne
        simp only [mem_node_push_iff]
        constructor
        · exact .inl
        · rintro (h | ⟨es, hu, c, hc, hm⟩)
          · exact h
          · exact absurd (hks.getElem?_zero hc) (hne c)
    have hc := hch _ hcmem
    rw [ih1 (by simpa [ExprShape.size_getKeyArgs_snd] using hc), hacc, exists_empty_iff, exists_empty_iff,
      unify_top_iff hqs]
    simp only [mem_node_push_iff]
    constructor
    · rintro ((h | h) | ⟨es, hu, hm⟩)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨es, hu, c, hcmem, hm⟩)
    · rintro (h | h | ⟨es, hu, c', hc', hm⟩)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · obtain rfl := congrArg Prod.snd (hks.eq_of_mem hc' hcmem rfl)
        exact .inr ⟨es, hu, hm⟩
  | case11 qs accum keyArgs hb hk k c hkk ih =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    have hqs : q ≠ .star := fun h => hk (by simp [h, ExprShape.getKeyArgs])
    obtain ⟨m, hm, hns, hc⟩ := Trie.wf_chain.1 ht
    simp only [Array.size_push, Nat.zero_add, Nat.add_right_cancel_iff] at hm
    subst hm
    obtain rfl := beq_iff_eq.1 hkk
    simp only [Array.pop_push] at ih ⊢
    rw [ih (by simpa [ExprShape.size_getKeyArgs_snd] using hc), exists_empty_iff, exists_empty_iff,
      unify_top_iff hqs]
    simp only [mem_chain_push_iff]
    apply or_congr_right
    constructor
    · rintro ⟨es, hu, hm⟩; exact .inr ⟨es, hu, trivial, hm⟩
    · rintro (⟨es, hu, h, -⟩ | ⟨es, hu, -, hm⟩)
      · exact absurd h.symm hns
      · exact ⟨es, hu, hm⟩
  | case12 qs accum keyArgs hb hk k c hkk =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    have hqs : q ≠ .star := fun h => hk (by simp [h, ExprShape.getKeyArgs])
    obtain ⟨m, -, hns, -⟩ := Trie.wf_chain.1 ht
    rw [exists_empty_iff, unify_top_iff hqs]
    simp only [mem_chain_push_iff]
    constructor
    · exact .inl
    · rintro (h | ⟨es, hu, h, -⟩ | ⟨es, hu, h, -⟩)
      · exact h
      · exact absurd h.symm hns
      · exact absurd (by simp [h]) hkk
  | case13 qs accum keyArgs hb hk n c ih =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    have hqs : q ≠ .star := fun h => hk (by simp [h, ExprShape.getKeyArgs])
    have hkq : q.getKeyArgs.fst ≠ .star := fun h => hqs (ExprShape.getKeyArgs_fst_eq_star.1 h)
    obtain ⟨m, hm, hn, -, -, -⟩ := Trie.wf_stars.1 ht
    simp only [Array.size_push, Nat.zero_add, Nat.add_right_cancel_iff] at hm
    subst hm
    simp only [Array.pop_push] at ih ⊢
    rw [ih (by simpa using Trie.wf_mkStars_pred (by simpa using ht)), exists_empty_iff, exists_empty_iff,
      unify_top_iff hqs]
    simp only [mem_stars_iff_pred hn]
    apply or_congr_right
    constructor
    · rintro ⟨es, hu, hm⟩; exact .inl ⟨es, hu, _, rfl, hm⟩
    · rintro (⟨es, hu, r, he, hm⟩ | ⟨es, hu, r, he, -⟩)
      · obtain ⟨-, rfl⟩ := Array.push_eq_push.1 he
        exact ⟨es, hu, hm⟩
      · exact absurd (Array.push_eq_push.1 he).1 hkq

theorem Spec.mem_foldl_insert_iff {kvs : KVMap α} (ht : t.WF 1) :
    Mem (kvs.foldl (fun x ⟨k, v⟩ => Trie.insert k.getKeyPath v x) t) p w ↔
      Mem t p w ∨ ∃ kv ∈ kvs, p = kv.key.getKeyPath ∧ w = kv.value := by
  induction kvs generalizing t with
  | nil => simp
  | cons kv kvs ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.foldl_cons]
    rw [ih (ht.insert (validPath_getKeyPath k) v), mem_insert_iff ht (validPath_getKeyPath k)]
    simp only [List.mem_cons, exists_eq_or_imp]
    grind

theorem Trie.getUnify_empty (skip : Nat) (qs : Array ExprShape) (accum : Array α) :
    (Trie.empty : Trie α).getUnify skip qs accum = accum := by
  cases skip with
  | succ skip => unfold getUnify; simp [Trie.empty]
  | zero =>
    unfold getUnify
    split
    · simp [Trie.empty, nodeValues]
    · split
      · unfold getUnify; simp [Trie.empty]
      · simp only [Trie.empty]
        split
        · simp_all
        · split <;> simp_all [Array.binSearch]

end

/-!
# Correctness
-/

def KVMap.toTrie : KVMap α → Trie α
  | [] => Trie.empty
  | ⟨k, v⟩ :: map =>
      map.foldl (init := Trie.singleton k.getKeyPath v)
        (fun x ⟨k, v⟩ => Trie.insert k.getKeyPath v x)

/-! Repeated insertion produces well-formed tries. -/
theorem Trie.WF.construct {kvMap : KVMap α} : kvMap = [] ∨ kvMap.toTrie.WF 1 := by
  have step : ∀ (kvs : KVMap α) (t : Trie α), t.WF 1 →
      (kvs.foldl (fun x ⟨k, v⟩ => Trie.insert k.getKeyPath v x) t).WF 1 := by
    intro kvs
    induction kvs with
    | nil => exact fun _ h => h
    | cons kv kvs ih =>
      obtain ⟨k, v⟩ := kv
      exact fun t h => ih _ (h.insert (Spec.validPath_getKeyPath k) v)
  match kvMap with
  | [] => exact .inl rfl
  | ⟨k, v⟩ :: kvs => exact .inr (step kvs _ (Trie.wf_singleton (Spec.validPath_getKeyPath k) v))

/-! A well-formed trie can be decomposed into key/value mappings. -/
theorem Trie.WF.deconstruct {t : Trie α} : t.WF 1 → ∃ elements : KVMap α, t = elements.toTrie := by
  classical
  intro h
  obtain ⟨p, v, L, ⟨hp, hL⟩, rfl⟩ := Trie.WF.exists_build 1 t h
  let shapeOf (q : Array Key) : ExprShape :=
    if hq : Spec.ValidPath 1 q then (Spec.exists_getKeyPath hq).choose else .star
  have hshape : ∀ q, Spec.ValidPath 1 q → (shapeOf q).getKeyPath = q := fun q hq => by
    simp only [shapeOf, hq, ↓reduceDIte]
    exact (Spec.exists_getKeyPath hq).choose_spec
  refine ⟨⟨shapeOf p, v⟩ :: L.map fun q => ⟨shapeOf q.1, q.2⟩, ?_⟩
  clear h
  simp only [KVMap.toTrie, List.foldl_map, hshape p hp, Spec.build]
  generalize Trie.singleton p v = s
  induction L generalizing s with
  | nil => rfl
  | cons q L ih =>
    simp only [List.foldl_cons, hshape q.1 (hL q (by simp))]
    exact ih (fun r hr => hL r (by simp [hr])) _

/-! The key-value map view and {name}`Trie.getUnify` agree on queries. -/
theorem Trie.mem_getUnify_toTrie {kvMap : KVMap α} :
  v ∈ kvMap.toTrie.getUnify 0 #[k] #[] ↔ v ∈ kvMap.getUnify k := by
    match kvMap, (Trie.WF.construct (kvMap := kvMap)) with
  | [], _ => simp [KVMap.toTrie, KVMap.getUnify, Trie.getUnify_empty]
  | kv :: kvs, .inl h => exact absurd h (by simp)
  | ⟨k₀, v₀⟩ :: kvs, .inr ht =>
    have hmem : ∀ p w, Spec.Mem (KVMap.toTrie (⟨k₀, v₀⟩ :: kvs)) p w ↔
        ∃ kv ∈ (⟨k₀, v₀⟩ :: kvs : KVMap α), p = kv.key.getKeyPath ∧ w = kv.value := by
      intro p w
      simp only [KVMap.toTrie]
      rw [Spec.mem_foldl_insert_iff (Trie.wf_singleton (Spec.validPath_getKeyPath k₀) v₀),
        Spec.mem_singleton_iff]
      simp
    rw [Spec.mem_getUnify_iff (by simpa using ht)]
    simp only [Spec.exists_empty_iff]
    simp only [hmem]
    simp only [KVMap.getUnify, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨es, hu, kv, hkv, hp, rfl⟩)
      · simp at h
      · obtain ⟨e, rfl⟩ : ∃ e, es = #[e] := by
          have := hu.size_eq
          rcases es with ⟨_ | ⟨e, _ | _⟩⟩ <;> simp at this
          exact ⟨e, rfl⟩
        have he : e = kv.key := by
          have := Spec.flatMap_getKeyPath_inj (xs := #[e]) (ys := #[kv.key]) (by simpa using hp) rfl
          simpa using this
        subst he
        exact ⟨kv, ⟨hkv, (Spec.unifyMany_push (es := #[]) (qs := #[])).1 hu |>.2⟩, rfl⟩
    · rintro ⟨kv, ⟨hkv, hu⟩, rfl⟩
      exact .inr ⟨#[kv.key], (Spec.unifyMany_push (es := #[]) (qs := #[])).2 ⟨Spec.unifyMany_empty, hu⟩,
        kv, hkv, by simp, rfl⟩
