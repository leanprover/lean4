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
    {lit}`c e1 e2 e3` is represented as {lean (type := "ExprShape")}`.const c #[e1, e2, e3]`.
    -/
  | const (declName : Name) (args : Array ExprShape)
    /--
    {given -show}`x, e1, e2, e3` The term
    {lit}`x e1 e2 e3` is represented as {lean (type := "ExprShape")}`.fvar x #[e1, e2, e3]`.
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

This implementation incorporates suffix tries, a performance optimization being explored in
-/

/--
{given -show}`g, s`
A tries linearizes a structured term into a sequence of keys: the expression `g (s *) "hi"` can be
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
  | .const c args => ⟨.const c args.size, args.reverse⟩
  | .fvar x args => ⟨.fvar x args.size, args.reverse⟩
  | .arrow e => ⟨.arrow, #[e]⟩
  | .star => ⟨.star, #[]⟩
  | .other => ⟨.other, #[]⟩

/--
Transforms a shape into a sequence of keys (with the first key at the index 0).
-/
def ExprShape.getKeyPath : ExprShape → Array Key
  | .lit l => #[.lit l]
  | .const c args => #[.const c args.size] ++ args.flatMap getKeyPath
  | .fvar x args => #[.fvar x args.size] ++ args.flatMap getKeyPath
  | .arrow e => #[.arrow] ++ getKeyPath e
  | .star => #[.star]
  | .other => #[.other]

inductive Trie (α : Type) : Type where
  | leaf (vs : Array α)
  | node (cs : Array (Key × Trie α))
    /-- Special case optimization: node with one (non-star) key -/
  | chain (k : Key) (t : Trie α)
    /-- Special case optimization: chain of {name}`n` nodes that all have the key {lean (type := "Key")}`.star` -/
  | stars (n : Nat) (t : Trie α)
    /-- Terminal chain from {lean}`keys[start:]` to {name}`v` -/
  | suffix (keys : Array Key) (start : Nat) (h : start < keys.size) (v : α)

def Trie.empty : Trie α := Trie.node #[]

instance : Inhabited (Trie α) where
  default := Trie.empty

/-- Pass over stars starting at _n_ and return the first index not containing a star -/
def Key.passStars (n : Nat) (args : Array Key) (h : n < args.size) : Nat :=
  if args[n] != .star then
    n
  else if _ : n + 1 = args.size then
    args.size
  else
    Key.passStars (n + 1) args (by omega)

/-- Adds {name}`n` stars to a trie, preserving trie well-formedness. -/
def Trie.mkStars (n : Nat) (t : Trie α) : Trie α :=
  if n = 0 then
    t
  else match t with
  | .stars m t => .stars (n + m) t
  | _ => .stars n t

/--
Creates {name}`Trie.chain` or {name}`Trie.stars` singleton node. Does not check for rewindable
suffixes.
-/
def Trie.mkChain : Key → Trie α → Trie α
  | .star, .stars n c => .stars (n + 1) c
  | .star, c => .stars 1 c
  | k, c => .chain k c

/--
Makes a node from an array of keys and tries. Checks {name}`Trie.suffix` nodes for whether they
can be rewound into the correct form.
-/
def Trie.mkNode (cs : Array (Key × Trie α)) : Trie α :=
  if _ : cs.size = 1 then
    let c := cs[0]
    match c.snd with
    | .suffix keys (start + 1) h t =>
      if c.fst == keys[start]' (by omega) then
        .suffix keys start (by omega) t
      else
        .mkChain c.fst c.snd
    | _ =>
      .mkChain c.fst c.snd
  else
    .node cs

def Trie.nodeValues : Trie α → Array α
  | .leaf vs => vs
  | _ => #[]

def Trie.nodeChildren : Trie α → Array (Key × Trie α)
  | .leaf vs => #[]
  | .node cs => cs
  | .chain k c => #[(k, c)]
  | .stars n c => #[(.star, .mkStars (n - 1) c)]
  | .suffix keys start h v =>
    if _ : start + 1 = keys.size then
      #[(keys[start], .leaf #[v])]
    else
      #[(keys[start], .suffix keys (start + 1) (by omega) v)]

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

theorem List.le_sum_of_mem_nat {l : List Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l <;> simp_all <;> grind

/--
A size measure for tries that decreases from a trie to each of its {name}`Trie.nodeChildren`: a run
of {lit}`n` stars counts as {lit}`n` nodes, and a suffix counts its remaining keys.
-/
def Trie.measure : Trie α → Nat
  | .leaf _ => 1
  | .node cs => 1 + (cs.map (·.snd.measure)).sum
  | .chain _ c => 1 + c.measure
  | .stars n c => 1 + n + c.measure
  | .suffix keys start _ _ => 1 + (keys.size - start)
decreasing_by
  all_goals first
  | (simp; omega)
  | (rename_i kc hkc; have := Array.sizeOf_lt_of_mem hkc; cases kc; simp at this ⊢; omega)

/-- Removing a star decreases the measure, even for a zero-length run. -/
theorem Trie.measure_mkStars_pred_lt (n : Nat) (c : Trie α) :
    (mkStars (n - 1) c).measure < (Trie.stars n c).measure := by
  unfold mkStars
  split
  · simp only [measure]; omega
  · split <;> simp only [measure] <;> omega

theorem Trie.measure_lt_of_mem_nodeChildren {t : Trie α} (h : kc ∈ t.nodeChildren) :
    kc.snd.measure < t.measure := by
  cases t with
  | leaf vs => simp [nodeChildren] at h
  | node cs =>
    simp only [nodeChildren] at h
    have := List.le_sum_of_mem_nat (List.mem_map_of_mem (f := (·.snd.measure)) (Array.mem_toList_iff.2 h))
    simp only [measure, ← Array.sum_toList, Array.toList_map]
    omega
  | chain k c =>
    simp only [nodeChildren, Array.mem_singleton] at h
    subst h; simp only [measure]; omega
  | stars n c =>
    simp only [nodeChildren, Array.mem_singleton] at h
    subst h
    exact measure_mkStars_pred_lt n c
  | suffix keys start hs v =>
    simp only [nodeChildren] at h
    split at h <;> simp only [Array.mem_singleton] at h <;> subst h <;> simp only [measure] <;> omega

theorem ExprShape.getKeyPath_size_pos (e : ExprShape) : 0 < e.getKeyPath.size := by
  cases e <;> simp [getKeyPath] <;> omega

/-!
## Trie Operations
-/

def Trie.singleton (i : Nat) (path : Array Key) (h : i ≤ path.size) (v : α) : Trie α :=
  if _ : i = path.size then
    .leaf #[v]
  else
    .suffix path i (by omega) v

/-- Inserts the trie along the path -/
def Trie.insert (i : Nat) (path : Array Key) (h : i ≤ path.size) (v : α) (t : Trie α) : Trie α :=
  if _ : i = path.size then
    .leaf (t.nodeValues.push v)
  else
    .mkNode <| Id.run $ t.nodeChildren.binInsertM (·.fst < ·.fst)
      (fun (_, c) => (path[i], insert (i + 1) path (by omega) v c))
      (fun _ => (path[i], .singleton (i + 1) path (by omega) v))
      (path[i], .empty)

def Trie.exactLookup (i : Nat) (path : Array Key) (h : i ≤ path.size) (t : Trie α) : Array α :=
  if _ : i = path.size then
    t.nodeValues
  else match t.nodeChildren.binSearch (path[i], .empty) (·.fst < ·.fst) with
    | .none => #[]
    | .some (_, c) => exactLookup (i + 1) path (by omega) c

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

def Trie.getUnify (skip : Nat) (todo : Array ExprShape) (accum : Array α) (t : Trie α) : Array α :=
  match skip with
  | skip + 1 =>
    t.nodeChildren.attach.foldl (init := accum) fun accum ⟨kc, _⟩ => getUnify (skip + kc.fst.arity) todo accum kc.snd
  | 0 =>
    match _h : todo.back?.map ExprShape.getKeyArgs with
    | .none => accum ++ t.nodeValues
    | .some keyArgs =>
      if keyArgs.fst == .star then
        getUnify 1 todo.pop accum t
      else
        let cs := t.nodeChildren
        let accum :=
          match _hs : cs[0]? with
          | .some (.star, t) => getUnify 0 todo.pop accum t
          | _ => accum
        match _hf : cs.binSearch (keyArgs.fst, .empty) (·.fst < ·.fst) with
        | .some (_, c) => getUnify 0 (todo.pop ++ keyArgs.snd) accum c
        | .none => accum
termination_by (t.measure, todo.size)
decreasing_by
  all_goals first
  | apply Prod.Lex.left
    first
    | exact Trie.measure_lt_of_mem_nodeChildren ‹_ ∈ t.nodeChildren›
    | exact Trie.measure_lt_of_mem_nodeChildren (Array.mem_of_getElem? _hs)
    | exact Trie.measure_lt_of_mem_nodeChildren (Array.mem_of_binSearch_eq_some _hf).1
  | apply Prod.Lex.right
    obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.1 _h
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 he
    simp

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

Does not capture a property that .mkNode preserves, which is that if we have
{given -show}`k,keys,v`{given -show}`h : 1 < keys.size`{lean (type := "Trie α")}`.chain k (.suffix keys 1 (by omega) v)`, we expect
that {lean}`k != keys[0]!`.
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
  | n+1, .suffix keys start h v =>
    if _ : start + 1 = keys.size then
      keys[start].arity = 0 ∧ n = 0
    else
      (Trie.suffix keys (start + 1) (by omega) v).WF (n + keys[start].arity)
termination_by _ t => t.measure
decreasing_by
  · exact Trie.measure_lt_of_mem_nodeChildren (t := .node cs) (by simpa only [nodeChildren] using
    ‹c ∈ cs›)
  · simp only [Trie.measure]; omega
  · simp only [Trie.measure]; omega
  · simp only [Trie.measure]; omega

/--
Our correctness properties utilize this function, which transforms a list of key-value pairs to a
trie via repeated insertion.
-/
def KVMap.toTrie : KVMap α → Trie α
  | [] => Trie.empty
  | ⟨k, v⟩ :: map =>
      map.foldl (init := Trie.suffix k.getKeyPath 0 (k.getKeyPath_size_pos) v)
        (fun x ⟨k, v⟩ => Trie.insert 0 k.getKeyPath (Nat.zero_le _) v x)

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

theorem Literal.eq_of_not_lt {l l' : Literal} (h₁ : l.lt l' = false) (h₂ : l'.lt l = false) : l = l' := by
  cases l <;> cases l' <;> simp_all [Literal.lt] <;> grind

theorem Literal.lt_irrefl (l : Literal) : l.lt l = false := by
  cases l <;> simp [Literal.lt, Std.lt_irrefl]

theorem Literal.lt_trans {a b c : Literal} (h₁ : a.lt b) (h₂ : b.lt c) : a.lt c := by
  cases a <;> cases b <;> cases c <;> simp_all [Literal.lt] <;> grind

theorem Key.eq_of_not_lt {k k' : Key} (h₁ : k.lt k' = false) (h₂ : k'.lt k = false) : k = k' := by
  cases k <;> cases k' <;> simp_all [Key.lt, Key.ctorIdx]
  · exact Literal.eq_of_not_lt (by simpa [LT.lt] using h₁) (by simpa [LT.lt] using h₂)
  case fvar.fvar x _ y _ =>
    have := Name.eq_of_not_quickLt h₁.1 h₂.1
    cases x; cases y
    grind
  · have := Name.eq_of_not_quickLt h₁.1 h₂.1
    grind

theorem Key.lt_iff {a b : Key} : a < b ↔ Key.lt a b = true := Iff.rfl

private theorem Literal.lt_iff {a b : Literal} : a < b ↔ a.lt b = true := Iff.rfl

theorem Key.lt_irrefl (k : Key) : ¬ k < k := by
  rw [Key.lt_iff]
  cases k <;> simp [Key.lt, Name.quickLt_irrefl, Literal.lt_iff, Literal.lt_irrefl]

theorem Key.lt_trans {a b c : Key} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [Key.lt_iff] at *
  cases a <;> cases b <;> cases c <;>
    simp_all [Key.lt, Key.ctorIdx, Literal.lt_iff] <;>
    grind [Name.quickLt_trans, Literal.lt_trans]

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

/-- In strictly sorted children, a key identifies its index. -/
theorem Spec.KeysSorted.getElem_fst_inj {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    (hi : i < cs.size) (hj : j < cs.size) : cs[i].fst = cs[j].fst ↔ i = j := by
  constructor
  · intro h
    have hij := hs.lt hi hj
    have hji := hs.lt hj hi
    grind only [Key.lt_irrefl]
  · rintro rfl; rfl

theorem Spec.KeysSorted.eq_of_mem {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    (ha : a ∈ cs) (hb : b ∈ cs) (h : a.fst = b.fst) : a = b := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hb
  obtain rfl := (hs.getElem_fst_inj hi hj).1 h
  rfl

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
  clear h_sorted h_asymm h_k h_x h_eq
  fun_induction Array.binSearchAux lt id as k lo hi h
  case case5 => exact ⟨_, rfl⟩
  all_goals grind only

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

section
variable {α : Type}

/-!
## Shapes and their key paths
-/

/-- The key path of a list of shapes, first shape first. -/
def Spec.F (ds : List ExprShape) : List Key := ds.flatMap (·.getKeyPath.toList)

/-- The key path of a query stack: the top of the stack (its back) comes first. -/
abbrev Spec.P (es : Array ExprShape) : List Key := F es.toList.reverse

theorem Spec.F_nil : F [] = [] := rfl
theorem Spec.F_cons : F (d :: ds) = d.getKeyPath.toList ++ F ds := rfl
theorem Spec.F_append : F (ds ++ ds') = F ds ++ F ds' := List.flatMap_append

theorem Spec.P_empty : P #[] = [] := rfl
theorem Spec.P_push : P (es.push e) = e.getKeyPath.toList ++ P es := by simp [P, F_cons]
theorem Spec.P_append : P (es ++ es') = P es' ++ P es := by simp [P, F_append]

theorem ExprShape.getKeyPath_eq (e : ExprShape) :
    e.getKeyPath.toList = e.getKeyArgs.fst :: Spec.P e.getKeyArgs.snd := by
  cases e <;> simp [getKeyPath, getKeyArgs, Spec.P, Spec.F]

/-- The shape whose key is {lit}`k` and whose argument stack is {lit}`args`. -/
def Spec.toShape : Key → Array ExprShape → ExprShape
  | .lit l, _ => .lit l
  | .const c _, args => .const c args.reverse
  | .fvar x _, args => .fvar x args.reverse
  | .arrow, args => .arrow (args[0]?.getD .star)
  | .star, _ => .star
  | .other, _ => .other

theorem Spec.getKeyArgs_toShape {k : Key} {args : Array ExprShape} (h : args.size = k.arity) :
    (toShape k args).getKeyArgs = (k, args) := by
  cases k <;> simp only [Key.arity] at h
  case const c n => subst h; simp [toShape, ExprShape.getKeyArgs]
  case fvar x n => subst h; simp [toShape, ExprShape.getKeyArgs]
  case arrow =>
    obtain ⟨e, rfl⟩ := Array.size_eq_one_iff.1 h
    simp [toShape, ExprShape.getKeyArgs]
  all_goals
    obtain rfl := Array.eq_empty_of_size_eq_zero h
    simp [toShape, ExprShape.getKeyArgs]

theorem Spec.getKeyPath_toShape {k : Key} {args : Array ExprShape} (h : args.size = k.arity) :
    (toShape k args).getKeyPath.toList = k :: P args := by
  rw [ExprShape.getKeyPath_eq, getKeyArgs_toShape h]

theorem ExprShape.getKeyArgs_inj {e e' : ExprShape} (h : e.getKeyArgs = e'.getKeyArgs) : e = e' := by
  cases e <;> cases e' <;> simp_all [getKeyArgs]

theorem ExprShape.size_getKeyArgs_snd {e : ExprShape} : e.getKeyArgs.snd.size = e.getKeyArgs.fst.arity := by
  cases e <;> simp [getKeyArgs, Key.arity]

theorem ExprShape.getKeyArgs_fst_eq_star {e : ExprShape} : e.getKeyArgs.fst = .star ↔ e = .star := by
  cases e <;> simp [getKeyArgs]

/-- Splitting off one complete shape from the front of a list of shapes. -/
theorem Spec.exists_cons_iff {X : List Key} {s : Nat} {R : List Key → Prop} :
    (∃ ds : List ExprShape, ds.length = s + 1 ∧ R (F ds ++ X)) ↔
      ∃ k, ∃ ds : List ExprShape, ds.length = s + k.arity ∧ R (k :: (F ds ++ X)) := by
  constructor
  · rintro ⟨_ | ⟨d, ds⟩, hl, hr⟩
    · simp at hl
    · refine ⟨d.getKeyArgs.fst, d.getKeyArgs.snd.toList.reverse ++ ds, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp [ExprShape.size_getKeyArgs_snd, hl, Nat.add_comm]
      · rw [F_cons, ExprShape.getKeyPath_eq] at hr
        simpa [F_append] using hr
  · rintro ⟨k, ds, hl, hr⟩
    refine ⟨toShape k (ds.take k.arity).reverse.toArray :: ds.drop k.arity, by simp; omega, ?_⟩
    rw [F_cons, getKeyPath_toShape (by simp; omega)]
    have : F ds = F (ds.take k.arity) ++ F (ds.drop k.arity) := by rw [← F_append, List.take_append_drop]
    simpa [this, P] using hr

/-- Key paths determine the shapes they came from. -/
theorem Spec.F_inj : ∀ {ds ds' : List ExprShape} {X X' : List Key},
    ds.length = ds'.length → F ds ++ X = F ds' ++ X' → ds = ds' ∧ X = X'
  | [], [], _, _, _, h => by simpa [F_nil] using h
  | d :: ds, d' :: ds', X, X', hl, h => by
    rw [F_cons, F_cons, ExprShape.getKeyPath_eq, ExprShape.getKeyPath_eq] at h
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hk, h⟩ := h
    have hl' : (d.getKeyArgs.snd.toList.reverse ++ ds).length = (d'.getKeyArgs.snd.toList.reverse ++ ds').length := by
      simp only [List.length_append, List.length_reverse, Array.length_toList, ExprShape.size_getKeyArgs_snd, hk]
      simp at hl; omega
    have h' : F (d.getKeyArgs.snd.toList.reverse ++ ds) ++ X = F (d'.getKeyArgs.snd.toList.reverse ++ ds') ++ X' := by
      simpa [F_append] using h
    obtain ⟨hds, rfl⟩ := F_inj hl' h'
    have hsz : (d.getKeyArgs.snd.toList.reverse).length = (d'.getKeyArgs.snd.toList.reverse).length := by
      simp [ExprShape.size_getKeyArgs_snd, hk]
    obtain ⟨ha, rfl⟩ := List.append_inj hds hsz
    refine ⟨?_, rfl⟩
    rw [ExprShape.getKeyArgs_inj (Prod.ext hk (by simpa using ha))]
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
termination_by ds => (F ds).length
decreasing_by
  rw [F_append, F_cons, ExprShape.getKeyPath_eq]
  simp

theorem ExprShape.getKeyPath_inj {e e' : ExprShape} (h : e.getKeyPath.toList = e'.getKeyPath.toList) : e = e' := by
  have := (Spec.F_inj (ds := [e]) (ds' := [e']) (X := []) (X' := []) rfl (by simpa [Spec.F_cons, Spec.F_nil] using h)).1
  simpa using this

/-- Key paths of {lit}`n` complete shapes. -/
def Spec.ValidPath (n : Nat) (p : List Key) : Prop := ∃ ds : List ExprShape, ds.length = n ∧ F ds = p

theorem Spec.validPath_nil_iff : ValidPath n [] ↔ n = 0 := by
  constructor
  · rintro ⟨_ | ⟨d, ds⟩, rfl, h⟩
    · rfl
    · have := d.getKeyPath_size_pos
      simp [F_cons] at h; simp [h] at this
  · rintro rfl; exact ⟨[], rfl, rfl⟩

theorem Spec.validPath_cons_iff : ValidPath n (k :: p) ↔ ∃ m, n = m + 1 ∧ ValidPath (m + k.arity) p := by
  cases n with
  | zero => simp [ValidPath, F_nil]
  | succ n =>
    simp only [Nat.add_right_cancel_iff, exists_eq_left', ValidPath]
    have h := exists_cons_iff (X := []) (s := n) (R := (· = k :: p))
    simp only [List.append_nil, List.cons.injEq] at h
    rw [h]
    grind only

theorem Spec.validPath_getKeyPath (e : ExprShape) : ValidPath 1 e.getKeyPath.toList :=
  ⟨[e], rfl, by simp [F_cons, F_nil]⟩

theorem Spec.exists_getKeyPath (h : ValidPath 1 p) : ∃ e : ExprShape, e.getKeyPath.toList = p := by
  obtain ⟨_ | ⟨e, _ | _⟩, hl, rfl⟩ := h <;> simp at hl
  exact ⟨e, by simp [F_cons, F_nil]⟩

/-!
## Semantics: what a trie stores
-/

/-- {lit}`Spec.Mem t p w`: the trie {lit}`t` stores {lit}`w` under the key path {lit}`p` (first key first). -/
inductive Spec.Mem : Trie α → List Key → α → Prop where
  | here : w ∈ t.nodeValues → Mem t [] w
  | child : (k, c) ∈ t.nodeChildren → Mem c p w → Mem t (k :: p) w

theorem Spec.mem_nil_iff : Mem t [] w ↔ w ∈ t.nodeValues := by
  constructor
  · intro h; cases h; assumption
  · exact .here

theorem Spec.mem_cons_iff : Mem t (k :: p) w ↔ ∃ c, (k, c) ∈ t.nodeChildren ∧ Mem c p w := by
  constructor
  · intro h; cases h; exact ⟨_, by assumption, by assumption⟩
  · rintro ⟨c, hc, h⟩; exact .child hc h

/-!
## Well-formedness through the node interface
-/

theorem Trie.wf_zero_iff {t : Trie α} : t.WF 0 ↔ ∃ vs, t = .leaf vs ∧ 0 < vs.size := by
  cases t <;> simp [Trie.WF]

theorem Trie.wf_node_iff {cs : Array (Key × Trie α)} : (Trie.node cs).WF (n + 1) ↔
    cs.size > 1 ∧ Spec.KeysSorted cs ∧ ∀ c ∈ cs, c.snd.WF (n + c.fst.arity) := by
  simp [Trie.WF, Spec.KeysSorted, List.pairwise_map]

theorem Trie.wf_chain_iff : (Trie.chain k c : Trie α).WF (n + 1) ↔ k ≠ .star ∧ c.WF (n + k.arity) := by
  simp [Trie.WF]

theorem Trie.wf_stars_iff : (Trie.stars j c : Trie α).WF n ↔
    j > 0 ∧ n ≥ j ∧ ¬ isStars c ∧ c.WF (n - j) := by
  cases n with
  | zero => simp only [Trie.WF, false_iff]; omega
  | succ n => simp only [Trie.WF]

theorem Trie.wf_suffix_succ_iff {keys : Array Key} {h : start < keys.size} :
    (Trie.suffix keys start h v : Trie α).WF (n + 1) ↔
      if _ : start + 1 = keys.size then keys[start].arity = 0 ∧ n = 0
      else (Trie.suffix keys (start + 1) (by omega) v).WF (n + keys[start].arity) := by
  rw [Trie.WF]

theorem Trie.mkStars_of_not_isStars {c : Trie α} (hc : ¬ isStars c) (hj : 0 < j) : mkStars j c = .stars j c := by
  unfold mkStars
  simp only [show ¬ j = 0 by omega, ↓reduceIte]
  split
  · simp [isStars] at hc
  · rfl

/-- Every child of a well-formed trie is well formed at the depth that its key's arity dictates. -/
theorem Trie.WF.succ {t : Trie α} (h : t.WF (m + 1)) :
    t.nodeValues = #[] ∧ Spec.KeysSorted t.nodeChildren ∧
      ∀ kc ∈ t.nodeChildren, kc.snd.WF (m + kc.fst.arity) := by
  cases t with
  | leaf vs => simp [Trie.WF] at h
  | node cs => obtain ⟨-, hs, hc⟩ := wf_node_iff.1 h; exact ⟨rfl, hs, hc⟩
  | chain k c =>
    obtain ⟨-, hc⟩ := wf_chain_iff.1 h
    refine ⟨rfl, by simp [Spec.KeysSorted, nodeChildren], ?_⟩
    simpa [nodeChildren] using hc
  | stars j c =>
    obtain ⟨hj, hle, hns, hc⟩ := wf_stars_iff.1 h
    refine ⟨rfl, by simp [Spec.KeysSorted, nodeChildren], ?_⟩
    simp only [nodeChildren, Array.mem_singleton, forall_eq, Key.arity, Nat.add_zero]
    by_cases hj1 : j = 1
    · subst hj1; simpa [mkStars] using hc
    · rw [mkStars_of_not_isStars hns (by omega)]
      rw [wf_stars_iff]
      grind only
  | suffix keys start hs v =>
    rw [wf_suffix_succ_iff] at h
    refine ⟨rfl, ?_, ?_⟩
    · simp only [nodeChildren]; split <;> simp [Spec.KeysSorted]
    · simp only [nodeChildren]
      split
      · rename_i heq; simp only [heq, ↓reduceDIte] at h
        simp only [Array.mem_singleton, forall_eq, h.1, h.2]
        simp [wf_zero_iff]
      · rename_i heq; simp only [heq, ↓reduceDIte] at h
        simpa using h

theorem Trie.WF.nodeChildren_eq_empty {t : Trie α} (h : t.WF 0) : t.nodeChildren = #[] := by
  obtain ⟨vs, rfl, -⟩ := wf_zero_iff.1 h; rfl

theorem Trie.nodeValues_mkChain : (mkChain k c : Trie α).nodeValues = #[] := by
  unfold mkChain; split <;> rfl

theorem Trie.nodeValues_mkNode {cs : Array (Key × Trie α)} : (mkNode cs).nodeValues = #[] := by
  fun_cases mkNode <;> first | rfl | exact nodeValues_mkChain

theorem Trie.nodeChildren_mkChain {c : Trie α} (hc : c.WF n) : (mkChain k c).nodeChildren = #[(k, c)] := by
  unfold mkChain
  split
  · rename_i j c'
    obtain ⟨hj, -, hns, -⟩ := wf_stars_iff.1 hc
    simp [nodeChildren, mkStars_of_not_isStars hns hj]
  · simp [nodeChildren, mkStars]
  · rfl

theorem Trie.nodeChildren_mkNode {cs : Array (Key × Trie α)} (hc : ∀ kc ∈ cs, ∃ n, kc.snd.WF n) :
    (mkNode cs).nodeChildren = cs := by
  by_cases h1 : cs.size = 1
  · obtain ⟨⟨k, c⟩, rfl⟩ := Array.size_eq_one_iff.1 h1
    obtain ⟨n, hn⟩ := hc (k, c) (by simp)
    unfold mkNode
    simp only [Array.size_singleton, ↓reduceDIte, Array.getElem_singleton]
    split
    · rename_i keys start hk v
      split
      · rename_i hbeq
        simp only [beq_iff_eq] at hbeq
        simp only [nodeChildren, show ¬ start + 1 = keys.size by omega, ↓reduceDIte]
        simp [hbeq]
      · exact nodeChildren_mkChain hn
    · exact nodeChildren_mkChain hn
  · unfold mkNode; simp only [h1, ↓reduceDIte]; rfl

theorem Trie.WF.mkChain {c : Trie α} (hc : c.WF (m + k.arity)) : (Trie.mkChain k c).WF (m + 1) := by
  unfold Trie.mkChain
  split
  · rename_i j c'
    simp only [Key.arity, Nat.add_zero, wf_stars_iff] at hc ⊢
    grind only
  · rename_i hns
    simp only [Key.arity, Nat.add_zero] at hc
    exact wf_stars_iff.2 ⟨by omega, by omega, by cases c <;> simp_all [isStars], by simpa using hc⟩
  · exact wf_chain_iff.2 ⟨by rintro rfl; simp_all, hc⟩

theorem Trie.WF.mkNode {cs : Array (Key × Trie α)} (hsz : 0 < cs.size) (hs : Spec.KeysSorted cs)
    (hc : ∀ kc ∈ cs, kc.snd.WF (m + kc.fst.arity)) : (Trie.mkNode cs).WF (m + 1) := by
  by_cases h1 : cs.size = 1
  · obtain ⟨⟨k, c⟩, rfl⟩ := Array.size_eq_one_iff.1 h1
    have hn := hc (k, c) (by simp)
    unfold Trie.mkNode
    simp only [Array.size_singleton, ↓reduceDIte, Array.getElem_singleton]
    split
    · rename_i keys start hk v
      split
      · rename_i hbeq
        simp only [beq_iff_eq] at hbeq
        rw [wf_suffix_succ_iff]
        simp only [show ¬ start + 1 = keys.size by omega, ↓reduceDIte]
        rw [← hbeq]
        exact hn
      · exact WF.mkChain hn
    · exact WF.mkChain hn
  · unfold Trie.mkNode; simp only [h1, ↓reduceDIte]
    exact wf_node_iff.2 ⟨by omega, hs, hc⟩

theorem Trie.wf_suffix_iff {keys : Array Key} {start : Nat} {h : start < keys.size} {n : Nat} :
    (Trie.suffix keys start h v : Trie α).WF n ↔ Spec.ValidPath n (keys.toList.drop start) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), Spec.validPath_cons_iff]
  cases n with
  | zero => simp [wf_zero_iff]
  | succ n =>
    rw [wf_suffix_succ_iff]
    split
    · rename_i he
      have : keys.toList.drop (start + 1) = [] := by simp; omega
      simp [this, Spec.validPath_nil_iff, and_comm]
    · rw [wf_suffix_iff]; simp
termination_by keys.size - start

theorem Spec.mem_leaf_iff : Mem (.leaf vs : Trie α) p w ↔ p = [] ∧ w ∈ vs := by
  cases p <;> simp [mem_nil_iff, mem_cons_iff, Trie.nodeValues, Trie.nodeChildren]

theorem Spec.mem_suffix_iff {keys : Array Key} {start : Nat} {h : start < keys.size} :
    Mem (.suffix keys start h v : Trie α) p w ↔ p = keys.toList.drop start ∧ w = v := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  cases p with
  | nil => simp [mem_nil_iff, Trie.nodeValues]
  | cons k q =>
    rw [mem_cons_iff]
    simp only [Trie.nodeChildren]
    split
    · rename_i he
      have : keys.toList.drop (start + 1) = [] := by simp; omega
      simp [this, mem_leaf_iff, and_assoc]
    · simp [mem_suffix_iff (keys := keys) (start := start + 1), and_assoc]
termination_by keys.size - start

theorem Spec.Mem.validPath {t : Trie α} (hm : Mem t p w) (ht : t.WF n) : ValidPath n p := by
  induction hm generalizing n with
  | here hw =>
    cases n with
    | zero => exact validPath_nil_iff.2 rfl
    | succ m => rw [ht.succ.1] at hw; simp at hw
  | child hc _ ih =>
    cases n with
    | zero => rw [ht.nodeChildren_eq_empty] at hc; simp at hc
    | succ m => exact validPath_cons_iff.2 ⟨m, rfl, ih (ht.succ.2.2 _ hc)⟩

theorem Spec.mem_mkNode_iff {cs : Array (Key × Trie α)} (hc : ∀ kc ∈ cs, ∃ n, kc.snd.WF n) :
    Mem (Trie.mkNode cs) p w ↔ ∃ k q c, p = k :: q ∧ (k, c) ∈ cs ∧ Mem c q w := by
  cases p <;> simp [mem_nil_iff, mem_cons_iff, Trie.nodeValues_mkNode, Trie.nodeChildren_mkNode hc] <;> grind

theorem Spec.mem_succ_iff {t : Trie α} (ht : t.WF (m + 1)) :
    Mem t p w ↔ ∃ k q c, p = k :: q ∧ (k, c) ∈ t.nodeChildren ∧ Mem c q w := by
  cases p <;> simp [mem_nil_iff, mem_cons_iff, ht.succ.1] <;> grind

end

section
variable {α : Type}

/-!
## Insertion
-/

theorem Array.binInsertM_id_induct {lt : α → α → Bool} {merge : α → Id α} {add : Unit → Id α}
    {as : Array α} {k : α} {P : Array α → Prop} (h_asymm : ∀ a b, lt a b → lt b a → False)
    (hmerge : ∀ i (hi : i < as.size) x, as[i] = x → lt x k = false → lt k x = false →
      P (as.set i (merge x).run))
    (hadd : ∀ i (hi : i ≤ as.size), (∀ h : 0 < i, lt as[i - 1] k) → (∀ h : i < as.size, lt k as[i]) →
      P (as.insertIdx i (add ()).run)) :
    P (as.binInsertM lt merge add k).run := by
  rcases Array.binInsertM_id_cases (lt := lt) (merge := merge) (add := add) (as := as) (k := k) h_asymm
    with ⟨i, hi, h1, h2, heq⟩ | ⟨i, hi, heq, h1, h2⟩
  · rw [heq]; exact hmerge i hi _ rfl h1 h2
  · rw [heq]; exact hadd i hi h1 h2

theorem Spec.KeysSorted.mem_set_iff {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat} (hi : i < cs.size)
    (hk : cs[i].fst = key) : (k, c) ∈ cs.set i (key, x) ↔ (k = key ∧ c = x) ∨ ((k, c) ∈ cs ∧ k ≠ key) := by
  have hkey {j : Nat} (hj : j < cs.size) : cs[j].fst = key ↔ j = i := by
    rw [← hk, hs.getElem_fst_inj hj hi]
  simp only [Array.mem_iff_getElem, Array.size_set, Array.getElem_set]
  grind

/-- A singleton stores exactly its remaining key path and preserves that path's depth. -/
theorem Spec.singleton_spec {path : Array Key} {hi : i ≤ path.size}
    (hv : ValidPath n (path.toList.drop i)) :
    (Trie.singleton i path hi v : Trie α).WF n ∧
      ∀ p w, Mem (Trie.singleton i path hi v) p w ↔ p = path.toList.drop i ∧ w = v := by
  unfold Trie.singleton
  split
  · rename_i he
    have hd : path.toList.drop i = [] := by simp [he]
    rw [hd, validPath_nil_iff] at hv
    rw [hv, hd]
    exact ⟨Trie.wf_zero_iff.2 ⟨_, rfl, by simp⟩, fun p w => by simp [mem_leaf_iff]⟩
  · exact ⟨Trie.wf_suffix_iff.2 hv, fun p w => mem_suffix_iff⟩

theorem Spec.insert_spec {path : Array Key} {hi : i ≤ path.size} {t : Trie α} (ht : t.WF n)
    (hv : ValidPath n (path.toList.drop i)) :
    (Trie.insert i path hi v t).WF n ∧
      ∀ p w, Mem (Trie.insert i path hi v t) p w ↔ Mem t p w ∨ (p = path.toList.drop i ∧ w = v) := by
  fun_induction Trie.insert i path hi v t generalizing n with
  | case1 t _ =>
    have hd : path.toList.drop path.size = [] := by simp
    rw [hd, validPath_nil_iff] at hv
    subst hv
    rw [hd]
    obtain ⟨vs, rfl, -⟩ := Trie.wf_zero_iff.1 ht
    refine ⟨Trie.wf_zero_iff.2 ⟨_, rfl, by simp⟩, fun p w => ?_⟩
    simp only [Trie.nodeValues, mem_leaf_iff, Array.mem_push]
    grind
  | case2 i _ t hsz ih =>
    rw [List.drop_eq_getElem_cons (by simp; omega)] at hv ⊢
    replace hv := validPath_cons_iff.1 hv
    obtain ⟨m, rfl, hv⟩ := hv
    simp only [Array.getElem_toList] at hv ⊢
    obtain ⟨-, hs, hc⟩ := ht.succ
    refine Array.binInsertM_id_induct (P := fun cs => (Trie.mkNode cs).WF (m + 1) ∧
        ∀ p w, Mem (Trie.mkNode cs) p w ↔ Mem t p w ∨ (p = path[i] :: path.toList.drop (i + 1) ∧ w = v))
      (fun a b h1 h2 => Key.lt_asymm (by simpa using h1) (by simpa using h2)) ?_ ?_
    · rintro j hj ⟨k, c⟩ hjx h1 h2
      dsimp only [Id.run]
      have hk : k = path[i] :=
        Key.eq_of_not_lt (by simpa [Key.lt_iff] using h1) (by simpa [Key.lt_iff] using h2)
      subst hk
      have hcj : t.nodeChildren[j].fst = path[i] := by rw [hjx]
      have hcm : (path[i], c) ∈ t.nodeChildren := hjx ▸ Array.getElem_mem hj
      obtain ⟨ihw, ihm⟩ := ih c (hc _ hcm) hv
      have hc' : ∀ kc ∈ t.nodeChildren.set j (path[i], Trie.insert (i + 1) path (by omega) v c),
          kc.snd.WF (m + kc.fst.arity) := by
        rintro ⟨k', c'⟩ hkc
        rcases (hs.mem_set_iff hj hcj).1 hkc with ⟨rfl, rfl⟩ | ⟨hmem, -⟩
        · exact ihw
        · exact hc _ hmem
      refine ⟨Trie.WF.mkNode (by simp; omega) (hs.set hj (by simp [hcj])) hc', fun p w => ?_⟩
      rw [mem_mkNode_iff (fun kc hkc => ⟨_, hc' kc hkc⟩), mem_succ_iff ht]
      have huniq : ∀ c', (path[i], c') ∈ t.nodeChildren → c' = c := by
        intro c' hc'
        simpa using hs.eq_of_mem hc' hcm rfl
      simp only [hs.mem_set_iff hj hcj]
      grind only
    · intro j hj hprev hnext
      dsimp only [Id.run]
      let new := Trie.singleton (i + 1) path (by omega) v
      obtain ⟨hnw, hnm⟩ := singleton_spec (v := v) (hi := show i + 1 ≤ path.size by omega) hv
      have hc' : ∀ kc ∈ t.nodeChildren.insertIdx j (path[i], new), kc.snd.WF (m + kc.fst.arity) := by
        intro kc hkc
        rcases Array.mem_insertIdx.1 hkc with rfl | hmem
        · exact hnw
        · exact hc _ hmem
      refine ⟨Trie.WF.mkNode (by simp) (hs.insertIdx hj (by simpa using hprev) (by simpa using hnext)) hc',
        fun p w => ?_⟩
      rw [mem_mkNode_iff (fun kc hkc => ⟨_, hc' kc hkc⟩), mem_succ_iff ht]
      simp only [Array.mem_insertIdx, Prod.mk.injEq]
      grind only

end

section
variable {α : Type}

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
  simp only [UnifyMany, Array.size_push, Nat.add_right_cancel_iff]
  by_cases hs : es.size = qs.size
  · simp +contextual [hs, Nat.forall_lt_succ_right', Array.getElem_push]
  · grind only [Array.size_push]

theorem Spec.unifyMany_empty_right : UnifyMany es #[] ↔ es = #[] := by
  constructor
  · intro h
    exact Array.eq_empty_of_size_eq_zero h.size_eq
  · rintro rfl; exact unifyMany_empty

/-- Split the top shape from any stack that unifies with a nonempty query stack. -/
theorem Spec.exists_unifyMany_push {R : Array ExprShape → Prop} :
    (∃ es, UnifyMany es (qs.push q) ∧ R es) ↔
      ∃ es e, UnifyMany es qs ∧ ExprShape.Unify e q ∧ R (es.push e) := by
  constructor
  · rintro ⟨es, hu, hr⟩
    obtain ⟨es, e, rfl⟩ := Array.exists_push_of_size_pos (by simp [hu.size_eq] : 0 < es.size)
    obtain ⟨hu, he⟩ := unifyMany_push.1 hu
    exact ⟨es, e, hu, he, hr⟩
  · rintro ⟨es, e, hu, he, hr⟩
    exact ⟨es.push e, unifyMany_push.2 ⟨hu, he⟩, hr⟩

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

theorem Spec.unifyMany_reverse : UnifyMany es.reverse qs.reverse ↔ UnifyMany es qs := by
  constructor
  · rintro ⟨hl, h⟩
    simp only [Array.size_reverse] at hl
    refine ⟨hl, fun i hi => ?_⟩
    have := h (es.size - 1 - i) (by simp; omega)
    simp only [Array.getElem_reverse] at this
    grind
  · rintro ⟨hl, h⟩
    refine ⟨by simp [hl], fun i hi => ?_⟩
    simp only [Array.size_reverse] at hi
    simp only [Array.getElem_reverse]
    have := h (es.size - 1 - i) (by omega)
    simpa [hl] using this

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
    | const h_len h => exact .inr ⟨by simp [ExprShape.getKeyArgs, h_len], unifyMany_reverse.2 ⟨h_len, h⟩⟩
    | fvar h_len h => exact .inr ⟨by simp [ExprShape.getKeyArgs, h_len], unifyMany_reverse.2 ⟨h_len, h⟩⟩
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
      case const.const =>
        obtain ⟨rfl, -⟩ := hk
        have := unifyMany_reverse.1 hargs
        exact .const this.1 this.2
      case fvar.fvar =>
        obtain ⟨rfl, -⟩ := hk
        have := unifyMany_reverse.1 hargs
        exact .fvar this.1 this.2
      case arrow.arrow =>
        simp only [ExprShape.getKeyArgs] at hargs
        exact .arrow ((unifyMany_push (es := #[]) (qs := #[])).1 hargs).2
      case other.other => exact .other
      case star.star => exact .star_left

/-!
## Unification-based lookup
-/

theorem Spec.mem_foldl_iff {β : Type} {cs : Array β} {f : Array α → β → Array α} {R : β → Prop}
    (h : ∀ acc x, x ∈ cs → (w ∈ f acc x ↔ w ∈ acc ∨ R x)) (acc : Array α) :
    w ∈ cs.foldl f acc ↔ w ∈ acc ∨ ∃ x ∈ cs, R x := by
  rcases cs with ⟨l⟩
  simp only [List.foldl_toArray', List.mem_toArray] at h ⊢
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp]
    rw [ih _ (fun acc y hy => h acc y (by simp [hy])), h acc x (by simp)]
    grind

theorem Array.extract_zero_append_extract {es : Array α} (h : n ≤ es.size) :
    es.extract 0 n ++ es.extract n es.size = es := by
  rw [Array.extract_append_extract, Nat.zero_min, Nat.max_eq_right h, Array.extract_size]

/-- Skipping one term means following some child and then skipping that child's arguments. -/
theorem Spec.skip_iff {t : Trie α} {X : List Key} :
    (∃ ds : List ExprShape, ds.length = s + 1 ∧ Mem t (F ds ++ X) w) ↔
      ∃ kc ∈ t.nodeChildren, ∃ ds : List ExprShape, ds.length = s + kc.fst.arity ∧ Mem kc.snd (F ds ++ X) w := by
  rw [exists_cons_iff (R := (Mem t · w))]
  simp only [mem_cons_iff]
  constructor
  · rintro ⟨k, ds, hl, c, hc, hm⟩; exact ⟨(k, c), hc, ds, hl, hm⟩
  · rintro ⟨⟨k, c⟩, hc, ds, hl, hm⟩; exact ⟨k, ds, hl, c, hc, hm⟩

/-- Matching a non-wildcard query against a trie: follow the wildcard child or the query's own key. -/
theorem Spec.unify_top_iff {qs : Array ExprShape} {t : Trie α} (hq : q ≠ .star)
    (hs : KeysSorted t.nodeChildren) :
    (∃ es, UnifyMany es (qs.push q) ∧ Mem t (P es) w) ↔
      (∃ c, t.nodeChildren[0]? = some (.star, c) ∧ ∃ es, UnifyMany es qs ∧ Mem c (P es) w) ∨
      (∃ c, (q.getKeyArgs.fst, c) ∈ t.nodeChildren ∧
        ∃ es, UnifyMany es (qs ++ q.getKeyArgs.snd) ∧ Mem c (P es) w) := by
  rw [exists_unifyMany_push]
  constructor
  · rintro ⟨es', e, hu', he, hm⟩
    rw [P_push, ExprShape.getKeyPath_eq, List.cons_append, mem_cons_iff] at hm
    obtain ⟨c, hc, hm⟩ := hm
    rcases (unify_iff_of_ne_star hq).1 he with rfl | ⟨hk, ha⟩
    · exact .inl ⟨c, hs.getElem?_zero hc, es', hu', by simpa [ExprShape.getKeyArgs, P, F] using hm⟩
    · refine .inr ⟨c, hk ▸ hc, es' ++ e.getKeyArgs.snd, (unifyMany_append hu'.size_eq).2 ⟨hu', ha⟩, ?_⟩
      rwa [P_append]
  · rintro (⟨c, hc, es, hu, hm⟩ | ⟨c, hc, es, hu, hm⟩)
    · refine ⟨es, .star, hu, .star_left, ?_⟩
      rw [P_push, show ExprShape.star.getKeyPath.toList = [.star] by simp [ExprShape.getKeyPath]]
      exact mem_cons_iff.2 ⟨c, Array.mem_of_getElem? hc, hm⟩
    · have hsz := hu.size_eq
      simp only [Array.size_append] at hsz
      rw [← Array.extract_zero_append_extract (es := es) (n := qs.size) (by omega)] at hu hm
      obtain ⟨hu₁, hu₂⟩ := (unifyMany_append (by simp; omega)).1 hu
      have hargs : (es.extract qs.size es.size).size = q.getKeyArgs.fst.arity := by
        simp [← ExprShape.size_getKeyArgs_snd]; omega
      refine ⟨es.extract 0 qs.size, toShape q.getKeyArgs.fst (es.extract qs.size es.size),
        hu₁, (unify_iff_of_ne_star hq).2 (.inr ?_), ?_⟩
      · rw [getKeyArgs_toShape hargs]; exact ⟨rfl, hu₂⟩
      · rw [P_push, getKeyPath_toShape hargs, List.cons_append, mem_cons_iff]
        exact ⟨c, hc, by rwa [P_append] at hm⟩

/-- The wildcard child's contribution to {name}`Trie.getUnify`'s accumulator. -/
theorem Spec.mem_starAccum_iff {cs : Array (Key × Trie α)} {qs : Array ExprShape} {acc0 : Array α}
    (hc : ∀ kc ∈ cs, kc.snd.WF (qs.size + kc.fst.arity))
    (ih : ∀ c, cs[0]? = some (.star, c) → c.WF (0 + qs.size) →
      (w ∈ Trie.getUnify 0 qs acc0 c ↔
        w ∈ acc0 ∨ ∃ es, UnifyMany es qs ∧ ∃ ds, ds.length = 0 ∧ Mem c (F ds ++ P es) w)) :
    w ∈ (match _hs : cs[0]? with
      | .some (.star, t) => Trie.getUnify 0 qs acc0 t
      | _ => acc0) ↔
      w ∈ acc0 ∨ ∃ c, cs[0]? = some (.star, c) ∧ ∃ es, UnifyMany es qs ∧ Mem c (P es) w := by
  split
  · rename_i c hs0
    rw [ih c hs0 (by simpa [Key.arity] using hc _ (Array.mem_of_getElem? hs0))]
    simp [hs0, F_nil]
  · grind only

/--
{name}`Trie.getUnify` on a well-formed trie returns the accumulator plus every value stored under
{lit}`skip` arbitrary terms followed by terms unifying with the query stack, top first.
-/
theorem Spec.mem_getUnify_iff {t : Trie α} (ht : t.WF (skip + qs.size)) :
    w ∈ t.getUnify skip qs accum ↔ w ∈ accum ∨
      ∃ es, UnifyMany es qs ∧ ∃ ds, ds.length = skip ∧ Mem t (F ds ++ P es) w := by
  fun_induction Trie.getUnify skip qs accum t with
  | case1 todo accum t skip ih =>
    have ht' : t.WF (skip + todo.size + 1) := by rwa [show skip + todo.size + 1 = skip + 1 + todo.size by omega]
    rw [mem_foldl_iff (R := fun x => ∃ es, UnifyMany es todo ∧
        ∃ ds, ds.length = skip + x.1.fst.arity ∧ Mem x.1.snd (F ds ++ P es) w)
      (fun acc ⟨kc, hkc⟩ _ => ih acc kc hkc (by
        have := ht'.succ.2.2 kc hkc
        rwa [show skip + todo.size + kc.fst.arity = skip + kc.fst.arity + todo.size by omega] at this))]
    apply or_congr_right
    constructor
    · rintro ⟨⟨kc, hkc⟩, -, es, hu, hm⟩
      exact ⟨es, hu, skip_iff.2 ⟨kc, hkc, hm⟩⟩
    · rintro ⟨es, hu, hm⟩
      obtain ⟨kc, hkc, hm⟩ := skip_iff.1 hm
      exact ⟨⟨kc, hkc⟩, by simp, es, hu, hm⟩
  | case2 todo accum t hb =>
    obtain rfl : todo = #[] := by simpa using hb
    simp only [Array.mem_append, unifyMany_empty_right, exists_eq_left, List.length_eq_zero_iff,
      F_nil, List.nil_append, P_empty, mem_nil_iff]
  | case3 todo accum t keyArgs hb hk ih =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    obtain rfl : q = .star := ExprShape.getKeyArgs_fst_eq_star.1 (beq_iff_eq.1 hk)
    simp only [Array.pop_push] at ih ⊢
    rw [ih (by simpa [Nat.add_comm] using ht)]
    simp only [List.length_eq_zero_iff, exists_eq_left, F_nil, List.nil_append]
    rw [exists_unifyMany_push]
    simp only [List.length_eq_one_iff, ← exists_and_right]
    simp only [exists_comm (α := List ExprShape) (β := ExprShape), exists_eq_left,
      F_cons, F_nil, List.append_nil, P_push, ExprShape.Unify.star_right, true_and, exists_and_left]
  | case4 todo acc0 t keyArgs hb hk cs acc k' c hf ih3 ih2 ih1 =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    have hqs : q ≠ .star := fun h => hk (by simp [h, ExprShape.getKeyArgs])
    have ht' : t.WF (qs'.size + 1) := by simpa using ht
    obtain ⟨-, hs, hc⟩ := ht'.succ
    obtain ⟨hmem, rfl⟩ := Trie.binSearch_key hf
    have hwf : c.WF (0 + ((qs'.push q).pop ++ q.getKeyArgs.snd).size) := by
      have := hc _ hmem; simpa [ExprShape.size_getKeyArgs_snd] using this
    rw [ih1 hwf]
    simp only [acc, cs]
    rw [mem_starAccum_iff (qs := (qs'.push q).pop) (by simpa using hc) ih2]
    simp only [Array.pop_push, List.length_eq_zero_iff, exists_eq_left, F_nil, List.nil_append]
    rw [unify_top_iff hqs hs]
    have huniq : ∀ c', (q.getKeyArgs.fst, c') ∈ t.nodeChildren ↔ c' = c := fun c' =>
      ⟨fun h => by simpa using hs.eq_of_mem h hmem rfl, fun h => h ▸ hmem⟩
    simp only [huniq, exists_eq_left, or_assoc]
  | case5 todo acc0 t keyArgs hb hk cs acc hf ih1 =>
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨qs', rfl⟩ := Array.back?_eq_some_iff.1 hq
    have hqs : q ≠ .star := fun h => hk (by simp [h, ExprShape.getKeyArgs])
    have ht' : t.WF (qs'.size + 1) := by simpa using ht
    obtain ⟨-, hs, hc⟩ := ht'.succ
    simp only [acc, cs]
    rw [mem_starAccum_iff (qs := (qs'.push q).pop) (by simpa using hc) ih1]
    simp only [Array.pop_push, List.length_eq_zero_iff, exists_eq_left, F_nil, List.nil_append]
    rw [unify_top_iff hqs hs]
    have hnone : ∀ c', (q.getKeyArgs.fst, c') ∉ t.nodeChildren := fun c' h => by
      have := hs.binSearch_eq (d := Trie.empty) h
      simp only [cs] at hf
      rw [this] at hf
      simp at hf
    simp [hnone, cs]

/-!
## Whole tries
-/

theorem Spec.foldl_insert_spec {L : KVMap α} {t : Trie α} (ht : t.WF 1) :
    (L.foldl (fun x ⟨k, v⟩ => Trie.insert 0 k.getKeyPath (Nat.zero_le _) v x) t).WF 1 ∧
      ∀ p w, Mem (L.foldl (fun x ⟨k, v⟩ => Trie.insert 0 k.getKeyPath (Nat.zero_le _) v x) t) p w ↔
        Mem t p w ∨ ∃ kv ∈ L, p = kv.key.getKeyPath.toList ∧ w = kv.value := by
  induction L generalizing t with
  | nil => exact ⟨ht, by simp⟩
  | cons kv L ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.foldl_cons]
    obtain ⟨hw, hm⟩ := insert_spec (v := v) (hi := Nat.zero_le _) ht (by simpa using validPath_getKeyPath k)
    obtain ⟨hw', hm'⟩ := ih hw
    refine ⟨hw', fun p w => ?_⟩
    rw [hm', hm]
    simp only [List.drop_zero, List.mem_cons, exists_eq_or_imp]
    grind

theorem Trie.getUnify_of_empty {t : Trie α} (hc : t.nodeChildren = #[]) (hv : t.nodeValues = #[]) :
    t.getUnify skip qs accum = accum := by
  fun_induction Trie.getUnify skip qs accum t with
  | case1 todo accum t skip ih =>
    rw [Array.eq_empty_of_size_eq_zero (by simp [hc] : t.nodeChildren.attach.size = 0)]; rfl
  | case2 => simp [hv]
  | case3 todo accum t keyArgs hb hk ih => exact ih hc hv
  | case4 todo acc0 t keyArgs hb hk cs acc k' c hf ih3 ih2 ih1 =>
    exact absurd (Trie.binSearch_key hf).1 (by simp [cs, hc])
  | case5 todo acc0 t keyArgs hb hk cs acc hf ih1 =>
    simp only [acc, cs]
    split
    · rename_i hs0; simp [hc] at hs0
    · rfl

theorem Spec.mem_getUnify_single {t : Trie α} (ht : t.WF 1) :
    w ∈ t.getUnify 0 #[query] #[] ↔ ∃ e, ExprShape.Unify e query ∧ Mem t e.getKeyPath.toList w := by
  rw [mem_getUnify_iff (by simpa using ht)]
  simp only [Array.not_mem_empty, false_or, List.length_eq_zero_iff, exists_eq_left, F_nil, List.nil_append]
  rw [show #[query] = (#[] : Array ExprShape).push query from rfl, exists_unifyMany_push]
  simp only [unifyMany_empty_right, exists_and_left, exists_eq_left, P_push, P_empty, List.append_nil]

/-- Everything a trie stores, as a list of key paths and values. -/
def Spec.entries (t : Trie α) : List (List Key × α) :=
  t.nodeValues.toList.map (([], ·)) ++
    t.nodeChildren.attach.toList.flatMap fun ⟨kc, _⟩ => (entries kc.snd).map fun pw => (kc.fst :: pw.1, pw.2)
termination_by t.measure
decreasing_by exact Trie.measure_lt_of_mem_nodeChildren ‹_›

theorem Spec.mem_entries {t : Trie α} : (p, w) ∈ entries t ↔ Mem t p w := by
  fun_induction entries t generalizing p w with
  | case1 t ih =>
    cases p <;> simp [mem_nil_iff, mem_cons_iff, List.mem_map, Prod.exists, Subtype.exists, and_assoc]
    grind only

end

theorem Spec.toTrie_spec {kvs : KVMap α} (h : kvs ≠ []) :
    kvs.toTrie.WF 1 ∧
      ∀ p w, Mem kvs.toTrie p w ↔ ∃ kv ∈ kvs, p = kv.key.getKeyPath.toList ∧ w = kv.value := by
  rcases kvs with _ | ⟨⟨k, v⟩, L⟩
  · exact absurd rfl h
  · have h0 : (Trie.suffix k.getKeyPath 0 k.getKeyPath_size_pos v : Trie α).WF 1 :=
      Trie.wf_suffix_iff.2 (by simpa using validPath_getKeyPath k)
    obtain ⟨hw, hm⟩ := foldl_insert_spec (L := L) h0
    refine ⟨hw, fun p w => ?_⟩
    rw [KVMap.toTrie, hm, mem_suffix_iff]
    simp [List.mem_cons, exists_eq_or_imp]

/-!
# Correctness

The "represents" property is weaker than the "deconstruct" property in other developments, because
suffixes mean there's not a unique way of representing a sequence of key/value pairs as a trie.
-/

/-! Repeated insertion produces well-formed tries. -/
theorem Trie.WF.construct {kvMap : KVMap α} : kvMap = [] ∨ kvMap.toTrie.WF 1 :=
  (Classical.em _).imp_right fun h => (Spec.toTrie_spec h).1

/-! A well-formed trie can be decomposed into key/value mappings. -/
theorem Trie.WF.represent {t : Trie α} : t.WF 1 →
  ∃ kvs : KVMap α, ∀ query v, v ∈ t.getUnify 0 #[query] #[] ↔ v ∈ kvs.getUnify query := by
  intro ht
  classical
  let decode (p : List Key) : ExprShape :=
    if h : ∃ e : ExprShape, e.getKeyPath.toList = p then h.choose else .other
  have hdec : ∀ e : ExprShape, decode e.getKeyPath.toList = e := fun e => by
    have h : ∃ e' : ExprShape, e'.getKeyPath.toList = e.getKeyPath.toList := ⟨e, rfl⟩
    simp only [decode, h, ↓reduceDIte]
    exact ExprShape.getKeyPath_inj h.choose_spec
  refine ⟨(Spec.entries t).map fun pw => ⟨decode pw.1, pw.2⟩, fun query v => ?_⟩
  rw [Spec.mem_getUnify_single ht]
  simp only [KVMap.getUnify, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, hm⟩
    exact ⟨⟨e, v⟩, ⟨⟨(e.getKeyPath.toList, v), Spec.mem_entries.2 hm, by simp [hdec]⟩, by simpa using he⟩, rfl⟩
  · rintro ⟨kv, ⟨⟨⟨p, w⟩, hpw, rfl⟩, hu⟩, rfl⟩
    have hm := Spec.mem_entries.1 hpw
    obtain ⟨e, rfl⟩ := Spec.exists_getKeyPath (hm.validPath ht)
    exact ⟨e, by simpa [hdec] using hu, hm⟩

/-! The key-value map view and {name}`Trie.getUnify` agree on queries. -/
theorem Trie.mem_getUnify_toTrie {kvMap : KVMap α} :
  v ∈ kvMap.toTrie.getUnify 0 #[query] #[] ↔ v ∈ kvMap.getUnify query := by
  by_cases h : kvMap = []
  · subst h
    rw [KVMap.toTrie, Trie.getUnify_of_empty rfl rfl]
    simp [KVMap.getUnify]
  · obtain ⟨hw, hm⟩ := Spec.toTrie_spec h
    rw [Spec.mem_getUnify_single hw]
    simp only [hm, KVMap.getUnify, List.mem_map, List.mem_filter, decide_eq_true_eq]
    grind only [ExprShape.getKeyPath_inj]
