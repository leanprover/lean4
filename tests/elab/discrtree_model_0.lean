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
    /- `e1 → e2` -/
  | arrow (domain : ExprShape) (range : ExprShape)
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
  | arrow : Unify domain domain' → Unify range range' → Unify (.arrow domain range) (.arrow domain' range')
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
  | .arrow domain range => Ground domain ∧ Ground range
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
  | .const n args => ⟨.const n args.size, args⟩
  | .fvar x args => ⟨.fvar x args.size, args⟩
  | .arrow e1 e2 => ⟨.arrow, #[e2, e1]⟩
  | .star => ⟨.star, #[]⟩
  | .other => ⟨.other, #[]⟩

inductive Trie (α : Type) : Type where
  | node (vs : Array α) (cs : Array (Key × Trie α))

def Trie.empty : Trie α := Trie.node #[] #[]

/-!
## Vibe-Coded Termination Lemmas
-/

noncomputable def ExprShape.argsSize (args : Array ExprShape) : Nat := (args.map sizeOf).sum

theorem sum_sizeOf_lt_sizeOf {α} [SizeOf α] (xs : List α) :
    (xs.map sizeOf).sum < sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.cons.sizeOf_spec]; omega

theorem ExprShape.argsSize_lt (e : ExprShape) :
    argsSize e.getKeyArgs.snd < sizeOf e := by
  cases e <;> simp [getKeyArgs, argsSize]
  all_goals try omega
  case const name args =>
    cases args with | mk xs =>
      have h := sum_sizeOf_lt_sizeOf xs
      simpa using Nat.lt_trans h (by simp +arith : sizeOf xs < 1 + sizeOf name + sizeOf xs.toArray)
  case fvar id args =>
    cases args with | mk xs =>
      have h := sum_sizeOf_lt_sizeOf xs
      simpa using Nat.lt_trans h (by simp +arith : sizeOf xs < 1 + sizeOf id + sizeOf xs.toArray)

theorem ExprShape.argsSize_pop_back {args : Array ExprShape} (h : 0 < args.size) :
    argsSize args = argsSize args.pop + sizeOf (args.back h) := by
  obtain ⟨xs, e, rfl⟩ := Array.exists_push_of_size_pos h
  simp [argsSize, Array.back]

theorem ExprShape.argsSize_append (xs ys : Array ExprShape) :
    argsSize (xs ++ ys) = argsSize xs + argsSize ys := by
  simp [argsSize, Array.sum_append]

/-- Replacing the top of the stack with its arguments shrinks the stack. -/
theorem ExprShape.argsSize_pop_append_lt {args : Array ExprShape} (h : 0 < args.size) :
    argsSize (args.pop ++ (args.back h).getKeyArgs.snd) < argsSize args := by
  have := argsSize_lt (args.back h)
  have := argsSize_pop_back h
  rw [argsSize_append]
  omega

/-- A child trie counts as a subtree for termination purposes. -/
theorem Trie.sizeOf_lt_of_mem {α p vs} {cs : Array (Key × Trie α)} (h : p ∈ cs) : sizeOf p.snd < sizeOf (Trie.node vs cs) := by
  have := Array.sizeOf_lt_of_mem h
  grind only [= Prod.mk.sizeOf_spec, = node.sizeOf_spec]

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

theorem Array.mem_of_binSearch_eq_some {as : Array α} {k : α} {lt : α → α → Bool} {lo hi : Nat} {a : α}
    (hs : as.binSearch k lt lo hi = some a) : a ∈ as ∧ lt a k = false ∧ lt k a = false := by
  unfold Array.binSearch at hs
  dsimp only at hs
  repeat' split at hs
  all_goals first | contradiction | exact Array.binSearchAux_id_eq_some hs

/-!
## Trie Operations
-/

def Trie.singleton (args : Array ExprShape) (v : α) : Trie α :=
  if h : args.size = 0 then
    .node #[v] #[]
  else
    let keyArgs := args.back.getKeyArgs
    .node #[] #[(keyArgs.fst, singleton (args.pop ++ keyArgs.snd) v)]
termination_by ExprShape.argsSize args
decreasing_by exact ExprShape.argsSize_pop_append_lt (by omega)

def Trie.insert (args : Array ExprShape) (v : α) : Trie α → Trie α
  | .node vs cs =>
    if h : args.size = 0 then
      .node (vs.push v) cs
    else
      let keyArgs := args.back.getKeyArgs
      .node vs <| Id.run $ cs.binInsertM (·.fst < ·.fst)
        (fun (_, c) => (keyArgs.fst, insert (args.pop ++ keyArgs.snd) v c))
        (fun _ => (keyArgs.fst, singleton (args.pop ++ keyArgs.snd) v))
        (keyArgs.fst, .empty)
termination_by ExprShape.argsSize args
decreasing_by exact ExprShape.argsSize_pop_append_lt (by omega)

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
  | .arrow => 2 -- n.b. this matches Sym usage, for regular discrimination tree arrows arrow has arity 1
  | .star => 0
  | .other => 0

def Trie.getUnify {α} (skip : Nat) (todo : Array ExprShape) (accum : Array α) : Trie α → Array α
  | .node vs cs =>
    match h_skip : skip with
    | skip+1 =>
      cs.foldl (init := accum) fun accum c => getUnify (skip + c.fst.arity) todo accum c.snd
    | 0 =>
      if h : todo.size = 0 then
        accum ++ vs
      else
        let keyArgs := todo.back (by omega) |>.getKeyArgs
        let todo := todo.pop
        if keyArgs.fst == .star then
          -- Unification only case; skip
          cs.foldl (init := accum) fun accum c => getUnify (skip + c.fst.arity) todo accum c.snd
        else
          let accum :=
            match h_star : cs[0]? with
            | .some (.star, t) => getUnify 0 todo accum t
            | _ => accum

          match h_find : cs.binSearch (keyArgs.fst, Trie.empty) (·.1 < ·.1) with
          | .none => accum
          | .some c => getUnify 0 (todo ++ keyArgs.snd) accum c.snd

termination_by t => sizeOf t
decreasing_by all_goals first
  | exact Trie.sizeOf_lt_of_mem ‹_ ∈ cs›
  | exact Trie.sizeOf_lt_of_mem (Array.mem_of_getElem? h_star)
  | exact Trie.sizeOf_lt_of_mem (Array.mem_of_binSearch_eq_some h_find).1

/-!
## Well-formed Tries
-/

/--
A discrimination tree is a map from expression shapes to values, but as the arity discussion above
shows, a sub-trie might represent map from shapes to (a map from shapes to (... (a map from shapes
to values))). Within each level, the children are stored in key-sorted order, so we can traverse
the tree with binary search.

This definition of well-formed tries captures how deep we are in that iteration: given
{given (type := "Trie α")}`t`,
{lit}`t.isWf 1` means {name}`t` is a map from expression shapes to values,
{lit}`t.isWf 0` means {name}`t` is a leaf node containing only values, and in general{given -show (type := "Nat")}`n`
{lit}`t.isWf (n+1)` means {name}`t` is a map from expression shapes to well formed tries that map
{name}`n` expressions to values.
-/
def Trie.WF {α} : Nat → Trie α → Prop
  | 0, .node vs cs => vs.size > 0 ∧ cs.size = 0
  | n+1, .node vs cs => vs.size = 0 ∧ cs.size > 0
      ∧ cs.toList.Pairwise (·.fst < ·.fst)
      ∧ ∀ c, ∀ _ : c ∈ cs, WF (n + c.fst.arity) c.snd
termination_by _ t => sizeOf t
decreasing_by exact Trie.sizeOf_lt_of_mem ‹c ∈ cs›

/-!
# Vibe Coded Correctness Lemmas
-/

/-!
## Basic facts
-/

deriving instance DecidableEq for Lean.Literal
deriving instance DecidableEq for Lean.FVarId
deriving instance DecidableEq for Key

theorem ExprShape.sizeOf_pos (e : ExprShape) : 0 < sizeOf e := by
  cases e <;> simp +arith

theorem Key.beq_star_iff {k : Key} : (k == .star) = true ↔ k = .star := by
  cases k <;> simp <;> rfl

/-- Unification is symmetric. -/
theorem ExprShape.Unify.symm : Unify a b → Unify b a
  | .star_left => .star_right
  | .star_right => .star_left
  | .lit => .lit
  | .const h_len h => .const h_len.symm fun i hi => (h i (h_len ▸ hi)).symm
  | .fvar h_len h => .fvar h_len.symm fun i hi => (h i (h_len ▸ hi)).symm
  | .arrow hd hr => .arrow hd.symm hr.symm
  | .other => .other

/-- Returns the values stored at the current trie node. -/
def Trie.nodeValues : Trie α → Array α
  | .node vs _ => vs

/-!
## Specification of Trie Lookup

A recursive specification of lookup, following Chapter 6 of Graf's "Term Indexing." The stack-based
{name}`Trie.getUnify` is proved equal to it below.
-/

/-- Definition 6.1.2 from "Term Indexing" (p. 129-130) -/
def Trie.skip {α} : (m : Nat) → (t : Trie α) → Array (Trie α)
  | 0, t => #[t]
  | m+1, ⟨_, cs⟩ => cs.flatMap fun c => skip (m + c.fst.arity) c.snd
termination_by _ t => sizeOf t
decreasing_by exact Trie.sizeOf_lt_of_mem ‹_ ∈ cs›

mutual
def Trie.lookup (e : ExprShape) : (t : Trie α) → Array (Trie α)
  | .node _ cs =>
    let keyArgs := e.getKeyArgs
    if keyArgs.fst == .star then
      cs.flatMap fun c => Trie.skip c.fst.arity c.snd
    else
      let findWildcard :=
        match cs[0]? with
        | some (.star, c) => #[c]
        | _ => #[]
      let findExact :=
        match cs.binSearch (keyArgs.fst, Trie.empty) (·.fst < ·.fst) with
        | .none => #[]
        | .some c => Trie.lookupMany keyArgs.snd c.snd
      findWildcard ++ findExact
termination_by (sizeOf e, 0)
decreasing_by exact Prod.Lex.left _ _ (ExprShape.argsSize_lt e)

def Trie.lookupMany (args : Array ExprShape) (t : Trie α) : Array (Trie α) :=
  if h : args.size = 0 then
    #[t]
  else
    (Trie.lookup (args.back (by omega)) t).flatMap (Trie.lookupMany args.pop)
termination_by (ExprShape.argsSize args, 1)
decreasing_by all_goals grind only [ExprShape.argsSize_pop_back, = Prod.lex_def, = Array.size_pop, !ExprShape.sizeOf_pos]
end

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
    have := h₁.2 (by simp [FVarId.beq_eq_name_beq]); have := h₂.2 (by simp [FVarId.beq_eq_name_beq])
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
## Semantics

A trie denotes a set of (stack of shapes, value) pairs: the stacks whose keys, read in order, spell
a path from the root to a node holding the value.
-/

/-- Pointwise {name}`ExprShape.Unify` on stacks of shapes. -/
def ExprShape.UnifyMany (qs es : Array ExprShape) : Prop :=
  ∃ h : qs.size = es.size, ∀ i, ∀ hi : i < qs.size, Unify qs[i] es[i]

theorem ExprShape.unifyMany_empty : UnifyMany #[] #[] := ⟨rfl, fun _ h => by simp at h⟩

theorem ExprShape.UnifyMany.size_eq (h : UnifyMany qs es) : qs.size = es.size := h.1

theorem ExprShape.unifyMany_push :
    UnifyMany (qs.push q) (es.push e) ↔ UnifyMany qs es ∧ Unify q e := by
  constructor
  · rintro ⟨h_len, h⟩
    simp only [Array.size_push, Nat.add_right_cancel_iff] at h_len
    refine ⟨⟨h_len, fun i hi => ?_⟩, ?_⟩
    · have := h i (by simp; omega)
      simpa [Array.getElem_push, hi, h_len ▸ hi] using this
    · have := h qs.size (by simp)
      simpa [Array.getElem_push, h_len] using this
  · rintro ⟨⟨h_len, h⟩, hq⟩
    refine ⟨by simp [h_len], fun i hi => ?_⟩
    simp only [Array.size_push] at hi
    rw [Array.getElem_push, Array.getElem_push]
    split
    · grind
    · grind

/-- A shape is a wildcard exactly when its key is. -/
theorem ExprShape.getKeyArgs_fst_eq_star {e : ExprShape} : e.getKeyArgs.fst = .star ↔ e = .star := by
  cases e <;> simp [getKeyArgs]

theorem ExprShape.getKeyArgs_inj {e e' : ExprShape} (h : e.getKeyArgs = e'.getKeyArgs) : e = e' := by
  cases e <;> cases e' <;> simp_all [getKeyArgs]

/--
Unification is checked one key at a time: either side is a wildcard, or the keys agree and the
arguments unify pointwise.
-/
theorem ExprShape.unify_iff_getKeyArgs {q e : ExprShape} :
    Unify q e ↔ q = .star ∨ e = .star ∨
      (q.getKeyArgs.fst = e.getKeyArgs.fst ∧ UnifyMany q.getKeyArgs.snd e.getKeyArgs.snd) := by
  constructor
  · intro h
    cases h with
    | star_left => exact .inl rfl
    | star_right => exact .inr (.inl rfl)
    | lit => exact .inr (.inr ⟨rfl, unifyMany_empty⟩)
    | const h_len h => exact .inr (.inr ⟨by simp [getKeyArgs, h_len], h_len, h⟩)
    | fvar h_len h => exact .inr (.inr ⟨by simp [getKeyArgs, h_len], h_len, h⟩)
    | arrow hd hr =>
      refine .inr (.inr ⟨rfl, ?_⟩)
      simp only [getKeyArgs]
      exact (unifyMany_push (qs := #[_]) (es := #[_])).2 ⟨(unifyMany_push (qs := #[]) (es := #[])).2 ⟨unifyMany_empty, hr⟩, hd⟩
    | other => exact .inr (.inr ⟨rfl, unifyMany_empty⟩)
  · rintro (rfl | rfl | ⟨hk, hargs⟩)
    · exact .star_left
    · exact .star_right
    · cases q <;> cases e <;> simp only [getKeyArgs, Key.const.injEq, Key.fvar.injEq, Key.lit.injEq,
        reduceCtorEq] at hk
      case lit.lit => exact hk ▸ .lit
      case const.const => obtain ⟨rfl, -⟩ := hk; exact .const hargs.1 hargs.2
      case fvar.fvar => obtain ⟨rfl, -⟩ := hk; exact .fvar hargs.1 hargs.2
      case arrow.arrow =>
        simp only [getKeyArgs] at hargs
        have ⟨h₁, h₂⟩ := (unifyMany_push (qs := #[_]) (es := #[_])).1 hargs
        exact .arrow h₂ ((unifyMany_push (qs := #[]) (es := #[])).1 h₁).2
      case other.other => exact .other
      case star.star => exact .star_left

theorem ExprShape.size_getKeyArgs_snd {e : ExprShape} : e.getKeyArgs.snd.size = e.getKeyArgs.fst.arity := by
  cases e <;> simp [getKeyArgs, Key.arity]

/-!
## Shapes from keys
-/

/-- Rebuilds a shape from its key and its arguments; inverse to {name}`ExprShape.getKeyArgs`. -/
def Key.toShape (k : Key) (args : Array ExprShape) : ExprShape :=
  match k with
  | .lit l => .lit l
  | .const n _ => .const n args
  | .fvar x _ => .fvar x args
  | .arrow => .arrow (args.getD 1 .other) (args.getD 0 .other)
  | .star => .star
  | .other => .other

theorem Key.getKeyArgs_toShape {k : Key} {args : Array ExprShape} (h : args.size = k.arity) :
    (k.toShape args).getKeyArgs = (k, args) := by
  cases k <;> simp only [Key.arity] at h <;> simp [toShape, ExprShape.getKeyArgs, h]
  all_goals try exact Array.eq_empty_of_size_eq_zero h
  grind

theorem Array.pop_push_back {xs : Array α} (h : 0 < xs.size) : xs.pop.push (xs.back h) = xs := by grind

/-!
## Paths through a trie
-/

/--
{given -show (type := "Trie α")}`t, x`
{given -show (type := "Array ExprShape")}`es`
{lean}`t.Reach es x` if consuming the stack {name}`es` from {name}`t` (following the key of the
top shape and pushing its arguments) leads to {name}`x`.
-/
inductive Trie.Reach : Trie α → Array ExprShape → Trie α → Prop where
  | refl : Reach t #[] t
  | step : (e.getKeyArgs.fst, c) ∈ cs → Reach c (es ++ e.getKeyArgs.snd) x →
      Reach (.node vs cs) (es.push e) x

/-- {given -show (type := "α")}`v` A trie contains {name}`v` at the stack {name}`es`. -/
def Trie.Contains (t : Trie α) (es : Array ExprShape) (v : α) : Prop :=
  ∃ x, t.Reach es x ∧ v ∈ x.nodeValues

theorem Trie.reach_empty_iff : Reach t #[] x ↔ x = t := by
  constructor
  · intro h
    generalize hz : (#[] : Array ExprShape) = z at h
    cases h with
    | refl => rfl
    | step => exact absurd hz.symm Array.push_ne_empty
  · rintro rfl; exact .refl

theorem Trie.reach_push_iff {vs : Array α} {cs} :
    Reach (.node vs cs) (es.push e) x ↔
      ∃ c, (e.getKeyArgs.fst, c) ∈ cs ∧ Reach c (es ++ e.getKeyArgs.snd) x := by
  constructor
  · intro h
    generalize hz : es.push e = z at h
    cases h with
    | refl => exact absurd hz Array.push_ne_empty
    | step hc hr =>
      obtain ⟨rfl, rfl⟩ := Array.push_eq_push.1 hz
      exact ⟨_, hc, hr⟩
  · rintro ⟨c, hc, hr⟩; exact .step hc hr

theorem Trie.reach_singleton_iff {vs : Array α} {cs} :
    Reach (.node vs cs) #[e] x ↔ ∃ c, (e.getKeyArgs.fst, c) ∈ cs ∧ Reach c e.getKeyArgs.snd x := by
  have := reach_push_iff (vs := vs) (cs := cs) (es := #[]) (e := e) (x := x)
  simpa using this

theorem Trie.Reach.trans (h₁ : Reach t ys y) (h₂ : Reach y xs x) : Reach t (xs ++ ys) x := by
  induction h₁ generalizing xs with
  | refl => simpa using h₂
  | step hc _ ih =>
    rw [Array.append_push]
    exact .step hc (by rw [Array.append_assoc]; exact ih h₂)

theorem Trie.Reach.split (h : Reach t zs x) : zs = xs ++ ys → ∃ y, Reach t ys y ∧ Reach y xs x := by
  induction h generalizing xs ys with
  | refl =>
    intro h
    have := congrArg Array.size h
    simp only [Array.size_empty, Array.size_append] at this
    rw [Array.eq_empty_of_size_eq_zero (by omega : xs.size = 0),
      Array.eq_empty_of_size_eq_zero (by omega : ys.size = 0)]
    exact ⟨_, .refl, .refl⟩
  | step hc hr ih =>
    intro h
    rcases Array.push_eq_append_iff.1 h with ⟨rfl, rfl⟩ | ⟨ys', rfl, rfl⟩
    · exact ⟨_, .refl, .step hc hr⟩
    · obtain ⟨y, h₁, h₂⟩ := ih (xs := xs) (ys := ys' ++ _) (by rw [Array.append_assoc])
      exact ⟨y, .step hc h₁, h₂⟩

/-- Consuming {lit}`xs ++ ys` means consuming {name}`ys` (the top of the stack) and then {name}`xs`. -/
theorem Trie.reach_append_iff : Reach t (xs ++ ys) x ↔ ∃ y, Reach t ys y ∧ Reach y xs x :=
  ⟨fun h => h.split rfl, fun ⟨_, h₁, h₂⟩ => h₁.trans h₂⟩

/-- {name}`Trie.skip` returns exactly the tries reached by consuming {name}`m` arbitrary shapes. -/
theorem Trie.mem_skip_iff {m : Nat} {t x : Trie α} :
    x ∈ skip m t ↔ ∃ es, es.size = m ∧ Reach t es x := by
  constructor
  · intro h
    fun_induction skip m t with
    | case1 t => simp only [Array.mem_singleton] at h; exact ⟨#[], rfl, h ▸ .refl⟩
    | case2 m vs cs ih =>
      simp only [Array.mem_flatMap] at h
      obtain ⟨⟨k, c⟩, hc, h⟩ := h
      obtain ⟨es, h_size, hr⟩ := ih ⟨k, c⟩ hc h
      simp only at h_size hr
      have h₁ : (es.extract 0 m).size = m := by simp; omega
      have h₂ : (es.extract m es.size).size = k.arity := by simp only [Array.size_extract, Nat.min_self]; omega
      have h_es : es.extract 0 m ++ es.extract m es.size = es := by
        rw [Array.extract_append_extract]; simp [Nat.max_eq_right (by omega : m ≤ es.size)]
      refine ⟨(es.extract 0 m).push (k.toShape (es.extract m es.size)), by simp [h₁], ?_⟩
      refine .step (c := c) ?_ ?_
      · rwa [Key.getKeyArgs_toShape h₂]
      · rwa [Key.getKeyArgs_toShape h₂, h_es]
  · rintro ⟨es, rfl, h⟩
    induction h with
    | refl => simp [skip]
    | step hc _ ih =>
      rename_i e c _ es _ _
      simp only [Array.size_push, skip, Array.mem_flatMap]
      refine ⟨_, hc, ?_⟩
      simpa [ExprShape.size_getKeyArgs_snd] using ih

/-!
## Soundness of lookup
-/

theorem Trie.binSearch_key {cs : Array (Key × Trie α)}
    (h : cs.binSearch (key, d) (·.fst < ·.fst) = some c) : c ∈ cs ∧ c.fst = key := by
  have ⟨hmem, h₁, h₂⟩ := Array.mem_of_binSearch_eq_some h
  exact ⟨hmem, Key.eq_of_not_lt (by simpa only [Key.lt_iff, Bool.decide_eq_true] using h₁)
    (by simpa only [Key.lt_iff, Bool.decide_eq_true] using h₂)⟩

mutual
/-- Every trie that {name}`Trie.lookup` returns is reached by a shape that unifies with the query. -/
theorem Trie.lookup_sound (q : ExprShape) :
    ∀ (t : Trie α), x ∈ lookup q t → ∃ e, q.Unify e ∧ Reach t #[e] x
  | .node vs cs, h => by
    rw [lookup] at h
    split at h
    · rename_i hst
      simp only [Array.mem_flatMap] at h
      obtain ⟨⟨k, c⟩, hc, h⟩ := h
      obtain ⟨es, h_size, hr⟩ := mem_skip_iff.1 h
      refine ⟨k.toShape es, ExprShape.getKeyArgs_fst_eq_star.1 (Key.beq_star_iff.1 hst) ▸ .star_left, ?_⟩
      rw [reach_singleton_iff, Key.getKeyArgs_toShape h_size]
      exact ⟨c, hc, hr⟩
    · rename_i hst
      rw [Array.mem_append] at h
      rcases h with h | h
      · split at h
        · rename_i c heq
          simp only [Array.mem_singleton] at h; subst h
          refine ⟨.star, .star_right, ?_⟩
          rw [reach_singleton_iff]
          exact ⟨_, Array.mem_of_getElem? heq, .refl⟩
        · simp at h
      · split at h
        · simp at h
        · rename_i c h_search
          have ⟨hc, hk⟩ := binSearch_key h_search
          obtain ⟨es, hu, hr⟩ := lookupMany_sound q.getKeyArgs.snd c.snd h
          have h_size : es.size = q.getKeyArgs.fst.arity := by
            rw [← hu.size_eq, ExprShape.size_getKeyArgs_snd]
          refine ⟨q.getKeyArgs.fst.toShape es, ?_, ?_⟩
          · rw [ExprShape.unify_iff_getKeyArgs, Key.getKeyArgs_toShape h_size]
            exact .inr (.inr ⟨rfl, hu⟩)
          · rw [reach_singleton_iff, Key.getKeyArgs_toShape h_size, ← hk]
            exact ⟨c.snd, hc, hr⟩
termination_by (sizeOf q, 0)
decreasing_by exact Prod.Lex.left _ _ (ExprShape.argsSize_lt q)

/-- Every trie that {name}`Trie.lookupMany` returns is reached by a stack that unifies with the query. -/
theorem Trie.lookupMany_sound (qs : Array ExprShape) (t : Trie α) (h : x ∈ lookupMany qs t) :
    ∃ es, ExprShape.UnifyMany qs es ∧ Reach t es x := by
  rw [lookupMany] at h
  split at h
  · rename_i h0
    simp only [Array.mem_singleton] at h; subst h
    rw [Array.eq_empty_of_size_eq_zero h0]
    exact ⟨#[], ExprShape.unifyMany_empty, .refl⟩
  · rename_i h0
    simp only [Array.mem_flatMap] at h
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨e, hu, hr₁⟩ := lookup_sound (qs.back (by omega)) t hy
    obtain ⟨es, hus, hr₂⟩ := lookupMany_sound qs.pop y h
    refine ⟨es.push e, ?_, ?_⟩
    · have := ExprShape.unifyMany_push.2 ⟨hus, hu⟩
      rwa [Array.pop_push_back] at this
    · rw [← Array.append_singleton]
      exact hr₁.trans hr₂
termination_by (ExprShape.argsSize qs, 1)
decreasing_by all_goals grind only [ExprShape.argsSize_pop_back, = Prod.lex_def, = Array.size_pop, !ExprShape.sizeOf_pos]
end

/-!
## Completeness of lookup on sorted tries
-/

/-- The children of a node are strictly sorted by key. -/
def Trie.KeysSorted (cs : Array (Key × Trie α)) : Prop :=
  (cs.toList.map Prod.fst).Pairwise (· < ·)

/--
Every node's children are strictly sorted by key. {name}`Trie.insert` maintains this, and
{name}`Trie.lookup` relies on it to find children with {name}`Array.binSearch` and the wildcard
child at index 0.
-/
inductive Trie.Sorted : Trie α → Prop where
  | node : KeysSorted cs → (∀ c ∈ cs, Sorted c.snd) → Sorted (.node vs cs)

theorem Trie.KeysSorted.lt {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i j : Nat}
    (hi : i < cs.size) (hj : j < cs.size) (hij : i < j) : cs[i].fst < cs[j].fst := by
  have := List.pairwise_iff_getElem.1 hs i j (by simpa using hi) (by simpa using hj) hij
  simpa using this

theorem Trie.KeysSorted.eq_of_mem {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
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
theorem Trie.KeysSorted.binSearch_eq {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    (hc : (k, c) ∈ cs) : cs.binSearch (k, d) (·.fst < ·.fst) = some (k, c) := by
  obtain ⟨y, hy⟩ := Array.binSearch_complete (lt := fun (a b : Key × Trie α) => decide (a.fst < b.fst)) (k := (k, d))
    (x := (k, c))
    (fun i j hi hj hij => by simpa using hs.lt hi hj hij)
    (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    (fun _ => ⟨rfl, rfl⟩) (by simpa using Key.lt_irrefl k) hc
  have ⟨hy_mem, hy_key⟩ := binSearch_key hy
  rw [hy, hs.eq_of_mem hy_mem hc hy_key]

/-- In a sorted node, the wildcard child, if any, comes first. -/
theorem Trie.KeysSorted.getElem?_zero {cs : Array (Key × Trie α)} (hs : KeysSorted cs)
    (hc : (.star, c) ∈ cs) : cs[0]? = some (.star, c) := by
  obtain ⟨j, hj, h_eq⟩ := Array.mem_iff_getElem.1 hc
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [Array.getElem?_eq_getElem hj, h_eq]
  · have := hs.lt (by omega) hj hj0
    rw [h_eq] at this
    exact absurd this (Key.not_lt_star _)

theorem Trie.Sorted.child {vs : Array α} {cs} (hs : Sorted (.node vs cs)) (hc : c ∈ cs) : Sorted c.snd := by
  cases hs with | node _ h => exact h c hc

theorem Trie.Sorted.keys {vs : Array α} {cs} (hs : Sorted (.node vs cs)) : KeysSorted cs := by
  cases hs with | node h _ => exact h

theorem Trie.Sorted.reach (hs : Sorted t) (h : Reach t es x) : Sorted x := by
  induction h with
  | refl => exact hs
  | step hc _ ih => exact ih (hs.child hc)

mutual
/-- On a sorted trie, {name}`Trie.lookup` returns every trie reached by a shape that unifies with the query. -/
theorem Trie.lookup_complete (q e : ExprShape) (hu : q.Unify e) :
    ∀ (t : Trie α), Sorted t → Reach t #[e] x → x ∈ lookup q t
  | .node vs cs, hs, hr => by
    obtain ⟨c, hc, hr⟩ := reach_singleton_iff.1 hr
    rw [lookup]
    split
    · simp only [Array.mem_flatMap]
      exact ⟨_, hc, mem_skip_iff.2 ⟨_, ExprShape.size_getKeyArgs_snd, hr⟩⟩
    · rename_i hst
      have hq : q ≠ .star := fun h => hst (Key.beq_star_iff.2 (ExprShape.getKeyArgs_fst_eq_star.2 h))
      rw [Array.mem_append]
      rcases ExprShape.unify_iff_getKeyArgs.1 hu with h | rfl | ⟨hk, hargs⟩
      · exact absurd h hq
      · simp only [ExprShape.getKeyArgs] at hc hr
        rw [reach_empty_iff] at hr; subst hr
        left
        rw [hs.keys.getElem?_zero hc]; simp
      · right
        rw [← hk] at hc
        rw [hs.keys.binSearch_eq hc]
        exact lookupMany_complete _ _ hargs c (hs.child hc) hr
termination_by (sizeOf q, 0)
decreasing_by exact Prod.Lex.left _ _ (ExprShape.argsSize_lt q)

/-- On a sorted trie, {name}`Trie.lookupMany` returns every trie reached by a stack that unifies with the query. -/
theorem Trie.lookupMany_complete (qs es : Array ExprShape) (hu : ExprShape.UnifyMany qs es)
    (t : Trie α) (hs : Sorted t) (hr : Reach t es x) : x ∈ lookupMany qs t := by
  rw [lookupMany]
  split
  · rename_i h0
    have : es = #[] := Array.eq_empty_of_size_eq_zero (hu.size_eq ▸ h0)
    subst this
    rw [reach_empty_iff] at hr; subst hr; simp
  · rename_i h0
    have h0' : 0 < es.size := by have := hu.size_eq; omega
    have hu' : ExprShape.UnifyMany (qs.pop.push (qs.back (by omega))) (es.pop.push (es.back h0')) := by
      rw [Array.pop_push_back, Array.pop_push_back]; exact hu
    obtain ⟨hus, hu₁⟩ := ExprShape.unifyMany_push.1 hu'
    rw [← Array.pop_push_back h0', ← Array.append_singleton, reach_append_iff] at hr
    obtain ⟨y, hr₁, hr₂⟩ := hr
    simp only [Array.mem_flatMap]
    exact ⟨y, lookup_complete _ _ hu₁ t hs hr₁, lookupMany_complete _ _ hus y (hs.reach hr₁) hr₂⟩
termination_by (ExprShape.argsSize qs, 1)
decreasing_by all_goals grind only [ExprShape.argsSize_pop_back, = Prod.lex_def, = Array.size_pop, !ExprShape.sizeOf_pos]
end

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

/-!
## Insertion preserves sortedness and adds exactly one entry
-/

theorem Trie.insert_cases {args : Array ExprShape} (h0 : 0 < args.size) (v : α) (vs : Array α)
    (cs : Array (Key × Trie α)) :
    (∃ i, ∃ hi : i < cs.size, cs[i].fst = (args.back h0).getKeyArgs.fst ∧
      insert args v (.node vs cs) = .node vs (cs.set i ((args.back h0).getKeyArgs.fst,
        insert (args.pop ++ (args.back h0).getKeyArgs.snd) v cs[i].snd))) ∨
    (∃ i, ∃ hi : i ≤ cs.size,
      insert args v (.node vs cs) = .node vs (cs.insertIdx i ((args.back h0).getKeyArgs.fst,
        singleton (args.pop ++ (args.back h0).getKeyArgs.snd) v)) ∧
      (∀ h : 0 < i, cs[i - 1].fst < (args.back h0).getKeyArgs.fst) ∧
      (∀ h : i < cs.size, (args.back h0).getKeyArgs.fst < cs[i].fst)) := by
  rw [insert]
  split
  · omega
  rcases Array.binInsertM_id_cases (as := cs) (k := ((args.back h0).getKeyArgs.fst, Trie.empty))
      (lt := fun a b => decide (a.fst < b.fst))
      (merge := fun (_, c) => ((args.back h0).getKeyArgs.fst, insert (args.pop ++ (args.back h0).getKeyArgs.snd) v c))
      (add := fun _ => ((args.back h0).getKeyArgs.fst, singleton (args.pop ++ (args.back h0).getKeyArgs.snd) v))
      (fun a b h₁ h₂ => Key.lt_asymm (by simpa using h₁) (by simpa using h₂))
    with ⟨i, hi, hlt, hgt, hr⟩ | ⟨i, hi, hr, hprev, hnext⟩
  · refine .inl ⟨i, hi, Key.eq_of_not_lt (by simpa [Key.lt_iff] using hlt) (by simpa [Key.lt_iff] using hgt), ?_⟩
    exact congrArg (Trie.node vs) hr
  · refine .inr ⟨i, hi, congrArg (Trie.node vs) hr, fun h => by simpa using hprev h,
      fun h => by simpa using hnext h⟩

theorem Array.eq_empty_or_eq_push (xs : Array α) : xs = #[] ∨ ∃ (ys : Array α) (y : α), xs = ys.push y := by
  rcases Nat.eq_zero_or_pos xs.size with h | h
  · exact .inl (Array.eq_empty_of_size_eq_zero h)
  · obtain ⟨ys, y, rfl⟩ := Array.exists_push_of_size_pos h
    exact .inr ⟨ys, y, rfl⟩

/-- A stack is determined by the stack left after consuming its top shape, plus that shape's key. -/
theorem ExprShape.push_eq_of_keyArgs {es es' : Array ExprShape} {e e' : ExprShape}
    (hk : e.getKeyArgs.fst = e'.getKeyArgs.fst)
    (h : es ++ e.getKeyArgs.snd = es' ++ e'.getKeyArgs.snd) : es.push e = es'.push e' := by
  have h_args : e.getKeyArgs.snd.size = e'.getKeyArgs.snd.size := by
    rw [size_getKeyArgs_snd, size_getKeyArgs_snd, hk]
  have h_size : es.size = es'.size := by
    have := congrArg Array.size h; simp only [Array.size_append] at this; omega
  obtain ⟨rfl, h₂⟩ := Array.append_inj h h_size
  rw [getKeyArgs_inj (Prod.ext hk h₂)]

theorem Trie.contains_empty_iff : Contains t #[] w ↔ w ∈ t.nodeValues := by
  simp [Contains, reach_empty_iff]

theorem Trie.contains_push_iff {vs : Array α} {cs} :
    Contains (.node vs cs) (es.push e) w ↔
      ∃ c, (e.getKeyArgs.fst, c) ∈ cs ∧ Contains c (es ++ e.getKeyArgs.snd) w := by
  simp only [Contains, reach_push_iff]
  exact ⟨fun ⟨x, ⟨c, hc, hr⟩, hw⟩ => ⟨c, hc, x, hr, hw⟩, fun ⟨c, hc, x, hr, hw⟩ => ⟨x, ⟨c, hc, hr⟩, hw⟩⟩

/-- A singleton trie contains exactly its one entry. -/
theorem Trie.contains_singleton (es : Array ExprShape) (v : α) (es' : Array ExprShape) (w : α) :
    Contains (singleton es v) es' w ↔ es' = es ∧ w = v := by
  rw [singleton]
  split
  · rename_i h0
    have := Array.eq_empty_of_size_eq_zero h0; subst this
    rcases Array.eq_empty_or_eq_push es' with rfl | ⟨es'', e, rfl⟩
    · simp [contains_empty_iff, Trie.nodeValues]
    · simp [contains_push_iff]
  · rename_i h0
    have h_pos : 0 < es.size := by omega
    rcases Array.eq_empty_or_eq_push es' with rfl | ⟨es'', e, rfl⟩
    · simp only [contains_empty_iff, Trie.nodeValues, List.mem_toArray, List.not_mem_nil, false_iff, not_and]
      intro h; simp [← h] at h0
    · rw [contains_push_iff]
      simp only [Array.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨c, ⟨hk, rfl⟩, hc⟩
        have := (contains_singleton _ v _ w).1 hc
        exact ⟨by rw [ExprShape.push_eq_of_keyArgs hk this.1, Array.pop_push_back], this.2⟩
      · rintro ⟨h_eq, rfl⟩
        rw [← Array.pop_push_back h_pos] at h_eq
        obtain ⟨rfl, rfl⟩ := Array.push_eq_push.1 h_eq
        exact ⟨_, ⟨rfl, rfl⟩, (contains_singleton _ w _ w).2 ⟨rfl, rfl⟩⟩
termination_by ExprShape.argsSize es
decreasing_by all_goals exact ExprShape.argsSize_pop_append_lt h_pos

/--
Inserting adds exactly one entry and keeps all others. This holds for every trie, sorted or not.
-/
theorem Trie.contains_insert (es : Array ExprShape) (v : α) :
    ∀ (t : Trie α) (es' : Array ExprShape) (w : α),
      Contains (insert es v t) es' w ↔ Contains t es' w ∨ (es' = es ∧ w = v)
  | .node vs cs, es', w => by
    if h0 : es.size = 0 then
      have := Array.eq_empty_of_size_eq_zero h0; subst this
      rw [insert]
      simp only [Array.size_empty, ↓reduceDIte]
      rcases Array.eq_empty_or_eq_push es' with rfl | ⟨es'', e, rfl⟩
      · simp [contains_empty_iff, Trie.nodeValues]
      · simp [contains_push_iff]
    else
    have h_pos : 0 < es.size := by omega
    have h_es := Array.pop_push_back h_pos
    rcases Array.eq_empty_or_eq_push es' with rfl | ⟨es'', e, rfl⟩
    · rcases insert_cases h_pos v vs cs with ⟨i, hi, -, h_ins⟩ | ⟨i, hi, h_ins, -⟩ <;>
      · rw [h_ins]
        simp only [contains_empty_iff, Trie.nodeValues]
        constructor
        · exact .inl
        · rintro (h | ⟨h, _⟩)
          · exact h
          · simp [← h] at h0
    rcases insert_cases h_pos v vs cs with ⟨i, hi, hk, h_ins⟩ | ⟨i, hi, h_ins, -⟩
    · rw [h_ins, contains_push_iff, contains_push_iff]
      constructor
      · rintro ⟨c, hc, hw⟩
        rcases Array.mem_or_eq_of_mem_set hc with hc | hc
        · exact .inl ⟨c, hc, hw⟩
        · simp only [Prod.mk.injEq] at hc
          obtain ⟨hke, rfl⟩ := hc
          rcases (contains_insert _ v _ _ w).1 hw with hw | ⟨h_eq, rfl⟩
          · refine .inl ⟨cs[i].snd, ?_, hw⟩
            rw [hke, ← hk]; exact Array.getElem_mem hi
          · exact .inr ⟨by rw [ExprShape.push_eq_of_keyArgs hke h_eq, h_es], rfl⟩
      · rintro (⟨c, hc, hw⟩ | ⟨h_eq, rfl⟩)
        · obtain ⟨j, hj, hcj⟩ := Array.mem_iff_getElem.1 hc
          if hij : i = j then
            subst hij
            refine ⟨insert (es.pop ++ (es.back h_pos).getKeyArgs.snd) v c, ?_,
              (contains_insert _ v _ _ w).2 (.inl hw)⟩
            have := Array.getElem_mem (xs := cs.set i ((es.back h_pos).getKeyArgs.fst,
              insert (es.pop ++ (es.back h_pos).getKeyArgs.snd) v cs[i].snd) hi) (i := i) (by simpa using hi)
            simp only [Array.getElem_set_self] at this
            have hke : e.getKeyArgs.fst = (es.back h_pos).getKeyArgs.fst := by rw [← hk, hcj]
            have hc' : c = cs[i].snd := by rw [hcj]
            rw [hke, hc']; exact this
          else
            refine ⟨c, ?_, hw⟩
            have := Array.getElem_mem (xs := cs.set i ((es.back h_pos).getKeyArgs.fst,
              insert (es.pop ++ (es.back h_pos).getKeyArgs.snd) v cs[i].snd) hi) (i := j) (by simpa using hj)
            simp only [Array.getElem_set, hij, ↓reduceIte] at this
            rwa [hcj] at this
        · rw [← h_es] at h_eq
          obtain ⟨rfl, rfl⟩ := Array.push_eq_push.1 h_eq
          refine ⟨_, ?_, (contains_insert _ w cs[i].snd _ w).2 (.inr ⟨rfl, rfl⟩)⟩
          have := Array.getElem_mem (xs := cs.set i ((es.back h_pos).getKeyArgs.fst,
            insert (es.pop ++ (es.back h_pos).getKeyArgs.snd) w cs[i].snd) hi)
            (i := i) (by simpa using hi)
          simpa using this
    · rw [h_ins, contains_push_iff, contains_push_iff]
      constructor
      · rintro ⟨c, hc, hw⟩
        rcases Array.mem_insertIdx.1 hc with hc | hc
        · simp only [Prod.mk.injEq] at hc
          obtain ⟨hke, rfl⟩ := hc
          have := (contains_singleton _ v _ w).1 hw
          exact .inr ⟨by rw [ExprShape.push_eq_of_keyArgs hke this.1, h_es], this.2⟩
        · exact .inl ⟨c, hc, hw⟩
      · rintro (⟨c, hc, hw⟩ | ⟨h_eq, rfl⟩)
        · exact ⟨c, Array.mem_insertIdx.2 (.inr hc), hw⟩
        · rw [← h_es] at h_eq
          obtain ⟨rfl, rfl⟩ := Array.push_eq_push.1 h_eq
          exact ⟨_, Array.mem_insertIdx.2 (.inl rfl), (contains_singleton _ w _ w).2 ⟨rfl, rfl⟩⟩
termination_by _ => ExprShape.argsSize es
decreasing_by all_goals exact ExprShape.argsSize_pop_append_lt h_pos

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

theorem Trie.KeysSorted.set {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat} (hi : i < cs.size)
    {y : Key × Trie α} (hy : y.fst = cs[i].fst) : KeysSorted (cs.set i y) := by
  unfold KeysSorted at *
  rw [Array.toList_set, List.map_set, hy]
  have : cs[i].fst = (cs.toList.map Prod.fst)[i]'(by simpa using hi) := by simp
  rwa [this, List.set_getElem_self]

theorem Trie.KeysSorted.insertIdx {cs : Array (Key × Trie α)} (hs : KeysSorted cs) {i : Nat}
    (hi : i ≤ cs.size) {y : Key × Trie α}
    (hprev : ∀ h : 0 < i, cs[i - 1].fst < y.fst) (hnext : ∀ h : i < cs.size, y.fst < cs[i].fst) :
    KeysSorted (cs.insertIdx i y) := by
  unfold KeysSorted at *
  rw [Array.toList_insertIdx, List.map_insertIdx']
  refine List.pairwise_insertIdx_of_neighbors (R := (· < ·)) Key.lt_trans
    (by simp only [List.length_map, Array.length_toList]; exact hi) hs (fun h => ?_) (fun h => ?_)
  · simp only [List.getElem_map, Array.getElem_toList]; exact hprev h
  · grind

theorem Trie.sorted_singleton (es : Array ExprShape) (v : α) : Sorted (singleton es v) := by
  rw [singleton]
  split
  · exact .node (by simp [KeysSorted]) (by simp)
  · rename_i h0
    refine .node (by simp [KeysSorted]) ?_
    simp only [Array.mem_singleton, forall_eq]
    exact sorted_singleton _ v
termination_by ExprShape.argsSize es
decreasing_by exact ExprShape.argsSize_pop_append_lt (by omega)

/-- Insertion keeps every node's children sorted. -/
theorem Trie.Sorted.insert (es : Array ExprShape) (v : α) : ∀ (t : Trie α), Sorted t → Sorted (insert es v t)
  | .node vs cs, hs => by
    if h0 : es.size = 0 then
      rw [Trie.insert]
      simp only [h0, ↓reduceDIte]
      exact .node hs.keys (fun c hc => hs.child hc)
    else
    have h_pos : 0 < es.size := by omega
    rcases insert_cases h_pos v vs cs with ⟨i, hi, hk, h_ins⟩ | ⟨i, hi, h_ins, hprev, hnext⟩
    · rw [h_ins]
      refine .node (hs.keys.set hi hk.symm) (fun c hc => ?_)
      rcases Array.mem_or_eq_of_mem_set hc with hc | rfl
      · exact hs.child hc
      · exact Sorted.insert _ v _ (hs.child (Array.getElem_mem hi))
    · rw [h_ins]
      refine .node (hs.keys.insertIdx hi hprev hnext) (fun c hc => ?_)
      rcases Array.mem_insertIdx.1 hc with rfl | hc
      · exact sorted_singleton _ v
      · exact hs.child hc
termination_by _ => ExprShape.argsSize es
decreasing_by exact ExprShape.argsSize_pop_append_lt h_pos

/-!
## Stack-based lookup agrees with the specification
-/

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

theorem Trie.lookupMany_append (xs ys : Array ExprShape) (t : Trie α) :
    lookupMany (xs ++ ys) t = (lookupMany ys t).flatMap (lookupMany xs) := by
  if h : ys.size = 0 then
    rw [Array.eq_empty_of_size_eq_zero h]
    conv => rhs; rw [lookupMany]
    simp
  else
    have h_pos : 0 < ys.size := by omega
    have hne : ys ≠ #[] := fun h' => h (by simp [h'])
    conv => lhs; rw [lookupMany]
    conv => rhs; rw [lookupMany]
    simp only [Array.size_append, h, Nat.add_eq_zero_iff, and_false, ↓reduceDIte]
    rw [Array.flatMap_assoc]
    simp only [Array.back_append_right h_pos, Array.pop_append_of_ne_empty hne]
    congr 1
    funext u
    exact lookupMany_append xs ys.pop u
termination_by ys.size
decreasing_by simp; omega

theorem Trie.getUnify_eq (skip : Nat) (todo : Array ExprShape) (accum : Array α) (t : Trie α) :
    getUnify skip todo accum t = accum ++ ((Trie.skip skip t).flatMap (lookupMany todo)).flatMap Trie.nodeValues := by
  fun_induction getUnify skip todo accum t with
  | case1 todo accum vs cs s ih =>
    rw [Array.foldl_eq_append_flatMap
      (g := fun c => ((Trie.skip (s + c.fst.arity) c.snd).flatMap (lookupMany todo)).flatMap Trie.nodeValues)
      (fun acc c hc => ih acc c hc)]
    simp only [Trie.skip, Array.flatMap_assoc]
  | case2 todo accum vs cs h0 =>
    simp [h0, Trie.skip, lookupMany, Trie.nodeValues]
  | case3 todo accum vs cs h0 rest keyArgs hst ih =>
    have hst' : ((todo.back (by omega)).getKeyArgs.fst == .star) = true := hst
    rw [Array.foldl_eq_append_flatMap
      (g := fun c => ((Trie.skip (0 + c.fst.arity) c.snd).flatMap (lookupMany rest)).flatMap Trie.nodeValues) ?h]
    case h => exact fun acc c hc => ih acc c hc
    congr 1
    rw [Trie.skip, Array.flatMap_singleton, lookupMany, dite_eq_right h0, lookup]
    simp only [hst', ↓reduceIte, Array.flatMap_assoc, rest, Nat.zero_add]
  | case4 todo accum vs cs h0 rest accum' keyArgs hst h_search ih_star =>
    have hst' : ¬((todo.back (by omega)).getKeyArgs.fst == .star) = true := hst
    have h_search' : (cs.binSearch ((todo.back (by omega)).getKeyArgs.fst, Trie.empty) (·.fst < ·.fst)) = none :=
      h_search
    rw [Trie.skip, Array.flatMap_singleton, lookupMany, dite_eq_right h0, lookup]
    simp only [hst', Bool.false_eq_true, ↓reduceIte, h_search', Array.append_empty, Array.flatMap_assoc, accum']
    split
    · rename_i c heq
      rw [ih_star c heq]
      simp only [heq, Trie.skip, Array.flatMap_singleton, rest]
    · split <;> simp_all
  | case5 todo accum vs cs h0 rest accum' c keyArgs hst h_search ih_star _ ih =>
    have hst' : ¬((todo.back (by omega)).getKeyArgs.fst == .star) = true := hst
    have h_search' : (cs.binSearch ((todo.back (by omega)).getKeyArgs.fst, Trie.empty) (·.fst < ·.fst)) = some c :=
      h_search
    rw [ih]
    conv => rhs; rw [Trie.skip, Array.flatMap_singleton, lookupMany, dite_eq_right h0, lookup]
    simp only [hst', Bool.false_eq_true, ↓reduceIte, h_search', Array.flatMap_append, Array.flatMap_assoc, Trie.skip,
      Array.flatMap_singleton, lookupMany_append, rest, keyArgs]
    rw [← Array.append_assoc]
    congr 1
    simp only [accum']
    split
    · rename_i c' heq
      rw [ih_star c' heq]
      simp only [heq, Trie.skip, Array.flatMap_singleton, rest]
    · split <;> simp_all

/--
With nothing to skip, {name}`Trie.getUnify` returns the values at the tries {name}`Trie.lookupMany`
reaches. This holds for every trie, well-formed or not.
-/
theorem Trie.getUnify_eq_lookupMany (todo : Array ExprShape) (accum : Array α) (t : Trie α) :
    getUnify 0 todo accum t = accum ++ (lookupMany todo t).flatMap Trie.nodeValues := by
  rw [getUnify_eq]
  simp only [Trie.skip, Array.flatMap_singleton]

/-!
## Lookup on sorted tries
-/

theorem Trie.mem_getUnify_iff_lookupMany :
    w ∈ getUnify 0 qs #[] t ↔ ∃ x ∈ lookupMany qs t, w ∈ x.nodeValues := by
  simp [getUnify_eq_lookupMany, Array.mem_flatMap]

/--
Soundness: every value {name}`Trie.getUnify` returns is stored under a stack of shapes that unifies
with the query. This holds for every trie.
-/
theorem Trie.getUnify_sound (h : w ∈ getUnify 0 qs #[] t) :
    ∃ es, ExprShape.UnifyMany qs es ∧ Contains t es w := by
  obtain ⟨x, hx, hw⟩ := mem_getUnify_iff_lookupMany.1 h
  obtain ⟨es, hu, hr⟩ := lookupMany_sound qs t hx
  exact ⟨es, hu, x, hr, hw⟩

/--
On a sorted trie, {name}`Trie.getUnify` returns exactly the values stored under stacks of shapes
that unify with the query.
-/
theorem Trie.mem_getUnify_iff (hs : Sorted t) :
    w ∈ getUnify 0 qs #[] t ↔ ∃ es, ExprShape.UnifyMany qs es ∧ Contains t es w := by
  refine ⟨getUnify_sound, fun ⟨es, hu, x, hr, hw⟩ => ?_⟩
  exact mem_getUnify_iff_lookupMany.2 ⟨x, lookupMany_complete qs es hu t hs hr, hw⟩

theorem ExprShape.unifyMany_singleton_left : UnifyMany #[q] es ↔ ∃ e, es = #[e] ∧ Unify q e := by
  constructor
  · intro ⟨h_size, h⟩
    obtain ⟨es', e, rfl⟩ := Array.exists_push_of_size_pos (by simp at h_size; omega : 0 < es.size)
    obtain rfl : es' = #[] := by simpa using h_size.symm
    exact ⟨e, rfl, h 0 (by simp)⟩
  · rintro ⟨e, rfl, h⟩
    exact ⟨rfl, fun | 0, _ => h⟩

/--
Looking up after an insertion finds what was found before, plus the inserted value exactly when
the query unifies with the inserted key.
-/
theorem Trie.mem_getUnify_insert_iff (hs : Sorted t) :
    w ∈ getUnify 0 qs #[] (insert es v t) ↔
      w ∈ getUnify 0 qs #[] t ∨ (w = v ∧ ExprShape.UnifyMany qs es) := by
  rw [mem_getUnify_iff (Sorted.insert es v t hs), mem_getUnify_iff hs]
  simp only [contains_insert]
  grind

theorem Trie.empty_eq : (Trie.empty : Trie α) = .node #[] #[] := rfl

theorem Trie.sorted_empty : Sorted (Trie.empty : Trie α) :=
  empty_eq ▸ .node (by simp [KeysSorted]) (by simp)

theorem Trie.not_contains_empty : ¬ Contains (Trie.empty : Trie α) es w := by
  rintro ⟨x, hr, hw⟩
  rcases Array.eq_empty_or_eq_push es with rfl | ⟨es', e, rfl⟩
  · grind [reach_empty_iff, Trie.empty, Trie.nodeValues]
  · grind [reach_push_iff, Trie.empty]

/--
A trie built by inserting a list of key/value pairs into the empty trie returns, for any query,
exactly the values whose keys unify with the query.
-/
theorem Trie.mem_getUnify_foldl_insert {kvs : List (ExprShape × α)} :
    w ∈ getUnify 0 #[q] #[] (kvs.foldl (fun t (e, v) => t.insert #[e] v) Trie.empty) ↔
      ∃ e, (e, w) ∈ kvs ∧ q.Unify e := by
  suffices ∀ (t : Trie α), Sorted t →
      (Sorted (kvs.foldl (fun t (e, v) => t.insert #[e] v) t) ∧
        (w ∈ getUnify 0 #[q] #[] (kvs.foldl (fun t (e, v) => t.insert #[e] v) t) ↔
          w ∈ getUnify 0 #[q] #[] t ∨ ∃ e, (e, w) ∈ kvs ∧ q.Unify e)) by
    rw [(this Trie.empty sorted_empty).2, mem_getUnify_iff sorted_empty]
    simp [not_contains_empty]
  induction kvs with
  | nil => intro t hs; simp [hs]
  | cons kv kvs ih =>
    intro t hs
    obtain ⟨e, v⟩ := kv
    obtain ⟨ih₁, ih₂⟩ := ih _ (Sorted.insert #[e] v t hs)
    refine ⟨ih₁, ?_⟩
    simp only [List.foldl_cons]
    rw [ih₂, mem_getUnify_insert_iff hs, ExprShape.unifyMany_singleton_left]
    grind

/-!
## Well-formedness

Insertion preserves {name}`Trie.WF`.
-/

theorem Trie.wf_zero {vs : Array α} {cs} : (node vs cs).WF 0 ↔ vs.size > 0 ∧ cs.size = 0 := by
  rw [Trie.WF]

theorem Trie.wf_succ {vs : Array α} {cs} :
    (node vs cs).WF (n + 1) ↔ vs.size = 0 ∧ cs.size > 0 ∧ KeysSorted cs ∧
      ∀ c ∈ cs, c.snd.WF (n + c.fst.arity) := by
  rw [Trie.WF, KeysSorted, List.pairwise_map]

theorem Trie.wf_singleton (args : Array ExprShape) (v : α) : (singleton args v).WF args.size := by
  rw [singleton]
  split
  · rename_i h0
    rw [h0, wf_zero]
    simp
  · rename_i h0
    obtain ⟨k, hk⟩ : ∃ k, args.size = k + 1 := ⟨args.size - 1, by omega⟩
    rw [hk, wf_succ]
    refine ⟨rfl, by simp, by simp [KeysSorted], ?_⟩
    simp only [Array.mem_singleton, forall_eq]
    have := wf_singleton (args.pop ++ (args.back (by omega)).getKeyArgs.snd) v
    rw [Array.size_append, Array.size_pop] at this
    rwa [← ExprShape.size_getKeyArgs_snd, show k = args.size - 1 by omega]
termination_by ExprShape.argsSize args
decreasing_by exact ExprShape.argsSize_pop_append_lt (by omega)

/--
Inserting a stack of shapes into a trie whose level is the stack's size preserves well-formedness.
-/
theorem Trie.WF.insert (args : Array ExprShape) (v : α) :
    ∀ (t : Trie α), t.WF args.size → (insert args v t).WF args.size
  | .node vs cs, h => by
    if h0 : args.size = 0 then
      rw [Trie.insert]
      simp only [h0, ↓reduceDIte] at h ⊢
      rw [wf_zero] at h ⊢
      simp only [Array.size_push]
      omega
    else
    have h_pos : 0 < args.size := by omega
    obtain ⟨k, hk⟩ : ∃ k, args.size = k + 1 := ⟨args.size - 1, by omega⟩
    have h_size : (args.pop ++ (args.back h_pos).getKeyArgs.snd).size =
        k + (args.back h_pos).getKeyArgs.fst.arity := by
      simp only [Array.size_append, Array.size_pop, ExprShape.size_getKeyArgs_snd]; omega
    rw [hk, wf_succ] at h
    obtain ⟨hvs, hcs, hks, hch⟩ := h
    rcases insert_cases h_pos v vs cs with ⟨i, hi, hk', h_ins⟩ | ⟨i, hi, h_ins, hprev, hnext⟩
    · rw [h_ins, hk, wf_succ]
      refine ⟨hvs, by simpa using hcs, hks.set hi hk'.symm, fun c hc => ?_⟩
      rcases Array.mem_or_eq_of_mem_set hc with hc | rfl
      · exact hch c hc
      · have := hch _ (Array.getElem_mem hi)
        rw [hk', ← h_size] at this
        rw [← h_size]
        exact Trie.WF.insert _ v _ this
    · rw [h_ins, hk, wf_succ]
      refine ⟨hvs, by simp, hks.insertIdx hi hprev hnext, fun c hc => ?_⟩
      rcases Array.mem_insertIdx.1 hc with rfl | hc
      · rw [← h_size]; exact wf_singleton _ v
      · exact hch c hc
termination_by ExprShape.argsSize args
decreasing_by exact ExprShape.argsSize_pop_append_lt h_pos

/-- Inserting into the empty trie builds a singleton. -/
theorem Trie.insert_empty (args : Array ExprShape) (v : α) :
    insert args v Trie.empty = singleton args v := by
  rw [empty_eq, insert, singleton]
  split
  · rfl
  · simp [Array.binInsertM]; rfl

theorem Trie.wf_insert_empty (args : Array ExprShape) (v : α) :
    (insert args v Trie.empty).WF args.size :=
  insert_empty args v ▸ wf_singleton args v

/-!
## Well-formed tries are built by insertion
-/

theorem Array.back_push' {xs : Array α} {x : α} {h} : (xs.push x).back h = x := by
  simp [Array.back]

/-- Inserting under a key larger than every existing key adds a new last child. -/
theorem Trie.insert_push_new {pre args : Array ExprShape} {k : Key} (hk : args.size = k.arity)
    {cs : Array (Key × Trie α)} (hlt : ∀ p ∈ cs, p.fst < k) :
    insert (pre.push (k.toShape args)) v (node vs cs) =
      node vs (cs.push (k, singleton (pre ++ args) v)) := by
  rcases insert_cases (show 0 < (pre.push (k.toShape args)).size by simp) v vs cs with ⟨i, hi, hk', h_ins⟩ | ⟨i, hi, h_ins, -, hnext⟩ <;>
    simp only [Array.back_push', Array.pop_push, Key.getKeyArgs_toShape hk] at *
  · exact absurd (hk' ▸ hlt _ (Array.getElem_mem hi)) (Key.lt_irrefl _)
  · rw [h_ins]
    obtain rfl : i = cs.size := by
      refine Nat.le_antisymm hi (Nat.not_lt.1 fun h => ?_)
      exact Key.lt_asymm (hnext h) (hlt _ (Array.getElem_mem h))
    rw [Array.insertIdx_size_self]

/-- Inserting under the last child's key inserts into that child. -/
theorem Trie.insert_push_last {pre args : Array ExprShape} {k : Key} (hk : args.size = k.arity)
    {cs : Array (Key × Trie α)} (hlt : ∀ p ∈ cs, p.fst < k) :
    insert (pre.push (k.toShape args)) v (node vs (cs.push (k, c))) =
      node vs (cs.push (k, insert (pre ++ args) v c)) := by
  rcases insert_cases (show 0 < (pre.push (k.toShape args)).size by simp) v vs (cs.push (k, c)) with ⟨i, hi, hk', h_ins⟩ | ⟨i, hi, h_ins, hprev, hnext⟩ <;>
    simp only [Array.back_push', Array.pop_push, Key.getKeyArgs_toShape hk] at *
  · rw [h_ins]
    obtain rfl : i = cs.size := by
      simp only [Array.size_push] at hi
      refine Nat.le_antisymm (by omega) (Nat.not_lt.1 fun h => ?_)
      have := hlt _ (Array.getElem_mem h)
      simp only [Array.getElem_push_lt h] at hk'
      exact Key.lt_irrefl _ (hk' ▸ this)
    simp [Array.set_push]
  · exfalso
    simp only [Array.size_push] at hi
    rcases Nat.lt_or_ge i (cs.push (k, c)).size with h | h
    · rcases Nat.lt_or_ge i cs.size with h' | h'
      · have := hnext h
        simp only [Array.getElem_push_lt h'] at this
        exact Key.lt_asymm this (hlt _ (Array.getElem_mem h'))
      · have := hnext h
        simp only [show i = cs.size by simp at h; omega, Array.getElem_push_eq] at this
        exact Key.lt_irrefl _ this
    · have := hprev (by simp at h; omega)
      simp only [show i - 1 = cs.size by simp at h; omega, Array.getElem_push_eq] at this
      exact Key.lt_irrefl _ this

/--
Turns a stack for the child under {name}`k` into a stack for its parent: the top {lit}`k.arity`
shapes become the arguments of a shape whose key is {name}`k`.
-/
def Trie.liftStack (n : Nat) (k : Key) (es : Array ExprShape) : Array ExprShape :=
  (es.extract 0 n).push (k.toShape (es.extract n es.size))

theorem Array.extract_zero_append_extract {es : Array α} (h : n ≤ es.size) :
    es.extract 0 n ++ es.extract n es.size = es := by
  rw [Array.extract_append_extract, Nat.zero_min, Nat.max_eq_right h, Array.extract_size]

theorem Trie.size_liftStack (h : n ≤ es.size) : (liftStack n k es).size = n + 1 := by
  simp [liftStack]; omega

/-- Inserting a lifted stack under a key larger than every existing key adds a new last child. -/
theorem Trie.insert_liftStack_new {k : Key} (hsz : es.size = n + k.arity)
    {cs : Array (Key × Trie α)} (hlt : ∀ p ∈ cs, p.fst < k) :
    insert (liftStack n k es) v (node vs cs) = node vs (cs.push (k, insert es v Trie.empty)) := by
  rw [liftStack, insert_push_new (by simp; omega) hlt, insert_empty,
    Array.extract_zero_append_extract (by omega)]

/-- Inserting a lifted stack under the last child's key inserts into that child. -/
theorem Trie.insert_liftStack_last {k : Key} (hsz : es.size = n + k.arity)
    {cs : Array (Key × Trie α)} (hlt : ∀ p ∈ cs, p.fst < k) :
    insert (liftStack n k es) v (node vs (cs.push (k, c))) =
      node vs (cs.push (k, insert es v c)) := by
  rw [liftStack, insert_push_last (by simp; omega) hlt, Array.extract_zero_append_extract (by omega)]

/-- Inserting the lifted stacks of a child, in order, adds that child as the new last child. -/
theorem Trie.foldl_insert_liftStack {k : Key} {cs : Array (Key × Trie α)} (hlt : ∀ p ∈ cs, p.fst < k)
    {L : List (Array ExprShape × α)} (hne : L ≠ []) (hsz : ∀ q ∈ L, q.1.size = n + k.arity) :
    (L.map fun q => (liftStack n k q.1, q.2)).foldl (fun t q => t.insert q.1 q.2) (node vs cs) =
      node vs (cs.push (k, L.foldl (fun t q => t.insert q.1 q.2) Trie.empty)) := by
  obtain ⟨q, L, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.map_cons, List.foldl_cons]
  rw [insert_liftStack_new (hsz q (by simp)) hlt]
  generalize insert q.1 q.2 Trie.empty = c
  induction L generalizing c with
  | nil => rfl
  | cons q' L ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [insert_liftStack_last (hsz q' (by simp)) hlt]
    exact ih (by simp) (fun q hq => hsz q (by grind)) _

/-- Inserting values at the empty stack appends them to a leaf. -/
theorem Trie.foldl_insert_empty_stack (l : List α) (us : Array α) :
    (l.map ((#[], ·))).foldl (fun t q => t.insert q.1 q.2) (node us cs) = node (us ++ l.toArray) cs := by
  induction l generalizing us with
  | nil => simp
  | cons v l ih => simp only [List.map_cons, List.foldl_cons]; rw [Trie.insert]; simp [ih]

/-- Children with sorted keys, each built by insertion, can be built by insertion at once. -/
theorem Trie.exists_foldl_insert_children {n : Nat} :
    ∀ (l : List (Key × Trie α)) (pre : Array (Key × Trie α)),
      (pre.toList ++ l).Pairwise (·.fst < ·.fst) →
      (∀ p ∈ l, ∃ L : List (Array ExprShape × α), L ≠ [] ∧ (∀ q ∈ L, q.1.size = n + p.1.arity) ∧
        p.2 = L.foldl (fun t q => t.insert q.1 q.2) Trie.empty) →
      ∃ L : List (Array ExprShape × α), (l ≠ [] → L ≠ []) ∧ (∀ q ∈ L, q.1.size = n + 1) ∧
        L.foldl (fun t q => t.insert q.1 q.2) (node vs pre) = node vs (pre ++ l.toArray)
  | [], _, _, _ => ⟨[], by simp, by simp, by simp⟩
  | p :: l, pre, hs, hch => by
    obtain ⟨Lp, hne, hszp, hp⟩ := hch p (by simp)
    have hlt : ∀ q ∈ pre, q.fst < p.fst := fun q hq =>
      (List.pairwise_append.1 hs).2.2 q (by simpa using hq) p (by simp)
    obtain ⟨L, -, hsz, heq⟩ := exists_foldl_insert_children l (pre.push p) (by simpa using hs)
      (fun q hq => hch q (by simp [hq]))
    refine ⟨Lp.map (fun q => (liftStack n p.1 q.1, q.2)) ++ L, by simp [hne], ?_, ?_⟩
    · intro q hq
      simp only [List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q', hq', rfl⟩ | hq
      · exact size_liftStack (by rw [hszp q' hq']; omega)
      · exact hsz q hq
    · rw [List.foldl_append, foldl_insert_liftStack hlt hne hszp, ← hp, heq]
      simp

/--
A trie that is well-formed at level {lit}`n` is built by inserting a nonempty list of stacks of
{lit}`n` shapes into the empty trie.
-/
theorem Trie.WF.exists_foldl_insert : ∀ (n : Nat) (t : Trie α), t.WF n →
    ∃ L : List (Array ExprShape × α), L ≠ [] ∧ (∀ q ∈ L, q.1.size = n) ∧
      t = L.foldl (fun t q => t.insert q.1 q.2) Trie.empty
  | 0, .node vs cs, h => by
    rw [wf_zero] at h
    obtain rfl : cs = #[] := Array.eq_empty_of_size_eq_zero h.2
    refine ⟨vs.toList.map ((#[], ·)), by simpa [← Array.toList_eq_nil_iff] using Array.ne_empty_of_size_pos h.1,
      by simp, ?_⟩
    rw [empty_eq, foldl_insert_empty_stack]
    simp
  | n+1, .node vs cs, h => by
    rw [wf_succ] at h
    obtain ⟨hvs, hcs, hks, hch⟩ := h
    obtain rfl : vs = #[] := Array.eq_empty_of_size_eq_zero hvs
    obtain ⟨L, hne, hsz, heq⟩ := exists_foldl_insert_children (n := n) (vs := (#[] : Array α)) cs.toList #[]
      (by simpa [KeysSorted, List.pairwise_map] using hks)
      (fun p hp => exists_foldl_insert (n + p.1.arity) p.2 (hch p (Array.mem_toList_iff.1 hp)))
    refine ⟨L, hne (by simpa [← Array.toList_eq_nil_iff] using Array.ne_empty_of_size_pos hcs), hsz, ?_⟩
    rw [empty_eq, heq]
    simp
termination_by _ t => sizeOf t
decreasing_by exact Trie.sizeOf_lt_of_mem (Array.mem_toList_iff.1 ‹_›)

/-!
# Correctness
-/

def KVMap.toTrie : KVMap α → Trie α :=
  List.foldl (init := Trie.empty) (fun x ⟨k, v⟩ => Trie.insert #[k] v x)

/-! Repeated insertion produces well-formed tries. -/
theorem Trie.WF.construct {kvMap : KVMap α} : kvMap = [] ∨ kvMap.toTrie.WF 1 := by
  have step : ∀ (kvs : KVMap α) (t : Trie α), t.WF 1 → (kvs.foldl (fun x ⟨k, v⟩ => Trie.insert #[k] v x) t).WF 1 := by
    intro kvs
    induction kvs with
    | nil => exact fun _ h => h
    | cons kv kvs ih => obtain ⟨k, v⟩ := kv; exact fun t h => ih _ (Trie.WF.insert #[k] v t h)
  match kvMap with
  | [] => exact .inl rfl
  | ⟨k, v⟩ :: kvs => exact .inr (step kvs _ (wf_insert_empty #[k] v))

/-! A well-formed trie can be decomposed into key/value mappings. -/
theorem Trie.WF.deconstruct {t : Trie α} : t.WF 1 → ∃ elements : KVMap α, t = elements.toTrie := by
  intro h
  obtain ⟨L, -, hsz, rfl⟩ := WF.exists_foldl_insert 1 t h
  refine ⟨L.map fun q => ⟨q.1.getD 0 .star, q.2⟩, ?_⟩
  clear h
  rw [KVMap.toTrie, List.foldl_map]
  generalize Trie.empty = t
  induction L generalizing t with
  | nil => rfl
  | cons q L ih =>
    obtain ⟨⟨_ | ⟨e, _ | _⟩⟩, v⟩ := q
    all_goals simp only [List.mem_cons, forall_eq_or_imp, List.size_toArray, List.length_cons, List.length_nil] at hsz
    all_goals try omega
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun q hq => hsz.2 q hq) _

/-! The key-value map view and {name}`Trie.getUnify` agree on queries. -/
theorem Trie.mem_getUnify_toTrie {kvMap : KVMap α} :
  v ∈ kvMap.toTrie.getUnify 0 #[k] #[] ↔ v ∈ kvMap.getUnify k := by
  have h : kvMap.toTrie =
      (kvMap.map fun kv => (kv.key, kv.value)).foldl (fun t (e, v) => t.insert #[e] v) Trie.empty := by
    rw [KVMap.toTrie, List.foldl_map]
  rw [h, Trie.mem_getUnify_foldl_insert]
  simp only [KVMap.getUnify, List.mem_map, List.mem_filter, decide_eq_true_eq]
  grind [ExprShape.Unify.symm]
