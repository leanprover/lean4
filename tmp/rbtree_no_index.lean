universes u v

inductive rbnode (α : Type u)
| leaf  {}                                                 : rbnode
| red_node   (lchild : rbnode) (val : α) (rchild : rbnode) : rbnode
| black_node (lchild : rbnode) (val : α) (rchild : rbnode) : rbnode

namespace rbnode
variables {α : Type u} {β : Type v}

@[derive decidable_eq]
inductive color
| red | black

open color nat

inductive well_formed : rbnode α → color → nat → Prop
| leaf_wff       : well_formed leaf black 0
| red_node_wff   : ∀ {v l r n}, well_formed l black n → well_formed r black n → well_formed (red_node l v r) red n
| black_node_wff : ∀ {v l r n c₁ c₂}, well_formed l c₁ n → well_formed r c₂ n → well_formed (black_node l v r) black (succ n)

open well_formed

def fold (f : α → β → β) : rbnode α → β → β
| leaf b               := b
| (red_node l v r)   b := fold r (f v (fold l b))
| (black_node l v r) b := fold r (f v (fold l b))

def rev_fold (f : α → β → β) : rbnode α → β → β
| leaf b               := b
| (red_node l v r)   b := rev_fold l (f v (rev_fold r b))
| (black_node l v r) b := rev_fold l (f v (rev_fold r b))

def depth (f : nat → nat → nat) : rbnode α → nat
| leaf               := 0
| (red_node l _ r)   := succ (f (depth l) (depth r))
| (black_node l _ r) := succ (f (depth l) (depth r))

lemma depth_min : ∀ {c n} {t : rbnode α}, well_formed t c n → depth min t ≥ n :=
begin
  intros c n' t h,
  induction h,
  case leaf_wff {apply le_refl},
  case red_node_wff { simp [depth],
    have : min (depth min l) (depth min r) ≥ n,
    { apply le_min, repeat {assumption}},
    apply le_succ_of_le, assumption },
  case black_node_wff { simp [depth],
    apply succ_le_succ,
    apply le_min, repeat {assumption} }
end

private def upper : color → nat → nat
| red   n := 2*n + 1
| black n := 2*n

private lemma upper_le : ∀ c n, upper c n ≤ 2 * n + 1
| red n   := by apply le_refl
| black n := by apply le_succ

lemma depth_max' : ∀ {c n} {t : rbnode α}, well_formed t c n → depth max t ≤ upper c n :=
begin
  intros c n' t h,
  induction h,
  case leaf_wff { simp [max, depth, upper] },
  case red_node_wff {
    suffices : succ (max (depth max l) (depth max r)) ≤ 2 * n + 1,
    { simp [depth, upper, *] at * },
    apply succ_le_succ,
    apply max_le, repeat {assumption}},
  case black_node_wff {
    have : depth max l ≤ 2*n + 1, from le_trans ih_1 (upper_le _ _),
    have : depth max r ≤ 2*n + 1, from le_trans ih_2 (upper_le _ _),
    suffices new : max (depth max l) (depth max r) + 1 ≤ 2 * n + 2*1,
    { simp [depth, upper, succ_eq_add_one, left_distrib, *] at * },
    apply succ_le_succ, apply max_le, repeat {assumption}
  }
end

lemma depth_max {c n} {t : rbnode α} (h : well_formed t c n) : depth max t ≤ 2 * n + 1:=
le_trans (depth_max' h) (upper_le _ _)

lemma balanced {c n} {t : rbnode α} (h : well_formed t c n) : 2 * depth min t + 1 ≥ depth max t :=
begin
 have : 2 * depth min t + 1 ≥ 2 * n + 1,
 { apply succ_le_succ, apply mul_le_mul_left, apply depth_min h},
 apply le_trans, apply depth_max h, apply this
end

structure node (α : Type u) :=
(lchild : rbnode α) (val : α) (rchild : rbnode α)

def balance1 : rbnode α → α → rbnode α → α → rbnode α → rbnode α
| (red_node l x r₁) y r₂  v t := red_node (black_node l x r₁) y (black_node r₂ v t)
| l₁ y (red_node l₂ x r)  v t := red_node (black_node l₁ y l₂) x (black_node r v t)
| l  y r                  v t := black_node (red_node l y r) v t

lemma balance1_wff {l r t : rbnode α} {y v : α} {c_l c_r c_t n} : well_formed l c_l n → well_formed r c_r n → well_formed t c_t n → ∃ c, well_formed (balance1 l y r v t) c (succ n) :=
begin
  intros h₁ h₂ h₃, cases h₁; cases h₂; repeat {assumption <|> constructor},
end

lemma balance1_ne_leaf (l : rbnode α) (x r v t) : balance1 l x r v t ≠ leaf :=
by cases l; cases r; simp [balance1]; intro; contradiction

def balance1_node : rbnode α → α → rbnode α → rbnode α
| (red_node l x r)   v t := balance1 l x r v t
| (black_node l x r) v t := balance1 l x r v t
| leaf               v t := t  /- dummy value -/

lemma balance1_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance1_node s a t ≠ leaf :=
begin
  intro h,
  induction s,
  case leaf       { contradiction},
  case red_node   { simp [balance1_node], apply balance1_ne_leaf },
  case black_node { simp [balance1_node], apply balance1_ne_leaf }
end

def balance2 : rbnode α → α → rbnode α → α → rbnode α → rbnode α
| (red_node l x₁ r₁) y r₂  v t := red_node (black_node t v l) x₁ (black_node r₁ y r₂)
| l₁ y (red_node l₂ x₂ r₂) v t := red_node (black_node t v l₁) y (black_node l₂ x₂ r₂)
| l  y r                   v t := black_node t v (red_node l y r)

lemma balance2_wff {l r t : rbnode α} {y v : α} {c_l c_r c_t n} : well_formed l c_l n → well_formed r c_r n → well_formed t c_t n → ∃ c, well_formed (balance2 l y r v t) c (succ n) :=
begin
  intros h₁ h₂ h₃, cases h₁; cases h₂; repeat {assumption <|> constructor},
end

def balance2_node : rbnode α → α → rbnode α → rbnode α
| (red_node l x r)   v t := balance2 l x r v t
| (black_node l x r) v t := balance2 l x r v t
| leaf               v t := t /- dummy -/

lemma balance2_ne_leaf (l : rbnode α) (x r v t) : balance2 l x r v t ≠ leaf :=
by cases l; cases r; simp [balance2]; intro; contradiction

lemma balance2_node_ne_leaf {s : rbnode α} (a : α) (t : rbnode α) : s ≠ leaf → balance2_node s a t ≠ leaf :=
begin
  intro h,
  induction s,
  case leaf       { contradiction},
  case red_node   { simp [balance2_node], apply balance2_ne_leaf },
  case black_node { simp [balance2_node], apply balance2_ne_leaf }
end

def get_color : rbnode α → color
| (red_node _ _ _) := red
| _                := black

section insert

variables (lt : α → α → Prop) [decidable_rel lt]

def ins : rbnode α → α → rbnode α
| leaf             x  := red_node leaf x leaf
| (red_node a y b) x  :=
   match cmp_using lt x y with
   | ordering.lt := red_node (ins a x) y b
   | ordering.eq := red_node a x b
   | ordering.gt := red_node a y (ins b x)
   end
| (black_node a y b) x :=
    match cmp_using lt x y with
    | ordering.lt :=
      if a.get_color = red then balance1_node (ins a x) y b
      else black_node (ins a x) y b
    | ordering.eq := black_node a x b
    | ordering.gt :=
      if b.get_color = red then balance2_node (ins b x) y a
      else black_node a y (ins b x)
    end

@[elab_as_eliminator]
lemma ins.induction_on {p : rbnode α → Prop}
  (t x)
  (h₁ : p leaf)
  (h₂ : ∀ a y b, cmp_using lt x y = ordering.lt → p a → p (red_node a y b))
  (h₃ : ∀ a y b, cmp_using lt x y = ordering.eq → p (red_node a y b))
  (h₄ : ∀ a y b, cmp_using lt x y = ordering.gt → p b → p (red_node a y b))
  (h₅ : ∀ a y b, cmp_using lt x y = ordering.lt → get_color a = red → p a → p (black_node a y b))
  (h₆ : ∀ a y b, cmp_using lt x y = ordering.lt → get_color a ≠ red → p a → p (black_node a y b))
  (h₇ : ∀ a y b, cmp_using lt x y = ordering.eq → p (black_node a y b))
  (h₈ : ∀ a y b, cmp_using lt x y = ordering.gt → get_color b = red → p b → p (black_node a y b))
  (h₉ : ∀ a y b, cmp_using lt x y = ordering.gt → get_color b ≠ red → p b → p (black_node a y b))
  : p t :=
begin
  induction t,
  case leaf { apply h₁ },
  case red_node a y b {
     generalize h : cmp_using lt x y = c,
     cases c,
     case ordering.lt { apply h₂, assumption, assumption },
     case ordering.eq { apply h₃, assumption },
     case ordering.gt { apply h₄, assumption, assumption },
   },
  case black_node a y b {
     generalize h : cmp_using lt x y = c,
     cases c,
     case ordering.lt {
       by_cases get_color a = red,
       { apply h₅, assumption, assumption, assumption },
       { apply h₆, assumption, assumption, assumption },
     },
     case ordering.eq { apply h₇, assumption },
     case ordering.gt {
       by_cases get_color b = red,
       { apply h₈, assumption, assumption, assumption },
       { apply h₉, assumption, assumption, assumption },
     }
  }
end

def insert (t : rbnode α) (x : α) : rbnode α :=
let r := ins lt t x in
match r with
| red_node l v r := black_node l v r
| _              := r
end

end insert

section membership

variables (lt : α → α → Prop) [decidable_rel lt]

def contains : rbnode α → α → bool
| leaf             x := ff
| (red_node a y b) x :=
  match cmp_using lt x y with
  | ordering.lt := contains a x
  | ordering.eq := tt
  | ordering.gt := contains b x
  end
| (black_node a y b) x :=
  match cmp_using lt x y with
  | ordering.lt := contains a x
  | ordering.eq := tt
  | ordering.gt := contains b x
  end

protected def mem : α → rbnode α → Prop
| a leaf               := false
| a (red_node l v r)   := mem a l ∨ cmp_using lt a v = ordering.eq  ∨ mem a r
| a (black_node l v r) := mem a l ∨ cmp_using lt a v = ordering.eq  ∨ mem a r

end membership

end rbnode

namespace rbnode

section membership_lemmas
parameters {α : Type u} (lt : α → α → Prop) [decidable_rel lt]

local infix `∈` := rbnode.mem lt

/- TODO(Leo): remove after we cleanup stdlib simp lemmas -/
local attribute [-simp] or.comm or.left_comm or.assoc

lemma mem_balance1_node {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance1_node s v t :=
begin
  cases s,
  case leaf { simp [rbnode.mem] },
  case red_node l v r {
    intro h,
    simp [balance1_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance1] at * },
    repeat { any_goals {cases h with h h} },
    any_goals { simp [*] }
  },
  case black_node l v r {
    intro h,
    simp [balance1_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance1] at * },
    repeat { any_goals {cases h with h h} },
    any_goals { simp [*] }
  }
end

lemma mem_balance2_node {x s} (v) (t : rbnode α) : x ∈ s → x ∈ balance2_node s v t :=
begin
  cases s,
  case leaf { simp [rbnode.mem] },
  case red_node l v r {
    intro h,
    simp [balance2_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance2] at * },
    repeat { any_goals {cases h with h h} },
    any_goals { simp [*] }
  },
  case black_node l v r {
    intro h,
    simp [balance2_node], cases l; cases r,
    any_goals { simp [*, rbnode.mem, balance2] at * },
    repeat { any_goals {cases h with h h} },
    any_goals { simp [*] }
  }
end

lemma ins_ne_leaf (t : rbnode α) (x : α) : t.ins lt x ≠ leaf :=
begin
  refine ins.induction_on lt t x _ _ _ _ _ _ _ _ _,
  any_goals { intros, simp [ins, *], contradiction},
  { intros, simp [ins, *], apply balance1_node_ne_leaf, assumption },
  { intros, simp [ins, *], apply balance2_node_ne_leaf, assumption },
end

lemma mem_ins [is_irrefl α lt] (t : rbnode α) (x : α) : x ∈ t.ins lt x :=
begin
  refine ins.induction_on lt t x _ _ _ _ _ _ _ _ _,
  { simp [ins, rbnode.mem], apply irrefl },
  any_goals { intros, simp [ins, rbnode.mem, *] },
  any_goals { right, left, apply irrefl },
  { apply mem_balance1_node, assumption },
  { apply mem_balance2_node, assumption }
end

lemma mem_black_node_of_mem_red_node {l r : rbnode α} {v a : α} : a ∈ red_node l v r → a ∈ black_node l v r :=
λ h, h

lemma mem_insert [is_irrefl α lt] : ∀ (a : α) (t : rbnode α), a ∈ t.insert lt a :=
begin
  intros a t,
  simp [insert],
  have h : ins lt t a ≠ leaf, { apply ins_ne_leaf },
  generalize he : ins lt t a = r,
  cases r; simp [insert],
  case leaf { contradiction },
  case black_node { rw [←he], apply mem_ins },
  case red_node {
    have : a ∈ red_node lchild val rchild, { rw [←he], apply mem_ins },
    apply mem_black_node_of_mem_red_node, assumption
  }
end

end membership_lemmas

end rbnode

open rbnode

meta def rbtree.default_lt : tactic unit :=
`[apply has_lt.lt]

def rbtree (α : Type u) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : Type u :=
{t : rbnode α // true } /- TODO(Leo): add wff condition -/

def mk_rbtree (α : Type u) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : rbtree α lt :=
⟨leaf, trivial⟩

namespace rbtree
variables {α : Type u} {lt : α → α → Prop} {h : decidable_rel lt}

def to_list : @rbtree α lt h → list α
| ⟨t, _⟩ := t.rev_fold (::) []

def insert : @rbtree α lt h → α → @rbtree α lt h
| ⟨t, _⟩   x := ⟨t.insert lt x, trivial⟩

def contains : @rbtree α lt h → α → bool
| ⟨t, _⟩ x := t.contains lt x

protected def mem (a : α) (t : @rbtree α lt h) : Prop :=
rbnode.mem lt a t.val

instance : has_mem α (@rbtree α lt h) :=
⟨rbtree.mem⟩

def from_list (l : list α) (lt : α → α → Prop . rbtree.default_lt) [decidable_rel lt] : rbtree α lt :=
l.foldl insert (mk_rbtree α lt)

lemma mem_insert [is_irrefl α lt] : ∀ (a : α) (t : @rbtree α lt h), a ∈ t.insert a
| a ⟨t, _⟩ := t.mem_insert lt a

instance [has_repr α] : has_repr (@rbtree α lt h) :=
⟨λ t, repr t.to_list⟩

end rbtree

#eval (rbtree.from_list [3, 4, 2, 5, 1] (<)).to_list
#eval (rbtree.from_list [3, 4, 2, 5, 1] (>)).to_list
#eval (rbtree.from_list [3, 4, 2, 5]).to_list
#eval rbtree.from_list [3, 4, 2, 5]
#eval rbtree.to_list $ rbtree.from_list [3, 4, 2, 5]
