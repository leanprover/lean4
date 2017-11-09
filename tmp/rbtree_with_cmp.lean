universes u v

inductive rbnode.color
| red
| black

open rbnode.color nat

inductive rbnode (α : Type u) : color → nat → Type u
| leaf {}                                                                      : rbnode black 0
| red_node  {n} (lchild : rbnode black n) (val : α) (rchild : rbnode black n)  : rbnode red n
| black_node {c₁ c₂ n} (lchild : rbnode c₁ n) (val : α) (rchild : rbnode c₂ n) : rbnode black (succ n)

namespace rbnode
variables {α : Type u} {β : Type v}

def fold (f : α → β → β) : Π {c n}, rbnode α c n → β → β
| _ _ leaf b               := b
| _ _ (red_node l v r)   b := fold r (f v (fold l b))
| _ _ (black_node l v r) b := fold r (f v (fold l b))

def rev_fold (f : α → β → β) : Π {c n}, rbnode α c n → β → β
| _ _ leaf b               := b
| _ _ (red_node l v r)   b := rev_fold l (f v (rev_fold r b))
| _ _ (black_node l v r) b := rev_fold l (f v (rev_fold r b))

def depth (f : nat → nat → nat) : Π {c n}, rbnode α c n → nat
| _ _ leaf               := 0
| _ _ (red_node l v r)   := succ (f (depth l) (depth r))
| _ _ (black_node l v r) := succ (f (depth l) (depth r))

lemma depth_min : ∀ {c n} (t : rbnode α c n), depth min t ≥ n :=
begin
  intros n c t,
  induction t,
  case leaf { simp [min, depth], apply le_refl },
  case red_node n l v r {
    simp [depth],
    have : min (depth min l) (depth min r) ≥ n,
    { apply le_min, repeat {assumption}},
    apply le_succ_of_le, assumption
  },
  case black_node c₁ c₂ n l v r {
    simp [depth],
    apply succ_le_succ,
    apply le_min, repeat {assumption}
  }
end

private def upper : color → nat → nat
| red   n := 2*n + 1
| black n := 2*n

private lemma upper_le : ∀ c n, upper c n ≤ 2 * n + 1
| red n   := by apply le_refl
| black n := by apply le_succ

lemma depth_max' : ∀ {c n} (t : rbnode α c n), depth max t ≤ upper c n :=
begin
  intros n c t,
  induction t,
  case leaf { simp [max, depth, upper] },
  case red_node n l v r {
    suffices : succ (max (depth max l) (depth max r)) ≤ 2 * n + 1,
    { simp [depth, upper, *] at * },
    apply succ_le_succ,
    apply max_le, repeat {assumption}},
  case black_node c₁ c₂ n l v r {
    have : depth max l ≤ 2*n + 1, from le_trans ih_1 (upper_le _ _),
    have : depth max r ≤ 2*n + 1, from le_trans ih_2 (upper_le _ _),
    suffices new : max (depth max l) (depth max r) + 1 ≤ 2 * n + 2*1,
    { simp [depth, upper, succ_eq_add_one, left_distrib, *] at * },
    apply succ_le_succ, apply max_le, repeat {assumption}
  }
end

lemma depth_max {c n} (t : rbnode α c n) : depth max t ≤ 2 * n + 1:=
le_trans (depth_max' t) (upper_le _ _)

lemma balanced {c n} (t : rbnode α c n) : 2 * depth min t + 1 ≥ depth max t :=
begin
 have : 2 * depth min t + 1 ≥ 2 * n + 1,
 { apply succ_le_succ, apply mul_le_mul_left, apply depth_min },
 apply le_trans, apply depth_max, apply this
end

/- Irregular tree nodes needed to implement insert operation -/
inductive rtree (α : Type u) : nat → Type u
| red_node' {c₁ c₂ n} (lchild : rbnode α c₁ n) (val : α) (rchild : rbnode α c₂ n) : rtree n

open rtree

def present (a : α) : Π {c n}, rbnode α c n → Prop
| _ _ leaf               := false
| _ _ (red_node l v r)   := present l ∨ a = v ∨ present r
| _ _ (black_node l v r) := present l ∨ a = v ∨ present r

def rpresent (a : α) : Π {n}, rtree α n → Prop
| _ (red_node' l v r) := present a l ∨ a = v ∨ present a r

def balance1 : Π {n}, rtree α n → α → Π {c₂}, rbnode α c₂ n → Σ c, rbnode α c (succ n)
| _ (red_node' (red_node l x r₁) y r₂)                        v _ t := ⟨_, red_node (black_node l x r₁) y (black_node r₂ v t)⟩
| _ (red_node' (black_node l₁ x₁ r₁) y (red_node l₂ x r))     v _ t := ⟨_, red_node (black_node (black_node l₁ x₁ r₁) y l₂) x (black_node r v t)⟩
| _ (red_node' (black_node l₁ x₁ r₁) y (black_node l₂ x₂ r₂)) v _ t := ⟨_, black_node (red_node (black_node l₁ x₁ r₁) y (black_node l₂ x₂ r₂)) v t⟩
| _ (red_node' leaf y (red_node l₂ x r))                      v _ t := ⟨_, red_node (black_node leaf y l₂) x (black_node r v t)⟩
| _ (red_node' leaf y leaf)                                   v _ t := ⟨_, black_node (red_node leaf y leaf) v t⟩

def balance2 : Π {n}, rtree α n → α → Π {c₂}, rbnode α c₂ n → Σ c, rbnode α c (succ n)
| _ (red_node' (red_node l x₁ r₁) y r₂)                       v _ t  := ⟨_, red_node (black_node t v l) x₁ (black_node r₁ y r₂)⟩
| _ (red_node' (black_node l₁ x₁ r₁) y (red_node l₂ x₂ r₂))   v _ t  := ⟨_, red_node (black_node t v (black_node l₁ x₁ r₁)) y (black_node l₂ x₂ r₂)⟩
| _ (red_node' leaf y leaf)                                   v _ t  := ⟨_, black_node t v (red_node leaf y leaf)⟩
| _ (red_node' leaf y (red_node l x r))                       v _ t  := ⟨_, red_node (black_node t v leaf) y (black_node l x r)⟩
| _ (red_node' (black_node l₁ x₁ r₁) y (black_node l₂ x₂ r₂)) v _ t  := ⟨_, black_node t v (red_node (black_node l₁ x₁ r₁) y (black_node l₂ x₂ r₂))⟩

def ins_result (α) : color → nat → Type u
| red   n := rtree α n
| black n := Σ c, rbnode α c n

def insert_result (α) : color → nat → Type u
| red   n := rbnode α black (succ n)
| black n := Σ c, rbnode α c n

def mk_rbnode : Π {c n}, ins_result α c n → insert_result α c n
| red   _ (red_node' a x b) := black_node a x b
| black _ t                 := t

variables [has_ordering α]

def ins : Π {c n}, rbnode α c n → α → ins_result α c n
| _ _ leaf             x   := ⟨_, red_node leaf x leaf⟩
| _ _ (red_node a y b) x   :=
    match cmp x y with
    | ordering.lt := red_node' (ins a x).2 y b
    | ordering.eq := red_node' a x b
    | ordering.gt := red_node' a y (ins b x).2
    end
| _ _ (@black_node _ c₁ c₂ _ a y b) x :=
    match cmp x y with
    | ordering.lt :=
      match c₁, a, ins a x with
      | red,   a, ins_a := balance1 ins_a y b
      | black, a, ins_a := ⟨_, black_node ins_a.2 y b⟩
      end
    | ordering.eq := ⟨_, black_node a x b⟩
    | ordering.gt :=
      match c₂, b, ins b x with
      | red, b, ins_b   := balance2 ins_b y a
      | black, b, ins_b := ⟨_, black_node a y ins_b.2⟩
      end
    end

def insert {c n} (t : rbnode α c n) (x : α) : insert_result α c n :=
mk_rbnode (ins t x)

def contains : Π {c n}, rbnode α c n → α → bool
| _ _ leaf             x := ff
| _ _ (red_node a y b) x :=
  match cmp x y with
  | ordering.lt := contains a x
  | ordering.eq := tt
  | ordering.gt := contains b x
  end
| _ _ (black_node a y b) x :=
  match cmp x y with
  | ordering.lt := contains a x
  | ordering.eq := tt
  | ordering.gt := contains b x
  end

end rbnode

/- Pack color depth and rbnode -/

structure rbtree (α : Type u) :=
(c : color) (n : nat) (t : rbnode α c n)

def mk_rbtree {α : Type u} : rbtree α :=
⟨black, 0, rbnode.leaf⟩

namespace rbtree
variables {α : Type u}

def to_list : rbtree α → list α
| ⟨_, _, t⟩ := t.rev_fold (::) []

section
variables [has_ordering α]
def insert : rbtree α → α → rbtree α
| ⟨red, n, t⟩   x := ⟨black, succ n, t.insert x⟩
| ⟨black, n, t⟩ x :=
  match t.insert x with
  | ⟨c, new_t⟩ := ⟨c, n, new_t⟩
  end

def contains : rbtree α → α → bool
| ⟨_, _, t⟩ x := t.contains x

def from_list (l : list α) : rbtree α :=
l.foldl insert mk_rbtree
end

end rbtree

set_option profiler true

#eval timeit "rbtree" $ (nat.repeat (λ i (r : rbtree nat), r.insert i) 1000 mk_rbtree).contains 100
