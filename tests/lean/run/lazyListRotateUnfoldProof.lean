inductive LazyList (α : Type u)
| nil : LazyList α
| cons (hd : α) (tl : LazyList α) : LazyList α
| delayed (t : Thunk (LazyList α)) : LazyList α

namespace LazyList
def length : LazyList α → Nat
| nil        => 0
| cons _ as  => length as + 1
| delayed as => length as.get

def force : LazyList α → Option (α × LazyList α)
| delayed as => force as.get
| nil        => none
| cons a as  => some (a,as)
end LazyList

def rotate (f : LazyList τ) (r : List τ) (a : LazyList τ)
  (h : f.length + 1 = r.length) : LazyList τ :=
  match r with
  | List.nil => False.elim (by simp_arith [LazyList.length] at h)
  | y::r' =>
  match f.force with
  | none =>  LazyList.cons y a
  | some (x, f') => LazyList.cons x (rotate f' r' (LazyList.cons y a) (sorry))

theorem rotate_inv {F : LazyList τ} {R : List τ} : (h : F.length + 1 = R.length) → (rotate F R nil h).length = F.length + R.length := by
  match F with
  | LazyList.nil => intro h; unfold rotate; sorry
  | LazyList.cons Fh Ft => sorry
  | LazyList.delayed Ft => sorry

def LazyList.ind {α : Type u} {motive : LazyList α → Sort v}
        (nil : motive LazyList.nil)
        (cons : (hd : α) → (tl : LazyList α) → motive tl → motive (LazyList.cons hd tl))
        (delayed : (t : Thunk (LazyList α)) → motive t.get → motive (LazyList.delayed t))
        (t : LazyList α) : motive t :=
  match t with
  | LazyList.nil => nil
  | LazyList.cons h t => cons h t (ind nil cons delayed t)
  | LazyList.delayed t => delayed t (ind nil cons delayed t.get)
-- Remark: Lean used well-founded recursion behind the scenes to define LazyList.ind

/--
info: case cons
τ : Type u_1
nil : LazyList τ
R : List τ
h : τ
t : LazyList τ
ih : ∀ (h : t.length + 1 = R.length), (rotate t R nil h).length = t.length + R.length
⊢ ∀ (h_1 : (LazyList.cons h t).length + 1 = R.length),
    (rotate (LazyList.cons h t) R nil h_1).length = (LazyList.cons h t).length + R.length
---
info: case delayed
τ : Type u_1
nil : LazyList τ
R : List τ
t : Thunk (LazyList τ)
a✝ : ∀ (h : t.get.length + 1 = R.length), (rotate t.get R nil h).length = t.get.length + R.length
⊢ ∀ (h : (LazyList.delayed t).length + 1 = R.length),
    (rotate (LazyList.delayed t) R nil h).length = (LazyList.delayed t).length + R.length
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem rotate_inv' {F : LazyList τ} {R : List τ} : (h : F.length + 1 = R.length) → (rotate F R nil h).length = F.length + R.length := by
  induction F using LazyList.ind with
  | nil => intro h; unfold rotate; sorry
  | cons h t ih => trace_state; sorry
  | delayed t => trace_state; sorry
