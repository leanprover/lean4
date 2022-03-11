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
