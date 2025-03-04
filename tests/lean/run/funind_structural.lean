set_option guard_msgs.diff true

/-!
This module tests functional induction principles on *structurally* recursive functions.
-/

def fib : Nat → Nat
  | 0 | 1 => 0
  | n+2 => fib n + fib (n+1)
termination_by structural x => x

/--
info: fib.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive n → motive (n + 1) → motive n.succ.succ) (a✝ : Nat) : motive a✝
-/
#guard_msgs in
#check fib.induct


def binary : Nat → Nat → Nat
  | 0, acc | 1, acc => 1 + acc
  | n+2, acc => binary n (binary (n+1) acc)
termination_by structural x => x

/--
info: binary.induct (motive : Nat → Nat → Prop) (case1 : ∀ (acc : Nat), motive 0 acc) (case2 : ∀ (acc : Nat), motive 1 acc)
  (case3 : ∀ (n acc : Nat), motive (n + 1) acc → motive n (binary (n + 1) acc) → motive n.succ.succ acc)
  (a✝ a✝¹ : Nat) : motive a✝ a✝¹
-/
#guard_msgs in
#check binary.induct


-- Different parameter order
def binary' : Bool → Nat → Bool
  | acc, 0 | acc , 1 => not acc
  | acc, n+2 => binary' (binary' acc (n+1)) n
termination_by structural _ x => x

/--
info: binary'.induct (motive : Bool → Nat → Prop) (case1 : ∀ (acc : Bool), motive acc 0)
  (case2 : ∀ (acc : Bool), motive acc 1)
  (case3 : ∀ (acc : Bool) (n : Nat), motive acc (n + 1) → motive (binary' acc (n + 1)) n → motive acc n.succ.succ)
  (a✝ : Bool) (a✝¹ : Nat) : motive a✝ a✝¹
-/
#guard_msgs in
#check binary'.induct

def zip {α β} : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (x, y) :: zip xs ys
termination_by structural x => x

/--
info: zip.induct.{u_1, u_2} {α : Type u_1} {β : Type u_2} (motive : List α → List β → Prop)
  (case1 : ∀ (x : List β), motive [] x) (case2 : ∀ (t : List α), (t = [] → False) → motive t [])
  (case3 : ∀ (x : α) (xs : List α) (y : β) (ys : List β), motive xs ys → motive (x :: xs) (y :: ys)) (a✝ : List α)
  (a✝¹ : List β) : motive a✝ a✝¹
-/
#guard_msgs in
#check zip.induct

/-- Lets try ot use it! -/
theorem zip_length {α β} (xs : List α) (ys : List β) :
    (zip xs ys).length = xs.length.min ys.length := by
  induction xs, ys using zip.induct
  case case1 => simp [zip]
  case case2 => simp [zip]
  case case3 =>
    simp [zip, *]
    simp [Nat.min_def]
    split <;> omega

theorem zip_get? {i : Nat}  {α β} (as : List α) (bs : List β) :
    (List.zip as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (a, b)
      | _, _ => none := by
  induction as, bs using zip.induct generalizing i
    <;> cases i <;> simp_all

-- Testing recursion on an indexed data type
inductive Finn : Nat → Type where
  | fzero : {n : Nat} → Finn n
  | fsucc : {n : Nat} → Finn n → Finn (n+1)

def Finn.min (x : Bool) {n : Nat} (m : Nat) : Finn n → (f : Finn n) → Finn n
  | fzero, _ => fzero
  | _, fzero => fzero
  | fsucc i, fsucc j => fsucc (Finn.min (not x) (m + 1) i j)
termination_by structural n

/--
info: Finn.min.induct (motive : Bool → {n : Nat} → Nat → Finn n → Finn n → Prop)
  (case1 : ∀ (x : Bool) (m n : Nat) (x_1 : Finn n), motive x m Finn.fzero x_1)
  (case2 : ∀ (x : Bool) (m n : Nat) (x_1 : Finn n), (x_1 = Finn.fzero → False) → motive x m x_1 Finn.fzero)
  (case3 : ∀ (x : Bool) (m n : Nat) (i j : Finn n), motive (!x) (m + 1) i j → motive x m i.fsucc j.fsucc) (x : Bool)
  {n : Nat} (m : Nat) (a✝ f : Finn n) : motive x m a✝ f
-/
#guard_msgs in
#check Finn.min.induct

namespace TreeExample

inductive Tree (β : Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)

def Tree.insert (t : Tree β) (k : Nat) (v : β) : Tree β :=
  match t with
  | leaf => node leaf k v leaf
  | node left key value right =>
    if k < key then
      node (left.insert k v) key value right
    else if key < k then
      node left key value (right.insert k v)
    else
      node left k v right
termination_by structural t

/--
info: TreeExample.Tree.insert.induct.{u_1} {β : Type u_1} (k : Nat) (motive : Tree β → Prop) (case1 : motive Tree.leaf)
  (case2 :
    ∀ (left : Tree β) (key : Nat) (value : β) (right : Tree β),
      k < key → motive left → motive (left.node key value right))
  (case3 :
    ∀ (left : Tree β) (key : Nat) (value : β) (right : Tree β),
      ¬k < key → key < k → motive right → motive (left.node key value right))
  (case4 :
    ∀ (left : Tree β) (key : Nat) (value : β) (right : Tree β),
      ¬k < key → ¬key < k → motive (left.node key value right))
  (t : Tree β) : motive t
-/
#guard_msgs in
#check Tree.insert.induct

end TreeExample

namespace TermDenote

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
  | .cons a as, .head => a
  | .cons _ as, .tail h => as.get h

inductive Ty where
  | nat
  | fn : Ty → Ty → Ty

@[reducible] def Ty.denote : Ty → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote

inductive Term : List Ty → Ty → Type
  | var   : Member ty ctx → Term ctx ty
  | const : Nat → Term ctx .nat
  | plus  : Term ctx .nat → Term ctx .nat → Term ctx .nat
  | app   : Term ctx (.fn dom ran) → Term ctx dom → Term ctx ran
  | lam   : Term (.cons dom ctx) ran → Term ctx (.fn dom ran)
  | let   : Term ctx ty₁ → Term (.cons ty₁ ctx) ty₂ → Term ctx ty₂

def Term.denote : Term ctx ty → HList Ty.denote ctx → ty.denote
  | .var h,     env => env.get h
  | .const n,   _   => n
  | .plus a b,  env => a.denote env + b.denote env
  -- the following recursive call is interesting: Here the `ty.denote` for `f`'s type
  -- becomes a function, and thus the recursive call takes an extra argument
  -- But in the induction principle, we have `motive f` here, which does not
  -- take an extra argument, so we have to be careful to not pass too many arguments to it
  | .app f a,   env => f.denote env (a.denote env)
  | .lam b,     env => fun x => b.denote (.cons x env)
  | .let a b,   env => b.denote (.cons (a.denote env) env)
termination_by structural x => x

/--
info: TermDenote.Term.denote.induct (motive : {ctx : List Ty} → {ty : Ty} → Term ctx ty → HList Ty.denote ctx → Prop)
  (case1 : ∀ (a : List Ty) (ty : Ty) (h : Member ty a) (env : HList Ty.denote a), motive (Term.var h) env)
  (case2 : ∀ (a : List Ty) (n : Nat) (x : HList Ty.denote a), motive (Term.const n) x)
  (case3 :
    ∀ (a : List Ty) (a_1 b : Term a Ty.nat) (env : HList Ty.denote a),
      motive a_1 env → motive b env → motive (a_1.plus b) env)
  (case4 :
    ∀ (a : List Ty) (ty dom : Ty) (f : Term a (dom.fn ty)) (a_1 : Term a dom) (env : HList Ty.denote a),
      motive f env → motive a_1 env → motive (f.app a_1) env)
  (case5 :
    ∀ (a : List Ty) (dom ran : Ty) (b : Term (dom :: a) ran) (env : HList Ty.denote a),
      (∀ (x : dom.denote), motive b (HList.cons x env)) → motive b.lam env)
  (case6 :
    ∀ (a : List Ty) (ty ty₁ : Ty) (a_1 : Term a ty₁) (b : Term (ty₁ :: a) ty) (env : HList Ty.denote a),
      motive a_1 env → motive b (HList.cons (a_1.denote env) env) → motive (a_1.let b) env)
  {ctx : List Ty} {ty : Ty} (a✝ : Term ctx ty) (a✝¹ : HList Ty.denote ctx) : motive a✝ a✝¹
-/
#guard_msgs in
#check TermDenote.Term.denote.induct

end TermDenote
