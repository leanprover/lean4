axiom testSorry : α

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
termination_by x => x

/--
info: fib.fun_cases_unfolding (motive : Nat → Nat → Prop) (case1 : motive 0 0) (case2 : motive 1 1)
  (case3 : ∀ (n : Nat), motive n.succ.succ (fib n + fib (n + 1))) (x✝ : Nat) : motive x✝ (fib x✝)
-/
#guard_msgs(pass trace, all) in
#check fib.fun_cases_unfolding

-- set_option trace.Meta.FunInd true in
def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n, m)

/--
info: ackermann.fun_cases_unfolding (motive : Nat → Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m (m + 1))
  (case2 : ∀ (n : Nat), motive n.succ 0 (ackermann n 1))
  (case3 : ∀ (n m : Nat), motive n.succ m.succ (ackermann n (ackermann (n + 1) m))) (x✝ x✝¹ : Nat) :
  motive x✝ x✝¹ (ackermann x✝ x✝¹)
-/
#guard_msgs(pass trace, all) in
#check ackermann.fun_cases_unfolding

def fib' : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n => fib' (n-1) + fib' (n-2)
decreasing_by all_goals exact testSorry

/--
info: fib'.fun_cases_unfolding (motive : Nat → Nat → Prop) (case1 : motive 0 0) (case2 : motive 1 1)
  (case3 : ∀ (n : Nat), (n = 0 → False) → (n = 1 → False) → motive n (fib' (n - 1) + fib' (n - 2))) (x✝ : Nat) :
  motive x✝ (fib' x✝)
-/
#guard_msgs(pass trace, all) in
#check fib'.fun_cases_unfolding

def fib'' (n : Nat) : Nat :=
  if _h : n < 2 then
    n
  else
    let foo := n - 2
    if foo < 100 then
      fib'' (n - 1) + fib'' foo
    else
      0

/--
info: fib''.fun_cases_unfolding (n : Nat) (motive : Nat → Prop) (case1 : n < 2 → motive n)
  (case2 :
    ¬n < 2 →
      have foo := n - 2;
      foo < 100 → motive (fib'' (n - 1) + fib'' foo))
  (case3 :
    ¬n < 2 →
      have foo := n - 2;
      ¬foo < 100 → motive 0) :
  motive (fib'' n)
-/
#guard_msgs(pass trace, all) in
#check fib''.fun_cases_unfolding

-- set_option trace.Meta.FunInd true in
def filter (p : Nat → Bool) : List Nat → List Nat
  | [] => []
  | x::xs => if p x then x::filter p xs else filter p xs

/--
info: filter.fun_cases (p : Nat → Bool) (motive : List Nat → Prop) (case1 : motive [])
  (case2 : ∀ (x : Nat) (xs : List Nat), p x = true → motive (x :: xs))
  (case3 : ∀ (x : Nat) (xs : List Nat), ¬p x = true → motive (x :: xs)) (x✝ : List Nat) : motive x✝
-/
#guard_msgs(pass trace, all) in
#check filter.fun_cases

/--
info: filter.fun_cases_unfolding (p : Nat → Bool) (motive : List Nat → List Nat → Prop) (case1 : motive [] [])
  (case2 : ∀ (x : Nat) (xs : List Nat), p x = true → motive (x :: xs) (x :: filter p xs))
  (case3 : ∀ (x : Nat) (xs : List Nat), ¬p x = true → motive (x :: xs) (filter p xs)) (x✝ : List Nat) :
  motive x✝ (filter p x✝)
-/
#guard_msgs(pass trace, all) in
#check filter.fun_cases_unfolding

/--
info: filter.induct (p : Nat → Bool) (motive : List Nat → Prop) (case1 : motive [])
  (case2 : ∀ (x : Nat) (xs : List Nat), p x = true → motive xs → motive (x :: xs))
  (case3 : ∀ (x : Nat) (xs : List Nat), ¬p x = true → motive xs → motive (x :: xs)) (a✝ : List Nat) : motive a✝
-/
#guard_msgs(pass trace, all) in
#check filter.induct

/--
info: filter.induct_unfolding (p : Nat → Bool) (motive : List Nat → List Nat → Prop) (case1 : motive [] [])
  (case2 : ∀ (x : Nat) (xs : List Nat), p x = true → motive xs (filter p xs) → motive (x :: xs) (x :: filter p xs))
  (case3 : ∀ (x : Nat) (xs : List Nat), ¬p x = true → motive xs (filter p xs) → motive (x :: xs) (filter p xs))
  (a✝ : List Nat) : motive a✝ (filter p a✝)
-/
#guard_msgs(pass trace, all) in
#check filter.induct_unfolding

theorem filter_const_false_is_nil :
    filter (fun _ => false) xs = [] := by
  refine filter.induct_unfolding (fun _ => false) (motive := fun xs r => r = []) ?case1 ?case2 ?case3 xs
  case case1 => rfl
  case case2 => intros; contradiction
  case case3 => intros; assumption

theorem filter_filter :
    filter q (filter p xs) = filter (fun x => p x && q x) xs := by
  refine filter.induct_unfolding p (motive := fun xs r => filter q r = filter (fun x => p x && q x) xs) ?case1 ?case2 ?case3 xs
  case case1 => rfl
  case case2 =>
    intro x xs hp ih
    by_cases hq : q x
    case pos => simp [*, filter]
    case neg => simp [*, filter]
  case case3 =>
    intros
    simp [*, filter]


def map (f : Nat → Bool) : List Nat → List Bool
  | [] => []
  | x::xs => f x::map f xs
termination_by x => x

/--
info: map.fun_cases (motive : List Nat → Prop) (case1 : motive []) (case2 : ∀ (x : Nat) (xs : List Nat), motive (x :: xs))
  (x✝ : List Nat) : motive x✝
-/
#guard_msgs(pass trace, all) in
#check map.fun_cases

/--
info: map.fun_cases_unfolding (f : Nat → Bool) (motive : List Nat → List Bool → Prop) (case1 : motive [] [])
  (case2 : ∀ (x : Nat) (xs : List Nat), motive (x :: xs) (f x :: map f xs)) (x✝ : List Nat) : motive x✝ (map f x✝)
-/
#guard_msgs(pass trace, all) in
#check map.fun_cases_unfolding

/--
info: map.induct (motive : List Nat → Prop) (case1 : motive [])
  (case2 : ∀ (x : Nat) (xs : List Nat), motive xs → motive (x :: xs)) (a✝ : List Nat) : motive a✝
-/
#guard_msgs(pass trace, all) in
#check map.induct

/--
info: map.induct_unfolding (f : Nat → Bool) (motive : List Nat → List Bool → Prop) (case1 : motive [] [])
  (case2 : ∀ (x : Nat) (xs : List Nat), motive xs (map f xs) → motive (x :: xs) (f x :: map f xs)) (a✝ : List Nat) :
  motive a✝ (map f a✝)
-/
#guard_msgs(pass trace, all) in
#check map.induct_unfolding

namespace BinaryWF

-- set_option trace.Meta.FunInd true in
def map2 (f : Nat → Nat → Bool) : List Nat → List Nat → List Bool
  | x::xs, y::ys => f x y::map2 f xs ys
  | _, _ => []
termination_by x => x


/--
info: BinaryWF.map2.induct_unfolding (f : Nat → Nat → Bool) (motive : List Nat → List Nat → List Bool → Prop)
  (case1 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive xs ys (map2 f xs ys) → motive (x :: xs) (y :: ys) (f x y :: map2 f xs ys))
  (case2 :
    ∀ (x x_1 : List Nat),
      (∀ (x_2 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), x = x_2 :: xs → x_1 = y :: ys → False) →
        motive x x_1 [])
  (a✝ a✝¹ : List Nat) : motive a✝ a✝¹ (map2 f a✝ a✝¹)
-/
#guard_msgs(pass trace, all) in
#check map2.induct_unfolding

end BinaryWF

namespace BinaryStructural

def map2 (f : Nat → Nat → Bool) : List Nat → List Nat → List Bool
  | x::xs, y::ys => f x y::map2 f xs ys
  | _, _ => []
termination_by structural x => x

/--
info: BinaryStructural.map2.induct_unfolding (f : Nat → Nat → Bool) (motive : List Nat → List Nat → List Bool → Prop)
  (case1 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive xs ys (map2 f xs ys) → motive (x :: xs) (y :: ys) (f x y :: map2 f xs ys))
  (case2 :
    ∀ (t x : List Nat),
      (∀ (x_1 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t = x_1 :: xs → x = y :: ys → False) → motive t x [])
  (a✝ a✝¹ : List Nat) : motive a✝ a✝¹ (map2 f a✝ a✝¹)
-/
#guard_msgs(pass trace, all) in
#check map2.induct_unfolding

end BinaryStructural

namespace MutualWF

mutual
def map2a (f : Nat → Nat → Bool) : List Nat → List Nat → List Bool
  | x::xs, y::ys => f x y::map2b f xs ys
  | _, _ => []
termination_by x => x
def map2b (f : Nat → Nat → Bool) : List Nat → List Nat → List Bool
  | x::xs, y::ys => f x y::map2a f xs ys
  | _, _ => []
termination_by x => x
end

/--
info: MutualWF.map2a.mutual_induct_unfolding (f : Nat → Nat → Bool) (motive1 motive2 : List Nat → List Nat → List Bool → Prop)
  (case1 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive2 xs ys (map2b f xs ys) → motive1 (x :: xs) (y :: ys) (f x y :: map2b f xs ys))
  (case2 :
    ∀ (x x_1 : List Nat),
      (∀ (x_2 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), x = x_2 :: xs → x_1 = y :: ys → False) →
        motive1 x x_1 [])
  (case3 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive1 xs ys (map2a f xs ys) → motive2 (x :: xs) (y :: ys) (f x y :: map2a f xs ys))
  (case4 :
    ∀ (x x_1 : List Nat),
      (∀ (x_2 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), x = x_2 :: xs → x_1 = y :: ys → False) →
        motive2 x x_1 []) :
  (∀ (a a_1 : List Nat), motive1 a a_1 (map2a f a a_1)) ∧ ∀ (a a_1 : List Nat), motive2 a a_1 (map2b f a a_1)
-/
#guard_msgs(pass trace, all) in
#check map2a.mutual_induct_unfolding

/--
info: MutualWF.map2a.induct_unfolding (f : Nat → Nat → Bool) (motive1 motive2 : List Nat → List Nat → List Bool → Prop)
  (case1 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive2 xs ys (map2b f xs ys) → motive1 (x :: xs) (y :: ys) (f x y :: map2b f xs ys))
  (case2 :
    ∀ (x x_1 : List Nat),
      (∀ (x_2 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), x = x_2 :: xs → x_1 = y :: ys → False) →
        motive1 x x_1 [])
  (case3 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive1 xs ys (map2a f xs ys) → motive2 (x :: xs) (y :: ys) (f x y :: map2a f xs ys))
  (case4 :
    ∀ (x x_1 : List Nat),
      (∀ (x_2 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), x = x_2 :: xs → x_1 = y :: ys → False) →
        motive2 x x_1 [])
  (a✝ a✝¹ : List Nat) : motive1 a✝ a✝¹ (map2a f a✝ a✝¹)
-/
#guard_msgs(pass trace, all) in
#check map2a.induct_unfolding

end MutualWF

namespace MutualStructural

-- set_option trace.Meta.FunInd true in
mutual
def map2a (f : Nat → Nat → Bool) : List Nat → List Nat → List Bool
  | x::xs, y::ys => f x y::map2b f xs ys
  | _, _ => []
termination_by structural x => x
def map2b (f : Nat → Nat → Bool) : List Nat → List Nat → List Bool
  | x::xs, y::ys => f x y::map2a f xs ys
  | _, _ => []
termination_by structural x => x
end

/--
info: MutualStructural.map2a.induct (motive_1 motive_2 : List Nat → List Nat → Prop)
  (case1 : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), motive_2 xs ys → motive_1 (x :: xs) (y :: ys))
  (case2 :
    ∀ (t x : List Nat),
      (∀ (x_1 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t = x_1 :: xs → x = y :: ys → False) → motive_1 t x)
  (case3 : ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), motive_1 xs ys → motive_2 (x :: xs) (y :: ys))
  (case4 :
    ∀ (t x : List Nat),
      (∀ (x_1 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t = x_1 :: xs → x = y :: ys → False) → motive_2 t x)
  (a✝ a✝¹ : List Nat) : motive_1 a✝ a✝¹
-/
#guard_msgs(pass trace, all) in
#check map2a.induct


/--
info: MutualStructural.map2a.mutual_induct_unfolding (f : Nat → Nat → Bool)
  (motive_1 motive_2 : List Nat → List Nat → List Bool → Prop)
  (case1 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive_2 xs ys (map2b f xs ys) → motive_1 (x :: xs) (y :: ys) (map2a f (x :: xs) (y :: ys)))
  (case2 :
    ∀ (t x : List Nat),
      (∀ (x_1 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t = x_1 :: xs → x = y :: ys → False) →
        motive_1 t x (map2a f t x))
  (case3 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive_1 xs ys (map2a f xs ys) → motive_2 (x :: xs) (y :: ys) (map2b f (x :: xs) (y :: ys)))
  (case4 :
    ∀ (t x : List Nat),
      (∀ (x_1 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t = x_1 :: xs → x = y :: ys → False) →
        motive_2 t x (map2b f t x)) :
  (∀ (a a_1 : List Nat), motive_1 a a_1 (map2a f a a_1)) ∧ ∀ (a a_1 : List Nat), motive_2 a a_1 (map2b f a a_1)
-/
#guard_msgs(pass trace, all) in
#check map2a.mutual_induct_unfolding


/--
info: MutualStructural.map2a.induct_unfolding (f : Nat → Nat → Bool)
  (motive_1 motive_2 : List Nat → List Nat → List Bool → Prop)
  (case1 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive_2 xs ys (map2b f xs ys) → motive_1 (x :: xs) (y :: ys) (map2a f (x :: xs) (y :: ys)))
  (case2 :
    ∀ (t x : List Nat),
      (∀ (x_1 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t = x_1 :: xs → x = y :: ys → False) →
        motive_1 t x (map2a f t x))
  (case3 :
    ∀ (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat),
      motive_1 xs ys (map2a f xs ys) → motive_2 (x :: xs) (y :: ys) (map2b f (x :: xs) (y :: ys)))
  (case4 :
    ∀ (t x : List Nat),
      (∀ (x_1 : Nat) (xs : List Nat) (y : Nat) (ys : List Nat), t = x_1 :: xs → x = y :: ys → False) →
        motive_2 t x (map2b f t x))
  (a✝ a✝¹ : List Nat) : motive_1 a✝ a✝¹ (map2a f a✝ a✝¹)
-/
#guard_msgs(pass trace, all) in
#check map2a.induct_unfolding

end MutualStructural


abbrev leftChild (i : Nat) := 2*i + 1
abbrev parent (i : Nat) := (i - 1) / 2

def siftDown (a : Array Int) (root : Nat) (e : Nat) (h : e ≤ a.size := by omega) : Array Int :=
  if _ : leftChild root < e then
    let child := leftChild root
    let child := if _ : child+1 < e then
      if a[child] < a[child + 1] then
        child + 1
      else
        child
    else
      child
    if a[root]! < a[child]! then
      let a := a.swapIfInBounds root child
      siftDown a child e testSorry
    else
      a
  else
    a
termination_by e - root
decreasing_by exact testSorry

/--
info: siftDown.induct_unfolding (e : Nat) (motive : (a : Array Int) → Nat → e ≤ a.size → Array Int → Prop)
  (case1 :
    ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        let child := if x : child + 1 < e then if h : a[child] < a[child + 1] then child + 1 else child else child;
        a[root]! < a[child]! →
          let a_1 := a.swapIfInBounds root child;
          motive a_1 child ⋯ (siftDown a_1 child e ⋯) → motive a root h (siftDown a_1 child e ⋯))
  (case2 :
    ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        have child := if x : child + 1 < e then if h : a[child] < a[child + 1] then child + 1 else child else child;
        ¬a[root]! < a[child]! → motive a root h a)
  (case3 : ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size), ¬leftChild root < e → motive a root h a) (a : Array Int)
  (root : Nat) (h : e ≤ a.size) : motive a root h (siftDown a root e h)
-/
#guard_msgs(pass trace, all) in
#check siftDown.induct_unfolding

/--
info: siftDown.induct (e : Nat) (motive : (a : Array Int) → Nat → e ≤ a.size → Prop)
  (case1 :
    ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        let child := if x : child + 1 < e then if h : a[child] < a[child + 1] then child + 1 else child else child;
        a[root]! < a[child]! →
          let a_1 := a.swapIfInBounds root child;
          motive a_1 child ⋯ → motive a root h)
  (case2 :
    ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size),
      leftChild root < e →
        let child := leftChild root;
        have child := if x : child + 1 < e then if h : a[child] < a[child + 1] then child + 1 else child else child;
        ¬a[root]! < a[child]! → motive a root h)
  (case3 : ∀ (a : Array Int) (root : Nat) (h : e ≤ a.size), ¬leftChild root < e → motive a root h) (a : Array Int)
  (root : Nat) (h : e ≤ a.size) : motive a root h
-/
#guard_msgs(pass trace, all) in
#check siftDown.induct

-- Now something with have

def withHave (n : Nat): Bool :=
  have : 0 < n := testSorry
  if n = 42 then true else withHave (n - 1)
termination_by n
decreasing_by exact testSorry

/--
info: withHave.induct_unfolding (motive : Nat → Bool → Prop) (case1 : 0 < 42 → motive 42 true)
  (case2 : ∀ (x : Nat), 0 < x → ¬x = 42 → motive (x - 1) (withHave (x - 1)) → motive x (withHave (x - 1))) (n : Nat) :
  motive n (withHave n)
-/
#guard_msgs(pass trace, all) in
#check withHave.induct_unfolding

/--
info: withHave.fun_cases_unfolding (n : Nat) (motive : Bool → Prop) (case1 : 0 < n → n = 42 → motive true)
  (case2 : 0 < n → ¬n = 42 → motive (withHave (n - 1))) : motive (withHave n)
-/
#guard_msgs(pass trace, all) in
#check withHave.fun_cases_unfolding

-- Structural Mutual recursion

inductive Tree (α : Type u) : Type u where
  | node : α → (Bool → List (Tree α)) → Tree α

mutual
def Tree.size : Tree α → Nat
  | .node _ tsf => 1 + size_aux (tsf true) + size_aux (tsf false)
termination_by structural t => t
def Tree.size_aux : List (Tree α) → Nat
  | [] => 0
  | t :: ts => size t + size_aux ts
end

/--
info: Tree.size.induct_unfolding.{u_1} {α : Type u_1} (motive_1 : Tree α → Nat → Prop) (motive_2 : List (Tree α) → Nat → Prop)
  (case1 :
    ∀ (a : α) (tsf : Bool → List (Tree α)),
      motive_2 (tsf true) (Tree.size_aux (tsf true)) →
        motive_2 (tsf false) (Tree.size_aux (tsf false)) →
          motive_1 (Tree.node a tsf) (1 + Tree.size_aux (tsf true) + Tree.size_aux (tsf false)))
  (case2 : motive_2 [] 0)
  (case3 :
    ∀ (t : Tree α) (ts : List (Tree α)),
      motive_1 t t.size → motive_2 ts (Tree.size_aux ts) → motive_2 (t :: ts) (t.size + Tree.size_aux ts))
  (a✝ : Tree α) : motive_1 a✝ a✝.size
-/
#guard_msgs(pass trace, all) in
#check Tree.size.induct_unfolding

/--
info: Tree.size_aux.induct_unfolding.{u_1} {α : Type u_1} (motive_1 : Tree α → Nat → Prop)
  (motive_2 : List (Tree α) → Nat → Prop)
  (case1 :
    ∀ (a : α) (tsf : Bool → List (Tree α)),
      motive_2 (tsf true) (Tree.size_aux (tsf true)) →
        motive_2 (tsf false) (Tree.size_aux (tsf false)) →
          motive_1 (Tree.node a tsf) (1 + Tree.size_aux (tsf true) + Tree.size_aux (tsf false)))
  (case2 : motive_2 [] 0)
  (case3 :
    ∀ (t : Tree α) (ts : List (Tree α)),
      motive_1 t t.size → motive_2 ts (Tree.size_aux ts) → motive_2 (t :: ts) (t.size + Tree.size_aux ts))
  (a✝ : List (Tree α)) : motive_2 a✝ (Tree.size_aux a✝)
-/
#guard_msgs(pass trace, all) in
#check Tree.size_aux.induct_unfolding


-- When the discriminants are duplicated, it is very easy for `FunInd` to be confused
-- about how to instantiate the equality theorem. Maybe not relevant in practice for now?
-- Maybe even impossible to solve.

-- set_option trace.Meta.FunInd true in
set_option linter.unusedVariables false in
def duplicatedDiscriminant (n : Nat) : Bool :=
  match h1 : n, h2 : n with
  | 0, 0 => true
  | a+1, 0 => false -- by simp_all
  | 0, b+1 => false -- by simp_all
  | a, b => true

/--
info: duplicatedDiscriminant.fun_cases_unfolding (motive : Nat → Bool → Prop) (case1 : 0 = 0 → motive 0 true)
  (case2 :
    ∀ (a : Nat),
      a.succ = 0 →
        motive 0
          (match h1 : 0, h2 : 0 with
          | 0, 0 => true
          | a.succ, 0 => false
          | 0, b.succ => false
          | a, b => true))
  (case3 :
    ∀ (b : Nat),
      0 = b.succ →
        motive b.succ
          (match h1 : b.succ, h2 : b.succ with
          | 0, 0 => true
          | a.succ, 0 => false
          | 0, b_1.succ => false
          | a, b_1 => true))
  (case4 :
    ∀ (b : Nat),
      (b = 0 → b = 0 → False) →
        (∀ (a : Nat), b = a.succ → b = 0 → False) →
          (∀ (b_1 : Nat), b = 0 → b = b_1.succ → False) →
            motive b
              (match h1 : b, h2 : b with
              | 0, 0 => true
              | a.succ, 0 => false
              | 0, b_1.succ => false
              | a, b_1 => true))
  (n : Nat) : motive n (duplicatedDiscriminant n)
-/
#guard_msgs(pass trace, all) in
#check duplicatedDiscriminant.fun_cases_unfolding

set_option linter.unusedVariables false in
def with_bif_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    bif n % 2 == 0 then
      with_bif_tailrec n
    else
      with_bif_tailrec (n-1)
termination_by n => n

/--
info: with_bif_tailrec.induct_unfolding (motive : Nat → Nat → Prop) (case1 : motive 0 0)
  (case2 : ∀ (n : Nat), (n % 2 == 0) = true → motive n (with_bif_tailrec n) → motive n.succ (with_bif_tailrec n))
  (case3 :
    ∀ (n : Nat),
      (n % 2 == 0) = false → motive (n - 1) (with_bif_tailrec (n - 1)) → motive n.succ (with_bif_tailrec (n - 1)))
  (a✝ : Nat) : motive a✝ (with_bif_tailrec a✝)
-/
#guard_msgs in
#check with_bif_tailrec.induct_unfolding


def binaryWithMatch (a b : Nat) :=
  match h : decide (a < b) with
  | true => 1 + binaryWithMatch (a - 1) (b - 1)
  | false => 0
termination_by b
decreasing_by simp at h; omega

/--
info: binaryWithMatch.induct_unfolding (motive : Nat → Nat → Nat → Prop)
  (case1 :
    ∀ (a b : Nat),
      decide (a < b) = true →
        motive (a - 1) (b - 1) (binaryWithMatch (a - 1) (b - 1)) → motive a b (1 + binaryWithMatch (a - 1) (b - 1)))
  (case2 : ∀ (a b : Nat), decide (a < b) = false → motive a b 0) (a b : Nat) : motive a b (binaryWithMatch a b)
-/
#guard_msgs in
#check binaryWithMatch.induct_unfolding
