module
@[expose] public section -- TODO: remove after we fix congr_eq

set_option trace.grind.ematch.pattern true

/--
trace: [grind.ematch.pattern] Array.getElem_push_lt: [@getElem (Array #4) `[Nat] _ _ _ (@Array.push _ #3 #2) #1 _]
-/
#guard_msgs in
grind_pattern Array.getElem_push_lt => (xs.push x)[i]


/--
trace: [grind.ematch.pattern] List.getElem_attach: [@getElem (List (@Subtype #3 _)) `[Nat] (@Subtype _ _) _ _ (@List.attach _ #2) #1 _]
-/
#guard_msgs in
grind_pattern List.getElem_attach => xs.attach[i]

/--
trace: [grind.ematch.pattern] List.mem_concat_self: [@Membership.mem #2 (List _) _ (@HAppend.hAppend (List _) (List _) (List _) _ #1 (@List.cons _ #0 (@List.nil _))) #0]
-/
#guard_msgs in
grind_pattern List.mem_concat_self => a ∈ xs ++ [a]

def foo (x : Nat) := x + x

/-- error: invalid E-matching theorem `foo`, type is not a proposition -/
#guard_msgs in
grind_pattern foo => x + x

/--
error: invalid pattern(s) for `Array.getElem_push_lt`
  [@Array.push #4 #3 #2]
the following theorem parameters cannot be instantiated:
  i : Nat
  h : i < xs.size
---
trace: [grind.ematch.pattern] Array.getElem_push_lt: [@Array.push #4 #3 #2]
-/
#guard_msgs in
grind_pattern Array.getElem_push_lt => (xs.push x)

class Foo (α : Type) (β : outParam Type) where
  a : Unit

class Boo (α : Type) (β : Type) where
  b : β

def f [Foo α β] [Boo α β] (a : α) : (α × β) :=
  (a, Boo.b α)

instance [Foo α β] : Foo (List α) (Array β) where
  a := ()

instance [Boo α β] : Boo (List α) (Array β) where
  b := #[Boo.b α]

theorem fEq [Foo α β] [Boo α β] (a : List α) : (f a).1 = a := rfl

/-- trace: [grind.ematch.pattern] fEq: [@f (List #4) (Array #3) _ _ #0] -/
#guard_msgs in
grind_pattern fEq => f a

theorem fEq2 [Foo α β] [Boo α β] (a : List α) (_h : a.length > 5) : (f a).1 = a := rfl

/-- trace: [grind.ematch.pattern] fEq2: [@f (List #5) (Array #4) _ _ #1] -/
#guard_msgs in
grind_pattern fEq2 => f a

def g [Boo α β] (a : α) : (α × β) :=
  (a, Boo.b α)

theorem gEq [Boo α β] (a : List α) : (g (β := Array β) a).1 = a := rfl

/--
error: invalid pattern(s) for `gEq`
  [@g (List #3) _ _ #0]
the following theorem parameters cannot be instantiated:
  β : Type
  inst✝ : Boo α β
---
trace: [grind.ematch.pattern] gEq: [@g (List #3) _ _ #0]
-/
#guard_msgs in
grind_pattern gEq => g a

def plus (a : Nat) (b : Nat) := a + b

theorem hThm1 (h : b > 10) : plus a b + plus a c > 10 := by
  unfold plus; omega

/--
error: invalid pattern(s) for `hThm1`
  [plus #2 #3]
the following theorem parameters cannot be instantiated:
  c : Nat
---
trace: [grind.ematch.pattern] hThm1: [plus #2 #3]
-/
#guard_msgs in
grind_pattern hThm1 => plus a b

/--
error: invalid pattern(s) for `hThm1`
  [plus #2 #1]
the following theorem parameters cannot be instantiated:
  b : Nat
  h : b > 10
---
trace: [grind.ematch.pattern] hThm1: [plus #2 #1]
-/
#guard_msgs in
grind_pattern hThm1 => plus a c

/-- trace: [grind.ematch.pattern] hThm1: [plus #2 #1, plus #2 #3] -/
#guard_msgs in
grind_pattern hThm1 => plus a c, plus a b

/--
error: invalid pattern, (non-forbidden) application expected
  And #4 #3
-/
#guard_msgs (error) in
grind_pattern And.imp_left => a ∧ b
