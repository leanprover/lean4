reset_grind_attrs%
set_option warn.sorry false
set_option trace.grind.inj true

def succ (x : Nat) := x+1

@[grind inj] theorem succ_inj : Function.Injective succ := by
  grind [Function.Injective, succ]

def double (x : Nat) := 2*x

@[grind inj] theorem double_inj : Function.Injective double := by
  grind [Function.Injective, double]

@[grind inj] theorem mul_2_inj : Function.Injective (2 * ·) := by
  grind [Function.Injective]

def Array.IsId (as : Array Nat) : Prop :=
  ∀ i : Fin as.size, as[i] = i

@[grind inj] theorem array_inj {as : Array Nat} (h : as.IsId) : Function.Injective (as[·]? : Fin as.size → Option Nat) := by
  intro a b; simp; have := h a; have := h b; simp_all; grind

structure InjFn (α : Type) (β : Type) where
  f : α → β
  h : Function.Injective f

instance : CoeFun (InjFn α β) (fun _ => α → β) where
  coe s := s.f

@[grind inj] theorem fn_inj (F : InjFn α β) : Function.Injective (F : α → β) := by
  grind [Function.Injective, cases InjFn]

def toList (a : α) : List α := [a]

@[grind inj] theorem toList_inj : Function.Injective (toList : α → List α) := by
  grind [Function.Injective, toList]

example (x y : Nat) : succ (double x) = succ (double y) → x = y := by
  grind

example (x y : Nat) : toList x = toList y → x = y := by
  grind

example (x y : Nat) : toList (succ (double x)) = toList (succ (double y)) → x = y := by
  grind

example (as : Array Nat) (h : as.IsId) (i j : Fin as.size) : as[i]? = as[j]? → i = j := by
  grind

example (F : InjFn α β) : F x = F y → x = y := by
  grind

example (F : InjFn α Nat) : toList (succ (F x)) = toList (succ (F y)) → x = y := by
  grind

example (F : InjFn α Nat) : toList (succ (F x)) = a → a = toList (succ (F y)) → x = y := by
  grind

opaque p : Nat → Nat → Prop
@[grind =] theorem peq : p x y = (x = double (succ y)) := sorry

example (x y : Nat) : (double (succ x)) = a → p a y → x = y := by
  grind
