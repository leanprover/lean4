def x := 1

#check x

variable {α : Type}

def f (a : α) : α :=
a

def tst (xs : List Nat) : Nat :=
xs.foldl (init := 10) (· + ·)

#check tst [1, 2, 3]

#check fun x y : Nat => x + y

#check tst

#check (fun stx => if True then let e := stx; Pure.pure e else Pure.pure stx : Nat → Id Nat)

#check let x : Nat := 1; x

def foo (a : Nat) (b : Nat := 10) (c : Bool := Bool.true) : Nat :=
a + b

set_option pp.all true

#check foo 1

#check foo 3 (c := false)

def Nat.boo (a : Nat) :=
succ a -- succ here is resolved as `Nat.succ`.

#check Nat.boo

#check true

-- apply is still a valid identifier name
def apply := "hello"

#check apply

theorem simple1 (x y : Nat) (h : x = y) : x = y :=
by {
  assumption
}

theorem simple2 (x y : Nat) : x = y → x = y :=
by {
  intro h;
  assumption
}

syntax "intro2" : tactic

macro_rules
| `(tactic| intro2) => `(tactic| intro; intro )

theorem simple3 (x y : Nat) : x = x → x = y → x = y :=
by {
  intro2;
  assumption
}

macro "intro3" : tactic => `(tactic| (intro; intro; intro))
macro "check2" x:term : command => `(#check $x #check $x)
macro "foo" x:term "," y:term : term => `($x + $y + $x)

set_option pp.all false

check2 0+1
check2 foo 0,1

theorem simple4 (x y : Nat) : y = y → x = x → x = y → x = y :=
by {
  intro3;
  assumption
}

theorem simple5 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intro h1; intro _; intro h3;
  exact Eq.trans h3 h1
}

theorem simple6 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intro h1; intro _; intro h3;
  refine Eq.trans ?_ h1;
  assumption
}

theorem simple7 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intro h1; intro _; intro h3;
  refine' Eq.trans ?pre ?post;
  exact y;
  { exact h3 }
  { exact h1 }
}

theorem simple8 (x y z : Nat) : y = z → x = x → x = y → x = z := by
intro h1; intro _; intro h3
refine' Eq.trans ?pre ?post
case post => exact h1
case pre => exact h3

theorem simple9 (x y z : Nat) : y = z → x = x → x = y → x = z := by
intros h1 _ h3
trace_state
focus
  refine' Eq.trans ?pre ?post
  first
    | exact h1
      assumption
    | exact y
      exact h3
      assumption

theorem simple9b (x y z : Nat) : y = z → x = x → x = y → x = z := by
intros h1 _ h3
trace_state
focus
  refine' Eq.trans ?pre ?post
  first
    | exact h1
    | exact y; exact h3
  assumption

theorem simple9c (x y z : Nat) : y = z → x = x → x = y → x = z := by
  intros h1 _ h3
  solve
    | exact h1
    | refine' Eq.trans ?pre ?post; exact y; exact h3; assumption
    | exact h3

theorem simple9d (x y z : Nat) : y = z → x = x → x = y → x = z := by
  intros h1 _ h3
  refine' Eq.trans ?pre ?post
  solve
    | exact h1
    | exact y
    | exact h3
  solve
    | exact h1
    | exact h3
  solve
    | exact h1
    | assumption


namespace Foo
  def Prod.mk := 1
  #check (⟨2, 3⟩ : Prod _ _)
end Foo

theorem simple10 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intro h1; intro h2; intro h3;
  skip;
  apply Eq.trans;
  exact h3;
  assumption
}

theorem simple11 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intro h1; intro h2; intro h3;
  apply @Eq.trans;
  trace_state;
  exact h3;
  assumption
}

theorem simple12 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intro h1; intro h2; intro h3;
  apply @Eq.trans;
  try exact h1; -- `exact h1` fails
  trace_state;
  try exact h3;
  trace_state;
  try exact h1;
}

theorem simple13 (x y z : Nat) : y = z → x = x → x = y → x = z := by
intros h1 h2 h3
trace_state
apply @Eq.trans
case b => exact y
trace_state
repeat assumption

theorem simple13b (x y z : Nat) : y = z → x = x → x = y → x = z := by {
intros h1 h2 h3;
trace_state;
apply @Eq.trans;
case b => exact y;
trace_state;
repeat assumption
}

theorem simple14 (x y z : Nat) : y = z → x = x → x = y → x = z := by
intros
apply @Eq.trans
case b => exact y
repeat assumption

theorem simple15 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intros h1 h2 h3;
  revert y;
  intros y h1 h3;
  apply Eq.trans;
  exact h3;
  exact h1
}

theorem simple16 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intros h1 h2 h3;
  try clear x; -- should fail
  clear h2;
  trace_state;
  apply Eq.trans;
  exact h3;
  exact h1
}

macro "blabla" : tactic => `(tactic| assumption)

-- Tactic head symbols do not become reserved words
def blabla := 100

#check blabla

theorem simple17 (x : Nat) (h : x = 0) : x = 0 :=
by blabla

theorem simple18 (x : Nat) (h : x = 0) : x = 0 :=
by blabla

theorem simple19 (x y : Nat) (h₁ : x = 0) (h₂ : x = y) : y = 0 :=
by subst x; subst y; exact rfl

theorem tstprec1 (x y z : Nat) : x + y * z = x + (y * z) :=
rfl

theorem tstprec2 (x y z : Nat) : y * z + x = (y * z) + x :=
rfl

set_option pp.all true

#check fun {α} (a : α) => a
#check @(fun α (a : α) => a)

#check
  let myid := fun {α} (a : α) => a;
  myid [myid 1]

-- In the following example, we need `@` otherwise we will try to insert mvars for α and [Add α],
-- and will fail to generate instance for [Add α]
#check @(fun α (s : Add α) (a : α) => a + a)

def g1 {α} (a₁ a₂ : α) {β} (b : β) : α × α × β :=
(a₁, a₂, b)

def id1 : {α : Type} → α → α :=
fun x => x

def listId : List ({α : Type} → α → α) :=
(fun x => x) :: []

def id2 : {α : Type} → α → α :=
@(fun α (x : α) => id1 x)

def id3 : {α : Type} → α → α :=
@(fun α x => id1 x)

def id4 : {α : Type} → α → α :=
fun x => id1 x

def id5 : {α : Type} → α → α :=
fun {α} x => id1 x

def id6 : {α : Type} → α → α :=
@(fun {α} x => id1 x)

def id7 : {α : Type} → α → α :=
fun {α} x => @id α x

def id8 : {α : Type} → α → α :=
fun {α} x => id (@id α x)

def altTst1 {m σ} [Alternative m] [Monad m] : Alternative (StateT σ m) :=
⟨StateT.failure, StateT.orElse⟩

def altTst2 {m σ} [Alternative m] [Monad m] : Alternative (StateT σ m) :=
⟨@(fun α => StateT.failure), @(fun α => StateT.orElse)⟩

def altTst3 {m σ} [Alternative m] [Monad m] : Alternative (StateT σ m) :=
⟨fun {α} => StateT.failure, fun {α} => StateT.orElse⟩

#check_failure 1 + true

/-
universe u v

/-
  MonadFunctorT.{u ?M_1 v} (λ (β : Type u), m α) (λ (β : Type u), m' α) n n'
-/
set_option pp.raw.maxDepth 100
set_option trace.Elab true


def adapt {m m' σ σ'} {n n' : Type → Type} [MonadFunctor m m' n n'] [MonadStateAdapter σ σ' m m'] : MonadStateAdapter σ σ' n n' :=
⟨fun split join => monadMap (adaptState split join : m α → m' α)⟩

-/

syntax "fn" (term:max)+ "=>" term : term

macro_rules
| `(fn $xs* => $b) => `(fun $xs* => $b)

set_option pp.all false

#check fn x => x+1

#check fn α (a : α) => a

def tst1 : {α : Type} → α → α :=
@(fn α a => a)

#check @tst1

syntax ident "==>" term : term

syntax "{" ident "}" "==>" term : term

macro_rules
| `($x:ident ==> $b)   => `(fn $x => $b)
| `({$x:ident} ==> $b) => `(fun {$x:ident} => $b)

#check x ==> x+1

def tst2a : {α : Type} → α → α :=
@(α ==> a ==> a)

def tst2b : {α : Type} → α → α :=
{α} ==> a ==> a

#check @tst2a
#check @tst2b

def tst3a : {α : Type} → {β : Type} → α → β → α × β :=
@(α ==> @(β ==> a ==> b ==> (a, b)))

def tst3b : {α : Type} → {β : Type} → α → β → α × β :=
{α} ==> {β} ==> a ==> b ==> (a, b)

syntax "function" (term:max)+ "=>" term : term

macro_rules
| `(function $xs* => $b) => `(@(fun $xs* => $b))

def tst4 : {α : Type} → {β : Type} → α → β → α × β :=
function α β a b => (a, b)

theorem simple20 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by intros h1 h2 h3;
   try clear x; -- should fail
   clear h2;
   trace_state;
   apply Eq.trans;
   exact h3;
   exact h1

theorem simple21 (x y z : Nat) : y = z → x = x → y = x → x = z :=
fun h1 _ h3 =>
  have : x = y := by { apply Eq.symm; assumption };
  Eq.trans this (by assumption)

theorem simple22 (x y z : Nat) : y = z → y = x → id (x = z + 0) :=
fun h1 h2 => show x = z + 0 by
  apply Eq.trans
  exact h2.symm
  assumption
  skip

theorem simple23 (x y z : Nat) : y = z → x = x → y = x → x = z :=
fun h1 _ h3 =>
  have : x = y := by apply Eq.symm; assumption
  Eq.trans this (by assumption)

theorem simple24 (x y z : Nat) : y = z → x = x → y = x → x = z :=
fun h1 _ h3 =>
  have h : x = y := by apply Eq.symm; assumption
  Eq.trans h (by assumption)

def f1 (x : Nat) : Nat :=
  let double x := x + x
  let rec loop x :=
    match x with
    | 0   => 0
    | x+1 => loop x + double x
  loop x

#eval f1 5

def f2 (x : Nat) : String :=
  let bad x : String := toString x
  bad x

def f3 x y :=
  x + y + 1

theorem f3eq x y : f3 x y = x + y + 1 :=
  rfl

def f4 (x y : Nat) : String :=
  if x > y + 1 then "hello" else "world"
