def x := 1

new_frontend

#check x

variables {α : Type}

def f (a : α) : α :=
a

def tst (xs : List Nat) : Nat :=
xs.foldl (init := 10) (· + ·)

#check tst [1, 2, 3]

#check tst

#check (fun stx => if True then let e := stx; HasPure.pure e else HasPure.pure stx : Nat → Id Nat)

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
begin
  assumption
end

theorem simple2 (x y : Nat) : x = y → x = y :=
begin
  intro h;
  assumption
end

syntax "intro2" : tactic

macro_rules
| `(tactic| intro2) => `(tactic| intro; intro )

theorem simple3 (x y : Nat) : x = x → x = y → x = y :=
begin
  intro2;
  assumption
end

macro intro3 : tactic => `(intro; intro; intro)
macro check2 x:term : command => `(#check $x #check $x)
macro foo x:term "," y:term : term => `($x + $y + $x)

set_option pp.all false

check2 0+1
check2 foo 0,1

theorem simple4 (x y : Nat) : y = y → x = x → x = y → x = y :=
begin
  intro3;
  assumption
end

theorem simple5 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intro h1; intro _; intro h3;
  exact Eq.trans h3 h1
end

theorem simple6 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intro h1; intro _; intro h3;
  refine Eq.trans _ h1;
  assumption
end

theorem simple7 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intro h1; intro _; intro h3;
  refine Eq.trans ?pre ?post;
  exact y;
  { exact h3 };
  { exact h1 }
end

theorem simple8 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intro h1; intro _; intro h3;
  refine Eq.trans ?pre ?post;
  case post { exact h1 };
  case pre { exact h3 };
end

theorem simple9 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intros h1 _ h3;
  traceState;
  { refine Eq.trans ?pre ?post;
    (exact h1) <|> (exact y; exact h3; assumption) }
end

namespace Foo
  def Prod.mk := 1
  #check (⟨2, 3⟩ : Prod _ _)
end Foo

theorem simple10 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intro h1; intro h2; intro h3;
  skip;
  apply Eq.trans;
  exact h3;
  assumption
end

theorem simple11 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intro h1; intro h2; intro h3;
  apply @Eq.trans;
  traceState;
  exact h3;
  assumption
end

macro try t:tactic : tactic => `($t <|> skip)

syntax "repeat" tactic : tactic
macro_rules
| `(tactic| repeat $t) => `(tactic| try ($t; repeat $t))


theorem simple12 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intro h1; intro h2; intro h3;
  apply @Eq.trans;
  try exact h1; -- `exact h1` fails
  traceState;
  try exact h3;
  traceState;
  try exact h1;
end

theorem simple13 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intros h1 h2 h3;
  traceState;
  apply @Eq.trans;
  case main.b exact y;
  traceState;
  repeat assumption
end

theorem simple14 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intros;
  apply @Eq.trans;
  case main.b exact y;
  repeat assumption
end

theorem simple15 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intros h1 h2 h3;
  revert y;
  intros y h1 h3;
  apply Eq.trans;
  exact h3;
  exact h1
end

theorem simple16 (x y z : Nat) : y = z → x = x → x = y → x = z :=
begin
  intros h1 h2 h3;
  try (clear x); -- should fail
  clear h2;
  traceState;
  apply Eq.trans;
  exact h3;
  exact h1
end

macro "blabla" : tactic => `(assumption)

-- Tactic head symbols do not become reserved words
def blabla := 100

#check blabla

theorem simple17 (x : Nat) (h : x = 0) : x = 0 :=
begin blabla end

theorem tstprec1 (x y z : Nat) : x + y * z = x + (y * z) :=
rfl

theorem tstprec2 (x y z : Nat) : y * z + x = (y * z) + x :=
rfl

#check fun {α} (a : α) => a
#check fun {α} [HasAdd α] (a : α) => a + a

def g1 {α} (a₁ a₂ : α) {β} (b : β) : α × α × β :=
(a₁, a₂, b)

#check @(g1 true)

set_option trace.Elab.definition true

def id1 : {α : Type} → α → α :=
fun x => x

def listId : List ({α : Type} → α → α) :=
(fun x => x) :: []

def altTst {m σ} [Alternative m] [Monad m] : Alternative (StateT σ m) :=
⟨StateT.failure, StateT.orelse⟩

#exit

def id2 : {α : Type} → α → α :=
fun {α} x => _
