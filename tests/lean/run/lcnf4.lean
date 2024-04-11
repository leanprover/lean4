import Lean


partial def foo (n : Nat) : Nat := Id.run do
  if n == 10 then return 0
  foo (n+1)

partial def bar (n : Nat) : Nat := Id.run do
  if n == 10 then 0 else
  bar (n+1)

#print foo._unsafe_rec

#eval Lean.Compiler.compile #[``foo]

def xyz : BaseIO UInt32 := do
  let ref ← IO.mkRef 42
  ref.set 10
  ref.get

-- set_option trace.compiler.simp true in
#eval Lean.Compiler.compile #[``xyz]

@[extern "f_imp"]
opaque f : Nat → Nat

@[extern "g_imp"]
opaque g : Nat → Nat → Nat → Nat

inductive Ty where
  | c1 | c2 | c3 | c4 | c5

def bla (ty : Ty) :=
  match ty with
  | .c1 => true
  | _ => true

#eval Lean.Compiler.compile #[``bla]

def boo (ty ty' : Ty) (a b : Nat) :=
  let d := match ty with
  | .c1 => f b + f a + f (a+1) + f (a*2) + f (a*3)
  | _ => f (b+1) + f b + f a
  let e := match ty' with
  | .c2 => f a * f (b+1) + f (a*2) + f (a*3)
  | _ => f b * f (b + 1) + f (a*2) + f (a*3)
  g e d e + g d d d

-- set_option trace.compiler.simp.step true in
-- set_option trace.compiler.simp.inline true in
-- set_option trace.compiler.simp.inline.stats true in
-- set_option trace.compiler.simp true in
#eval Lean.Compiler.compile #[``boo]

def f' (x y : Nat) :=
  let s := (x, y)
  let y := s.2
  y + s.2

-- set_option trace.compiler.simp true in
#eval Lean.Compiler.compile #[``f']

#eval Lean.Compiler.compile #[``Lean.Meta.isExprDefEqAuxImpl]

set_option trace.Meta.debug true
set_option trace.compiler true
#eval Lean.Compiler.compile #[``Lean.MetavarContext.MkBinding.collectForwardDeps]
