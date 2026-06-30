set_option trace.compiler.ir.result true

-- All generated case and ctor instructions should use the _impl version

inductive Exp
  | var (i : UInt32)
  | app (a b : Exp)
  | a1
  | a2
  | a3
  | a4
  | a5
with
  @[computed_field] hash : Exp → UInt64
    | .var i => Hashable.hash i + 1000
    | .app a b => mixHash (hash a) (hash b)
    | _ => 42

def f := Exp.hash (.app (.var 10) .a4)

-- should use 'default →' case
def g : Exp → Bool
  | .a3 => true
  | _ => false

-- using the same matcher as in the computed field should work
def hash' : Exp → Nat
  | .var i => i.toNat
  | .app a b => hash' a + hash' b
  | _ => 42

-- should not invoke Exp.var._override
def getAppFn : Exp → Exp
  | .app f _ => getAppFn f
  | e => e

-- should not call Exp.app._override
def Exp.f (e : Exp) : Exp :=
   match app e e with
   | var _ => e
   | app a _ => getAppFn a
   | e => e
