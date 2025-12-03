module
opaque R : Nat → Nat → Prop

@[grind ->]
axiom Rtrans {x y z : Nat} : R x y → R y z → R x z

@[grind →]
axiom Rtrans' {x y z : Nat} : R x y → R y z → R x z

@[grind <-]
axiom Rsymm {x y : Nat} : R x y → R y x

@[grind ←]
axiom Rsymm' {x y : Nat} : R x y → R y x

example : R a b → R b c → R d c → R a d := by
  grind only [-> Rtrans, <- Rsymm]

example : R a b → R b c → R d c → R a d := by
  grind only [→ Rtrans, ← Rsymm]


opaque State : Type
opaque State.le (σ₁ σ₂ : State) : Prop
axiom State.update : State → Nat → Nat → State
opaque Expr : Type
opaque Expr.eval : Expr → State → Nat
axiom Expr.constProp : Expr → State → Expr


/-- trace: [grind.ematch.pattern] eval_constProp_of_sub: [State.le #3 #2, constProp #1 #3] -/
#guard_msgs (trace) in
set_option trace.grind.ematch.pattern true in
@[grind! =>] theorem Expr.eval_constProp_of_sub (e : Expr) (h : State.le σ' σ) : (e.constProp σ').eval σ = e.eval σ :=
  sorry

/-- trace: [grind.ematch.pattern] eval_constProp_of_eq_of_sub: [State.le #3 #2, constProp #1 #3] -/
#guard_msgs (trace) in
set_option trace.grind.ematch.pattern true in
@[grind! =>] theorem Expr.eval_constProp_of_eq_of_sub {e : Expr} (h₂ : State.le σ' σ) : (e.constProp σ').eval σ = e.eval σ :=
  sorry

/-- trace: [grind.ematch.pattern] update_le_update: [le #4 #3, update #4 #2 #1] -/
#guard_msgs (trace) in
set_option trace.grind.ematch.pattern true in
@[grind! =>] theorem State.update_le_update (h : State.le σ' σ) : State.le (σ'.update x v) (σ.update x v) :=
  sorry


namespace Foo

/-- info: Rtrans: [R #4 #3, R #3 #2] -/
#guard_msgs (info) in
@[grind? ->]
axiom Rtrans {x y z : Nat} : R x y → R y z → R x z

/-- info: Rtrans': [R #4 #3, R #3 #2] -/
#guard_msgs (info) in
@[grind? →]
axiom Rtrans' {x y z : Nat} : R x y → R y z → R x z

end Foo
