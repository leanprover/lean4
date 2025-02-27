inductive Foo {f: Nat}: {d: Nat} → (h: d ≤ f) → Type where
| foo : Foo (Nat.zero_le _) → (Bool → Foo h) → Foo h

set_option trace.Elab.definition.structural true

/--
error: fail to show termination for
  Foo.bar
with errors
failed to infer structural recursion:
Not considering parameter d of Foo.bar:
  it is unchanged in the recursive calls
Not considering parameter f of Foo.bar:
  it is unchanged in the recursive calls
Not considering parameter h of Foo.bar:
  it is unchanged in the recursive calls
Not considering parameter #4 of Foo.bar:
  its type Foo is an inductive family
    Foo h
  and index
    h
  depends on the non index
    f
no parameters suitable for structural recursion

failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
d f✝ : Nat
h h✝ : d ≤ f✝
a✝ : Foo ⋯
f : Bool → Foo h✝
⊢ sizeOf (f true) < 1 + d + sizeOf a✝
-/
#guard_msgs in
def Foo.bar (h: d ≤ f): Foo h → Foo h
| foo _ f => (f true).bar h
