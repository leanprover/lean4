/-!
# `casesOn` for a proposition is built from projections

Proofs are opaque, so `I.casesOn` for a proposition must not go through `I.rec`: that only reduces
once the major premise is a constructor application, which a proof may never become.
-/

structure MyAnd (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

/--
info: @[reducible] def MyAnd.casesOn.{u} : {a b : Prop} →
  {motive : MyAnd a b → Sort u} → (t : MyAnd a b) → ((left : a) → (right : b) → motive ⋯) → motive t :=
fun {a b} {motive} t intro => intro ⋯ ⋯
-/
#guard_msgs in
#print MyAnd.casesOn

theorem opaqueProof : MyAnd (0 = 0) (1 = 1) := ⟨rfl, rfl⟩

-- Reduces even though the major premise is an opaque theorem
example : MyAnd.casesOn (motive := fun _ => Nat) opaqueProof (fun _ _ => 42) = 42 := rfl
example : MyAnd.recOn (motive := fun _ => Nat) opaqueProof (fun _ _ => 42) = 42 := rfl
example : (match opaqueProof with | ⟨_, _⟩ => 42) = 42 := rfl

-- Iota is unchanged
example (p : 0 = 0) (q : 1 = 1) (f : 0 = 0 → 1 = 1 → Nat) :
    MyAnd.casesOn (motive := fun _ => Nat) ⟨p, q⟩ f = f p q := rfl

-- Fields whose type depends on an earlier field are fine, by proof irrelevance
structure Dep : Prop where
  h1 : 0 = 0
  h2 : h1 = h1

/--
info: @[reducible] def Dep.casesOn.{u} : {motive : Dep → Sort u} →
  (t : Dep) → ((h1 : 0 = 0) → (h2 : h1 = h1) → motive ⋯) → motive t :=
fun {motive} t mk => mk ⋯ ⋯
-/
#guard_msgs in
#print Dep.casesOn

-- A proposition with a field that is not a proof has no projections, and keeps `rec`
inductive MyExists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : MyExists p

/--
info: @[reducible] def MyExists.casesOn.{u} : ∀ {α : Sort u} {p : α → Prop} {motive : MyExists p → Prop} (t : MyExists p),
  (∀ (w : α) (h : p w), motive ⋯) → motive t :=
fun {α} {p} {motive} t intro => MyExists.rec (fun w h => intro w h) t
-/
#guard_msgs in
#print MyExists.casesOn
