/-!
Tests for the `[override_runtime_type]` and `[compiled_cases]` attributes
-/

/-!
Defining the coinductive
```
coinductive Sequence (α : Type u) where
  | cons (head : α) (tail : Sequence α)
```
-/

@[override_runtime_type, ext]
structure Sequence (α : Type u) where
  get : Nat → α
deriving Nonempty

noncomputable def Sequence.consThunk {α : Type u} (head : α) (tail : Thunk (Sequence α)) : Sequence α where
  get | 0 => head | k + 1 => tail.get.get k

@[compiled_cases, elab_as_elim]
noncomputable def Sequence.casesOnImpl {α : Type u} {motive : Sequence α → Sort v} (t : Sequence α)
    (cons : (head : α) → (tail : Thunk (Sequence α)) → motive (.consThunk head tail)) :
    motive t :=
  haveI := cons (t.get 0) { get := fun n => t.get (n + 1) : Sequence α }
  cast ?_ this
where finally
  congr
  ext (_ | _) <;> rfl

@[inline]
def Sequence.head (seq : Sequence α) : α :=
  seq.casesOnImpl fun head _ => head

@[inline]
def Sequence.tail (seq : Sequence α) : Sequence α :=
  seq.casesOnImpl fun _ tail => tail.get

@[macro_inline]
def Sequence.cons (head : α) (tail : Sequence α) : Sequence α :=
  .consThunk head tail

def Sequence.take (seq : Sequence α) : Nat → List α
  | 0 => []
  | k + 1 => seq.head :: seq.tail.take k

noncomputable def Sequence.corec {α : Type u} {β : Sort v}
    (head : β → α) (tail : β → β) (init : β) : Sequence α where
  get := go init
where
  go (init : β) : Nat → α
    | 0 => head init
    | k + 1 => go (tail init) k

instance : Nonempty (Subtype (Eq a)) := ⟨a, rfl⟩

@[specialize]
partial def Sequence.corecPartial {α : Type u} {β : Sort v}
    (head : β → α) (tail : β → β) (init : β) : { res : Sequence α // corec head tail init = res } :=
  ⟨.cons (head init) (.corecPartial head tail (tail init)), ?_⟩
where finally
  have := (corecPartial head tail (tail init)).2
  rw [← this]
  ext (_ | _) <;> rfl

@[inline]
def Sequence.corecImpl {α : Type u} {β : Sort v}
    (head : β → α) (tail : β → β) (init : β) : Sequence α :=
  corecPartial head tail init

@[csimp]
theorem Sequence.corec_eq_corecImpl : @Sequence.corec = @Sequence.corecImpl := by
  funext α β head tail init
  apply Subtype.property

def Sequence.nats : Sequence Nat :=
  .corec id .succ 0

/-- info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] -/
#guard_msgs in #eval Sequence.nats.take 10

/-!
Defining `Shrink` in a computable way.
-/

structure Equiv (α : Sort u) (β : Sort v) where
  toFn : α → β
  invFn : β → α
  toFn_invFn (x : β) : toFn (invFn x) = x
  invFn_toFn (x : α) : invFn (toFn x) = x

attribute [simp] Equiv.toFn_invFn
attribute [simp] Equiv.invFn_toFn

def Equiv.refl (α : Type u) : Equiv α α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
def Equiv.ulift.{v} (α : Type u) : Equiv α (ULift.{v} α) :=
  ⟨ULift.up, ULift.down, fun _ => rfl, fun _ => rfl⟩
def Equiv.symm (x : Equiv α β) : Equiv β α := ⟨x.2, x.1, x.4, x.3⟩
def Equiv.trans (x : Equiv α β) (y : Equiv β γ) : Equiv α γ :=
  ⟨y.1 ∘ x.1, x.2 ∘ y.2, by simp, by simp⟩

class IsSmall.{v} (α : Type u) where
  exists_equiv (α) : ∃ β : Type v, Nonempty (Equiv α β)

class UnivLEHelper.{u, v} : Prop where
  isSmall (α : Type u) : IsSmall.{v} α

instance : UnivLEHelper.{u, u} where
  isSmall α := { exists_equiv := ⟨α, id, id, fun _ => rfl, fun _ => rfl⟩ }

class UnivLE.{u, v} : Prop where
  isSmall (α : Type u) : IsSmall.{v} α

instance [UnivLEHelper.{max u v, v}] : UnivLE.{u, v} where
  isSmall α := {
    exists_equiv := by
      obtain ⟨β, ⟨eqv⟩⟩ := UnivLEHelper.isSmall.{max u v, v} (ULift.{v} α)
      exact ⟨β, ⟨(Equiv.ulift α).trans eqv⟩⟩
  }

attribute [instance] UnivLE.isSmall

@[override_runtime_type]
structure Shrink.{v} (α : Type u) [IsSmall.{v} α] : Type v where
  mk' :: val' : (IsSmall.exists_equiv.{v} α).choose

noncomputable def Shrink.down.{v} {α : Type u} [IsSmall.{v} α] (x : α) : Shrink.{v} α :=
  .mk' <| (Classical.choice (IsSmall.exists_equiv.{v} α).choose_spec).toFn x

@[induction_eliminator, cases_eliminator, elab_as_elim]
noncomputable def Shrink.casesOnDown.{w, v} {α : Type u} [IsSmall.{v} α]
    {motive : Shrink.{v} α → Sort w} (t : Shrink α)
    (down : (x : α) → motive (Shrink.down x)) : motive t :=
  haveI := down <| (Classical.choice (IsSmall.exists_equiv.{v} α).choose_spec).invFn t.val'
  cast (by simp [Shrink.down]) this

@[simp]
theorem Shrink.casesOnDown_down.{w, v} {α : Type u} [IsSmall.{v} α]
    {motive : Shrink.{v} α → Sort w} (t : α)
    (down : (x : α) → motive (Shrink.down x)) :
    casesOnDown (.down t) down = down t := by
  apply eq_of_heq
  apply (cast_heq ..).trans
  congr
  simp [Shrink.down]

attribute [compiled_cases] Shrink.casesOnDown

def Shrink.up.{v} {α : Type u} [IsSmall.{v} α] (x : Shrink.{v} α) : α := x.casesOnDown id

/--
trace: [Compiler.result] size: 1
    def shrinkTest : UInt8 :=
      let _x.1 := 3;
      return _x.1
-/
#guard_msgs in
set_option trace.Compiler.result true in
def shrinkTest : Shrink.{0} UInt8 := .down 3

#guard shrinkTest.up == 3

/-!
`Shrink`s definition can not be exploited to jump across equivalences
-/

def natEquivInt : Equiv Nat Int where
  toFn x := if x % 2 = 0 then .ofNat (x / 2) else .negSucc (x / 2)
  invFn x := if x < 0 then 2 * x.natAbs - 1 else 2 * x.natAbs
  toFn_invFn := by grind
  invFn_toFn := by grind

/--
error: failed to compile definition, consider marking it as `noncomputable` because it depends on `Shrink.mk'`,
which had a special meaning to the compiler that was lost because of an inductive override
-/
#guard_msgs in
def convertShrink (x : Shrink Nat) : Shrink Int :=
  .mk' (cast ?_ x.val')
where finally
  congr
  ext α
  exact ⟨fun ⟨eqv⟩ => ⟨natEquivInt.symm.trans eqv⟩, fun ⟨eqv⟩ => ⟨natEquivInt.trans eqv⟩⟩

/-!
Defining an `Erased` type (not great, would really need some other compiler changes)
-/

@[override_runtime_type]
structure Erased (α : Sort u) where
  out : α

noncomputable def Erased.ofImpl {α : Sort u}
    (x : { f : α → Prop // ∃ x, f = Eq x }) : Erased α :=
  .mk x.2.choose

theorem Erased.ofImpl_eq {α : Sort u} (x : α) :
    Erased.ofImpl ⟨Eq x, x, rfl⟩ = .mk x := by
  have : ∃ y, Eq x = Eq y := Exists.intro x rfl
  have := this.choose_spec ▸ Eq.refl x
  rw [ofImpl, this]

noncomputable def Erased.casesOnImpl {α : Sort u} {motive : Erased α → Sort v}
    (t : Erased α) (ofImpl : ∀ f, motive (.ofImpl f)) : motive t :=
  cast ?_ (ofImpl ⟨Eq t.out, t.out, rfl⟩)
where finally rw [Erased.ofImpl_eq]

@[simp]
theorem Erased.casesOnImpl_ofImpl {α : Sort u} {motive : Erased α → Sort v}
    (x : _) (ofImpl : ∀ f, motive (.ofImpl f)) :
    casesOnImpl (.ofImpl x) ofImpl = ofImpl x := by
  obtain ⟨f, x, rfl⟩ := x
  apply eq_of_heq
  apply (cast_heq ..).trans
  congr
  rw [Erased.ofImpl_eq]

attribute [compiled_cases] Erased.casesOnImpl

@[macro_inline]
def Erased.mkImpl (x : α) : Erased α :=
  Erased.ofImpl ⟨Eq x, x, rfl⟩

@[csimp]
theorem Erased.mk_eq_mkImpl : @Erased.mk = @Erased.mkImpl := by
  funext α x
  symm
  apply Erased.ofImpl_eq

instance {α : Type u} : Repr (Erased α) where
  reprPrec _ _ := "Erased.mk _"

/-- info: Erased.mk _ -/
#guard_msgs in #eval Erased.mk (Classical.ofNonempty : Nat)

/--
error: failed to compile definition, consider marking it as `noncomputable` because it depends on `Erased.out`,
which had a special meaning to the compiler that was lost because of an inductive override
-/
#guard_msgs in #eval (Erased.mk (Classical.ofNonempty : Nat)).out

example : (Erased.mk (Classical.ofNonempty : Nat)).out = Classical.ofNonempty := rfl
