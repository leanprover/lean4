import Std

set_option warn.sorry false
open Std

section DHashMapModel

variable (α : Type u) (β : α → Type v) [BEq α] [Hashable α]

structure DHashMapModel : Type (max u v) where
  shape : DHashMap α (fun _ => Unit)
  keys : Fin shape.size → α
  data : (i : Fin shape.size) → β (keys i)

variable {α} {β}

-- We never want to run the code below, so mark it as `noncomputable`

noncomputable def DHashMapModel.ofDHashMap (m : DHashMap α β) : DHashMapModel α β where
  shape := m.map fun _ _ => ()
  keys := sorry
  data := sorry

noncomputable def DHashMapModel.toDHashMap (m : DHashMapModel α β) : DHashMap α β := sorry

theorem DHashMapModel.ofDHashMap_toDHashMap (m : DHashMap α β) : toDHashMap (ofDHashMap m) = m := by
  sorry

theorem DHashMapModel.toDHashMap_ofDHashMap (m : DHashMap α β) : toDHashMap (ofDHashMap m) = m := by
  sorry

end DHashMapModel

section DHashMap'

variable (α : Type u) (β : α → Type v) [BEq α] [Hashable α]

structure DHashMap' : Type (max u v) where mk ::
  toDHashMapModel : DHashMapModel α β

variable {α} {β}

unsafe def DHashMap'.ofDHashMapImpl (m : DHashMap α β) : DHashMap' α β := unsafeCast m
@[implemented_by DHashMap'.ofDHashMapImpl]
def DHashMap'.ofDHashMap (m : DHashMap α β) : DHashMap' α β := ⟨DHashMapModel.ofDHashMap m⟩

unsafe def DHashMap'.toDHashMapImpl (m : DHashMap' α β) : DHashMap α β := unsafeCast m
@[implemented_by DHashMap'.toDHashMapImpl]
def DHashMap'.toDHashMap (m : DHashMap' α β) : DHashMap α β := m.toDHashMapModel.toDHashMap

noncomputable
def DHashMap'.toDHashMapModelImpl (m : DHashMap' α β) : DHashMapModel α β := .ofDHashMap m.toDHashMap
noncomputable
def DHashMap'.ofDHashMapModelImpl (m : DHashMapModel α β) : DHashMap' α β := ofDHashMap m.toDHashMap

-- Now register these implementations for constructor and the projection
-- (I guess since we marked them as noncomputable, this means that they will never be run? Good!)
attribute [implemented_by DHashMap'.mk] DHashMap'.ofDHashMapModelImpl
attribute [implemented_by DHashMap'.toDHashMapModel] DHashMap'.toDHashMapModelImpl

end DHashMap'

section Operations

variable {α : Type u} {β : α → Type v} {γ : α → Type w} [BEq α] [Hashable α]

def DHashMap'.emptyWithCapacity (capacity : Nat := 8) : DHashMap' α β :=
  DHashMap'.ofDHashMap <| .emptyWithCapacity capacity

def DHashMap'.map (f : ∀ x, β x → γ x) (m : DHashMap' α β) : DHashMap' α γ :=
  DHashMap'.ofDHashMap <| m.toDHashMap.map f

def DHashMap'.insert (k : α) (v : β k) (m : DHashMap' α β) : DHashMap' α β :=
  DHashMap'.ofDHashMap <| m.toDHashMap.insert k v

instance : EmptyCollection (DHashMap' α β) where
  emptyCollection := DHashMap'.emptyWithCapacity

instance [Repr α] [∀ x, Repr (β x)]: Repr (DHashMap' α β) where
  reprPrec m p := reprPrec m.toDHashMap p

end Operations

-- Nested recursion works!
structure Tree (α : Type u) : Type u where
  val : α
  cs : DHashMap' String (fun _ => Tree α)

/--
info: { val := "root",
  cs := Std.DHashMap.ofList [⟨"child2", { val := "child2", cs := Std.DHashMap.ofList [] }⟩,
         ⟨"child1", { val := "child1", cs := Std.DHashMap.ofList [] }⟩] }
-/
#guard_msgs in
#eval! Tree.mk "root" (({} : DHashMap' _ _).insert "child1" (Tree.mk "child1" {}) |>.insert "child2" (Tree.mk "child2" {}))



section Size

-- Before we can define functions by well-founded recursion that nests through `DHashMap'`
-- we need to be able to define a size function on such types, by structural recursion.
-- We give a generic definition for `DHashMapModel' with a definition we can replicate
-- for the mutual structural recursion.

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α]

noncomputable def DHashMapModel.sizeOf (sizeOf : ∀ x, β x → Nat) (m : DHashMapModel α β) : Nat :=
  (List.ofFn (fun i => sizeOf (m.keys i) (m.data i))).sum

noncomputable instance [∀ x, SizeOf (β x)] : SizeOf (DHashMapModel α β) where
  sizeOf := DHashMapModel.sizeOf (fun _ => SizeOf.sizeOf)

noncomputable def DHashMap'.sizeOf [∀ x, SizeOf (β x)] (m : DHashMap' α β) : Nat :=
  m.toDHashMapModel.sizeOf (fun _ => SizeOf.sizeOf)

noncomputable instance [∀ x, SizeOf (β x)] : SizeOf (DHashMap' α β) where
  sizeOf := DHashMap'.sizeOf

end Size

-- Now the size on trees. We have three motives in the recursor:
-- (Would be good if we can have nested structural recursion, i.e. automate that part)

-- Or to address
-- the TODO: add support for finite domains
-- in private partial def ignoreFieldType (type : Expr) : MetaM Bool := do
-- in the SizeOf deriving handler

/--
info: Tree.rec.{u_1, u} {α : Type u} {motive_1 : Tree α → Sort u_1} {motive_2 : (DHashMap' String fun x => Tree α) → Sort u_1}
  {motive_3 : (DHashMapModel String fun x => Tree α) → Sort u_1}
  (mk : (val : α) → (cs : DHashMap' String fun x => Tree α) → motive_2 cs → motive_1 { val := val, cs := cs }) :
  ((toDHashMapModel : DHashMapModel String fun x => Tree α) →
      motive_3 toDHashMapModel → motive_2 { toDHashMapModel := toDHashMapModel }) →
    ((shape : DHashMap String fun x => Unit) →
        (keys : Fin shape.size → String) →
          (data : (i : Fin shape.size) → (fun x => Tree α) (keys i)) →
            ((i : Fin shape.size) → motive_1 (data i)) → motive_3 { shape := shape, keys := keys, data := data }) →
      (t : Tree α) → motive_1 t
-/
#guard_msgs in
#check Tree.rec

mutual
def Tree.sizeOf [SizeOf α] : (t : Tree α) → Nat
  | ⟨val, cs⟩ => 1 + SizeOf.sizeOf val + sizeOf_aux1 cs
termination_by structural t => t

def Tree.sizeOf_aux1 [SizeOf α] : (m : DHashMap' String (fun _ => Tree α)) → Nat
  | ⟨m⟩ => Tree.sizeOf_aux2 m

def Tree.sizeOf_aux2 [SizeOf α] : (m : DHashMapModel String (fun _ => Tree α)) → Nat
  | ⟨_shape, _keys, data⟩ => (List.ofFn (fun i => Tree.sizeOf (data i))).sum
end

instance [SizeOf α] : SizeOf (Tree α) where
  sizeOf := Tree.sizeOf

theorem Tree.sizeOf_eq [SizeOf α] : (t : Tree α) →
  SizeOf.sizeOf t = 1 + SizeOf.sizeOf t.val + SizeOf.sizeOf t.cs := by
  refine Tree.rec
    (motive_1 := fun t => _)
    (motive_2 := fun cs => sizeOf_aux1 cs = SizeOf.sizeOf cs)
    (motive_3 := fun m => sizeOf_aux2 m = SizeOf.sizeOf m)
    (fun val cs ih => by simp [*, SizeOf.sizeOf, Tree.sizeOf])
    (fun m ih => ih)
    (fun shape data ih => by simp [*, SizeOf.sizeOf, DHashMapModel.sizeOf, sizeOf_aux2])

@[simp]
theorem Tree.sizeOf_eq' [SizeOf α] :
    SizeOf.sizeOf (⟨v , c⟩ : Tree α) = 1 + SizeOf.sizeOf v + SizeOf.sizeOf c :=
  Tree.sizeOf_eq _


-- We now also need something to thread the size through `map`

section Attach

variable {α : Type u} {β : α → Type v} {γ : α → Type w} [BEq α] [Hashable α] [∀ x, SizeOf (β x)]

def DHashMap'.mapWithSize (m : DHashMap' α β)
  (f : (x : α) → (y : β x) → SizeOf.sizeOf y < SizeOf.sizeOf m → γ x) : DHashMap' α γ :=
  sorry

@[wf_preprocess]
theorem DHashMap'.map_eq_mapWithSize (m : DHashMap' α β) (f : (x : α )→ β x → γ x) :
  m.map f = m.mapWithSize (fun a x h => f a x) := by
  sorry

end Attach

section Tree

-- Now nested termination just works!

def Tree.map (f : α → β) : (t : Tree α) → Tree β
  | ⟨val, cs⟩ => ⟨f val, cs.map (fun _ t => t.map f)⟩
termination_by t => t

end Tree


-- Can we lift this to HashMap?

section


structure HashMap' (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  inner : DHashMap' α (fun _ => β)

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

noncomputable def HashMap'.sizeOf [SizeOf β] (m : HashMap' α β) : Nat :=
  SizeOf.sizeOf m.inner

noncomputable instance [SizeOf β] : SizeOf (HashMap' α β) where
  sizeOf := HashMap'.sizeOf

def HashMap'.emptyWithCapacity (capacity : Nat := 8) : HashMap' α β :=
  .mk <| .emptyWithCapacity capacity

def HashMap'.map (f : α → β → γ) (m : HashMap' α β) : HashMap' α γ :=
  .mk <| m.inner.map f

def HashMap'.insert (k : α) (v : β) (m : HashMap' α β) : HashMap' α β :=
  .mk <| m.inner.insert k v

def HashMap'.mapWithSize [SizeOf β] (m : HashMap' α β)
  (f : (x : α) → (y : β) → SizeOf.sizeOf y < SizeOf.sizeOf m → γ) : HashMap' α γ :=
  .mk <| m.inner.mapWithSize f

@[wf_preprocess]
theorem HashMap'.map_eq_mapWithSize [SizeOf β] (m : HashMap' α β) (f : (x : α) → β → γ) :
  m.map f = m.mapWithSize (fun a x h => f a x) := by
  sorry

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]


end

set_option genSizeOf false -- buggy

structure Tree' (α : Type u) : Type u where
  val : α
  cs : HashMap' String (Tree' α)

section SizeOf -- this can hopefully be automated

mutual
def Tree'.sizeOf [SizeOf α] : (t : Tree' α) → Nat
  | ⟨val, cs⟩ => 1 + SizeOf.sizeOf val + sizeOf_aux3 cs
termination_by structural t => t

def Tree'.sizeOf_aux1 [SizeOf α] : (m : DHashMap' String (fun _ => Tree' α)) → Nat
  | ⟨m⟩ => Tree'.sizeOf_aux2 m

def Tree'.sizeOf_aux2 [SizeOf α] : (m : DHashMapModel String (fun _ => Tree' α)) → Nat
  | ⟨_shape, _keys, data⟩ => (List.ofFn (fun i => Tree'.sizeOf (data i))).sum

def Tree'.sizeOf_aux3 [SizeOf α] : (m : HashMap' String (Tree' α)) → Nat
  | ⟨m⟩ => Tree'.sizeOf_aux1 m

end

instance [SizeOf α] : SizeOf (Tree' α) where
  sizeOf := Tree'.sizeOf

theorem Tree'.sizeOf_eq [SizeOf α] : (t : Tree' α) →
  SizeOf.sizeOf t = 1 + SizeOf.sizeOf t.val + SizeOf.sizeOf t.cs := by
  refine Tree'.rec
    (motive_1 := fun t => _)
    (motive_2 := fun cs => sizeOf_aux3 cs = SizeOf.sizeOf cs)
    (motive_3 := fun cs => sizeOf_aux1 cs = SizeOf.sizeOf cs)
    (motive_4 := fun m => sizeOf_aux2 m = SizeOf.sizeOf m)
    (fun val cs ih => by simp [*, SizeOf.sizeOf, Tree'.sizeOf])
    (fun m ih => by simp [*, sizeOf_aux3, SizeOf.sizeOf, HashMap'.sizeOf])
    (fun m ih => ih)
    (fun shape data ih => by simp [*, SizeOf.sizeOf, DHashMapModel.sizeOf, sizeOf_aux2])

@[simp]
theorem Tree'.sizeOf_eq' [SizeOf α] :
    SizeOf.sizeOf (⟨v , c⟩ : Tree' α) = 1 + SizeOf.sizeOf v + SizeOf.sizeOf c :=
  Tree'.sizeOf_eq _


end SizeOf

def Tree'.map (f : α → β) : (t : Tree' α) → Tree' β
  | ⟨val, cs⟩ => ⟨f val, cs.map (fun _ t => t.map f)⟩
termination_by t => t
