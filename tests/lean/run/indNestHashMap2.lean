import Std

set_option warn.sorry false
open Std

section HashMapModel

variable (α : Type u) (β : Type v) [BEq α] [Hashable α]

structure HashMapModel : Type (max u v) where
  shape : HashMap α Unit
  data : Fin shape.size → β

variable {α} {β}

-- We never want to run the code below, so mark it as `noncomputable`

noncomputable def HashMapModel.ofHashMap (m : HashMap α β) : HashMapModel α β where
  shape := m.map fun _ _ => ()
  data := sorry

noncomputable def HashMapModel.toHashMap (m : HashMapModel α β) : HashMap α β := sorry

theorem HashMapModel.ofHashMap_toHashMap (m : HashMap α β) : toHashMap (ofHashMap m) = m := by
  sorry

theorem HashMapModel.toHashMap_ofHashMap (m : HashMap α β) : toHashMap (ofHashMap m) = m := by
  sorry

end HashMapModel

section HashMap'

variable (α : Type u) (β : Type v) [BEq α] [Hashable α]

structure HashMap' : Type (max u v) where mk ::
  toHashMapModel : HashMapModel α β

variable {α} {β}

unsafe def HashMap'.ofHashMapImpl (m : HashMap α β) : HashMap' α β := unsafeCast m
@[implemented_by HashMap'.ofHashMapImpl]
def HashMap'.ofHashMap (m : HashMap α β) : HashMap' α β := ⟨HashMapModel.ofHashMap m⟩

unsafe def HashMap'.toHashMapImpl (m : HashMap' α β) : HashMap α β := unsafeCast m
@[implemented_by HashMap'.toHashMapImpl]
def HashMap'.toHashMap (m : HashMap' α β) : HashMap α β := m.toHashMapModel.toHashMap

noncomputable
def HashMap'.toHashMapModelImpl (m : HashMap' α β) : HashMapModel α β := .ofHashMap m.toHashMap
noncomputable
def HashMap'.ofHashMapModelImpl (m : HashMapModel α β) : HashMap' α β := ofHashMap m.toHashMap

-- Now register these implementations for constructor and the projection
-- (I guess since we marked them as noncomputable, this means that they will never be run? Good!)
attribute [implemented_by HashMap'.mk] HashMap'.ofHashMapModelImpl
attribute [implemented_by HashMap'.toHashMapModel] HashMap'.toHashMapModelImpl

end HashMap'

section Operations

variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]

def HashMap'.emptyWithCapacity (capacity : Nat := 8) : HashMap' α β :=
  HashMap'.ofHashMap <| .emptyWithCapacity capacity

def HashMap'.map (f : α → β → γ) (m : HashMap' α β) : HashMap' α γ :=
  HashMap'.ofHashMap <| m.toHashMap.map f

def HashMap'.insert (k : α) (v : β) (m : HashMap' α β) : HashMap' α β :=
  HashMap'.ofHashMap <| m.toHashMap.insert k v

instance : EmptyCollection (HashMap' α β) where
  emptyCollection := HashMap'.emptyWithCapacity

instance [Repr α] [Repr β ]: Repr (HashMap' α β) where
  reprPrec m p := reprPrec m.toHashMap p

end Operations

-- Nested recursion works!
structure Tree (α : Type u) : Type u where
  val : α
  cs : HashMap' String (Tree α)

/--
info: { val := "root",
  cs := Std.HashMap.ofList [("child2", { val := "child2", cs := Std.HashMap.ofList [] }),
         ("child1", { val := "child1", cs := Std.HashMap.ofList [] })] }
-/
#guard_msgs in
#eval! Tree.mk "root" (({} : HashMap' _ _).insert "child1" (Tree.mk "child1" {}) |>.insert "child2" (Tree.mk "child2" {}))



section Size

-- Before we can define functions by well-founded recursion that nests through `HashMap'`
-- we need to be able to define a size function on such types, by structural recursion.
-- We give a generic definition for `HashMapModel' with a definition we can replicate
-- for the mutual structural recursion.

variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]

noncomputable def HashMapModel.sizeOf (sizeOf : β → Nat) (m : HashMapModel α β) : Nat :=
  (List.ofFn (fun i => sizeOf (m.data i))).sum

noncomputable instance [SizeOf β] : SizeOf (HashMapModel α β) where
  sizeOf := HashMapModel.sizeOf SizeOf.sizeOf

noncomputable def HashMap'.sizeOf [SizeOf β] (m : HashMap' α β) : Nat :=
  m.toHashMapModel.sizeOf SizeOf.sizeOf

noncomputable instance [SizeOf β] : SizeOf (HashMap' α β) where
  sizeOf := HashMap'.sizeOf

end Size

-- Now the size on trees. We have three motives in the recursor:
-- (Would be good if we can have nested structural recursion, i.e. automate that part)

-- Or to address
-- the TODO: add support for finite domains
-- in private partial def ignoreFieldType (type : Expr) : MetaM Bool := do
-- in the SizeOf deriving handler

/--
info: Tree.rec.{u_1, u} {α : Type u} {motive_1 : Tree α → Sort u_1} {motive_2 : HashMap' String (Tree α) → Sort u_1}
  {motive_3 : HashMapModel String (Tree α) → Sort u_1}
  (mk : (val : α) → (cs : HashMap' String (Tree α)) → motive_2 cs → motive_1 { val := val, cs := cs }) :
  ((toHashMapModel : HashMapModel String (Tree α)) →
      motive_3 toHashMapModel → motive_2 { toHashMapModel := toHashMapModel }) →
    ((shape : HashMap String Unit) →
        (data : Fin shape.size → Tree α) →
          ((a : Fin shape.size) → motive_1 (data a)) → motive_3 { shape := shape, data := data }) →
      (t : Tree α) → motive_1 t
-/
#guard_msgs in
#check Tree.rec

mutual
def Tree.sizeOf [SizeOf α] : (t : Tree α) → Nat
  | ⟨val, cs⟩ => 1 + SizeOf.sizeOf val + sizeOf_aux1 cs
termination_by structural t => t

def Tree.sizeOf_aux1 [SizeOf α] : (m : HashMap' String (Tree α)) → Nat
  | ⟨m⟩ => Tree.sizeOf_aux2 m

def Tree.sizeOf_aux2 [SizeOf α] : (m : HashMapModel String (Tree α)) → Nat
  | ⟨_shape, data⟩ => (List.ofFn (fun i => Tree.sizeOf (data i))).sum
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
    (fun shape data ih => by simp [*, SizeOf.sizeOf, HashMapModel.sizeOf, sizeOf_aux2])

@[simp]
theorem Tree.sizeOf_eq' [SizeOf α] :
    SizeOf.sizeOf (⟨v , c⟩ : Tree α) = 1 + SizeOf.sizeOf v + SizeOf.sizeOf c :=
  Tree.sizeOf_eq _


-- We now also need something to thread the size through `map`

section Attach

variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α] [SizeOf β]

def HashMap'.mapWithSize (m : HashMap' α β)
  (f : α → (x : β) → SizeOf.sizeOf x < SizeOf.sizeOf m → γ) : HashMap' α γ :=
  sorry

@[wf_preprocess]
theorem HashMap'.map_eq_mapWithSize (m : HashMap' α β) (f : α → (x : β) → γ) :
  m.map f = m.mapWithSize (fun a x h => f a x) := by
  sorry

end Attach

section Tree

-- Now nested termination just works!

def Tree.map (f : α → β) : (t : Tree α) → Tree β
  | ⟨val, cs⟩ => ⟨f val, cs.map (fun _ t => t.map f)⟩
termination_by t => t

end Tree
