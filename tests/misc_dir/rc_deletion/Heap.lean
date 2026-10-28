import Graph
import Init.System.Deletion

/-!
The object operations of `Lean.Runtime.Deletion` on the ownership graph of `Graph.lean`.

`adapter g l` defines the operations that the cascade of `Init/System/Deletion.lean` is written
over, on a heap with one header cell per object. The cell holds a count until the object loses its
last reference, and the object's worklist link once it is queued, so that a link overwrites the
count as it does in the runtime. Slots are read through cursors into a `Layout`, and every pointer
a slot holds is the reference of one field occurrence of the graph. Reading the slot hands that
reference to the release in progress, which is when its ownership token leaves the heap.

The operations also record a fault whenever an access breaks the protocol of the runtime's heap: a
count read or adjusted after its object lost its last reference, a link written to an object that
was not just released or read from one that is not queued, a kind read twice, a slot read out of
range, from the wrong kind of object or after the object was freed, a pointer slot whose reference
was already released, `NULL` in a slot that cannot hold it, an object freed by the wrong terminal
effect or before all of its references were released, and an invalid tag. The fault is recorded
and the access proceeds.

`collect` releases a root as `lean_dec_ref` does: `decRef` of `rc_model` decides whether the
reference was the last, and the cascade then deletes. `Refinement.lean` proves what it does.

The runtime's operations are trusted to act as these do: in particular that a link keeps an
object's kind, and that the layout is fixed. Tasks, promises and external objects are leaves here:
what their terminal effects release, the runtime deletes in cascades of their own. Other threads and
memory ordering are not modelled; the atomic increment is one step.
-/

namespace RcGraph

open Lean.Runtime.Deletion

variable {α : Type} {objects roots fields : Nat}

/-! ## The heap -/

/-- A member of an object as its layout stores it: a slot, or a member of a thunk or `Ref`. -/
inductive Member (fields : Nat) where
  /-- A pointer that holds the reference of field occurrence `f`. -/
  | field (f : Fin fields)
  /-- An immediate, which holds no reference. -/
  | scalar
  /-- `NULL`, valid only as a member of a thunk or `Ref`. -/
  | null
  deriving DecidableEq, Repr

/-- The field occurrence whose reference a member holds. -/
def Member.field? : Member fields → Option (Fin fields)
  | .field f => some f
  | _ => none

/-- Each object's kind and members, in the order the cascade reads them. -/
structure Layout (objects fields : Nat) where
  tag : Fin objects → UInt8
  members : Fin objects → List (Member fields)

/-- Whether `tag` is a kind with slots: constructors, closures and arrays. -/
def hasSlots (tag : UInt8) : Bool :=
  tag ≤ LeanMaxCtorTag || tag == LeanClosure || tag == LeanArray

/--
The members of an object of kind `tag` that the cascade reads: slots that never hold `NULL`, a
thunk's closure and value, a `Ref`'s value, or none at all. `LeanStructArray` and `LeanReserved`
objects do not exist.
-/
def shapeOk (tag : UInt8) (ms : List (Member fields)) : Bool :=
  if hasSlots tag then !ms.contains .null
  else if tag == LeanThunk then ms.length == 2
  else if tag == LeanRef then ms.length == 1
  else if tag == LeanStructArray || tag == LeanReserved then false
  else ms.isEmpty

/--
Every object's members hold its field occurrences in order and fit its kind, and its slots can be
counted in a `USize`.
-/
def Layout.Valid (l : Layout objects fields) (g : Graph α objects roots fields) : Prop :=
  ∀ o, (l.members o).filterMap Member.field? = g.children o ∧ shapeOk (l.tag o) (l.members o) ∧
    (l.members o).length < USize.size

/-- `lean_object *` on the graph: a pointer to an object, an immediate, or `NULL`. -/
inductive Val (objects : Nat) where
  | obj (o : Fin objects)
  | scalar
  | null
  deriving DecidableEq, Repr

/--
An object's header: its count, or its worklist link once it is queued. The other states record how
far the deletion of an object that has lost its last reference has come.
-/
inductive Cell (objects : Nat) where
  /-- A count. -/
  | live (rc : Int32)
  /-- This thread is responsible for deleting the object, which is not queued: the count read one,
  or the atomic increment returned minus one. -/
  | last
  /-- Queued, linked to `next`; the link has replaced the count. -/
  | queued (next : Val objects)
  /-- Its kind has been read, so it is being deleted. -/
  | visited
  /-- Reclaimed. -/
  | freed
  deriving DecidableEq, Repr

/-- The count a cell holds. -/
def Cell.rc : Cell objects → Option Int32
  | .live rc => some rc
  | _ => none

@[simp] theorem Cell.rc_live (rc : Int32) : (Cell.live rc : Cell objects).rc = some rc := rfl
@[simp] theorem Cell.rc_last : (Cell.last : Cell objects).rc = none := rfl
@[simp] theorem Cell.rc_queued (next : Val objects) : (Cell.queued next).rc = none := rfl
@[simp] theorem Cell.rc_visited : (Cell.visited : Cell objects).rc = none := rfl
@[simp] theorem Cell.rc_freed : (Cell.freed : Cell objects).rc = none := rfl

/--
A heap of the graph: the ownership tokens still held, a header cell per object, the objects
reclaimed so far, the newest first, and whether an access broke the protocol.
-/
structure Heap (objects roots fields : Nat) where
  own : Ownership roots fields
  cell : Fin objects → Cell objects
  freed : List (Fin objects)
  fault : Bool := false

/-- The ownership state a heap stands for, given the worklist that its links spell. -/
def Heap.state (h : Heap objects roots fields) (todo : List (Fin objects)) :
    State objects roots fields :=
  { own := h.own, rc := fun o => (h.cell o).rc, todo, freed := h.freed }

/-- A heap for an ownership state with nothing queued; objects without a count are freed. -/
def Heap.ofState (s : State objects roots fields) : Heap objects roots fields :=
  { own := s.own, cell := fun o => (s.rc o).elim .freed .live, freed := s.freed }

def Heap.setCell (h : Heap objects roots fields) (o : Fin objects) (c : Cell objects) :
    Heap objects roots fields :=
  { h with cell := fun p => if p = o then c else h.cell p }

/-- Record a fault if `ok` fails. -/
def Heap.check (h : Heap objects roots fields) (ok : Bool) : Heap objects roots fields :=
  if ok then h else { h with fault := true }

abbrev M (objects roots fields : Nat) := StateM (Heap objects roots fields)

/-! ## The object operations -/

section Ops

variable (g : Graph α objects roots fields) (l : Layout objects fields)

/-- Whether `v` is `NULL` or points to a queued object, which a link may name. -/
def linkable (h : Heap objects roots fields) : Val objects → Bool
  | .null => true
  | .obj o => match h.cell o with | .queued _ => true | _ => false
  | .scalar => false

/-- `lean_del_get_rc`: reading one makes this thread responsible for the object. -/
def getRc : Val objects → M objects roots fields Int32
  | .obj o => fun h =>
    match h.cell o with
    | .live rc => (rc, if rc == 1 then h.setCell o .last else h)
    | _ => (0, h.check false)
  | _ => fun h => (0, h.check false)

/-- `lean_del_dec_rc`, on a count above one. -/
def decRc : Val objects → M objects roots fields Unit
  | .obj o => fun h =>
    match h.cell o with
    | .live rc => ((), (h.setCell o (.live (rc - 1))).check (rc > 1))
    | _ => ((), h.check false)
  | _ => fun h => ((), h.check false)

/-- `lean_del_release_mt`, an atomic increment of a thread-shared count. -/
def releaseMt : Val objects → M objects roots fields Int32
  | .obj o => fun h =>
    match h.cell o with
    | .live rc => (rc, (h.setCell o (if rc == -1 then .last else .live (rc + 1))).check (rc < 0))
    | _ => (0, h.check false)
  | _ => fun h => (0, h.check false)

/-- `lean_del_set_next`, which overwrites the header of an object that has just been released. -/
def setNext : Val objects → Val objects → M objects roots fields Unit
  | .obj o, next => fun h =>
    match h.cell o with
    | .last => ((), (h.setCell o (.queued next)).check (linkable h next))
    | _ => ((), h.check false)
  | _, _ => fun h => ((), h.check false)

/-- `lean_del_get_next`, on a queued object. -/
def getNext : Val objects → M objects roots fields (Val objects)
  | .obj o => fun h =>
    match h.cell o with
    | .queued next => (next, h)
    | _ => (.null, h.check false)
  | _ => fun h => (.null, h.check false)

/-- `lean_del_tag`, on an object this thread is responsible for and has not visited. -/
def readTag : Val objects → M objects roots fields UInt8
  | .obj o => fun h =>
    match h.cell o with
    | .last | .queued _ => (l.tag o, h.setCell o .visited)
    | _ => (l.tag o, h.check false)
  | _ => fun h => (LeanReserved, h.check false)

/-- Whether `o` is being deleted and of a kind `ok` accepts. -/
def visiting (h : Heap objects roots fields) (o : Fin objects) (ok : UInt8 → Bool) : Bool :=
  h.cell o == .visited && ok (l.tag o)

/-- The first slot of an object of a kind with slots. -/
def slots (ok : UInt8 → Bool) : Val objects → M objects roots fields (Val objects × Nat)
  | .obj o => fun h => ((.obj o, 0), h.check (visiting l h o ok))
  | v => fun h => ((v, 0), h.check false)

/-- The slot count of an object of a kind with slots. -/
def numSlots (ok : UInt8 → Bool) : Val objects → M objects roots fields USize
  | .obj o => fun h => (USize.ofNat (l.members o).length, h.check (visiting l h o ok))
  | _ => fun h => (0, h.check false)

/-- Take the reference that a member holds: the token leaves the heap. -/
def take (h : Heap objects roots fields) : Member fields → Val objects × Heap objects roots fields
  | .field f =>
    if Token.field f ∈ h.own then (.obj (g.target f), { h with own := h.own.erase (.field f) })
    else (.scalar, h.check false)
  | .scalar => (.scalar, h)
  | .null => (.null, h)

/-- `lean_del_get_slot` -/
def getSlot : Val objects × Nat → M objects roots fields (Val objects)
  | (.obj o, i) => fun h =>
    let h := h.check (visiting l h o hasSlots && i < (l.members o).length &&
      (l.members o)[i]? != some .null)
    match (l.members o)[i]? with
    | some m => take g h m
    | none => (.scalar, h)
  | _ => fun h => (.scalar, h.check false)

/-- `lean_del_thunk_closure`, `lean_del_thunk_value` and `lean_del_ref_value`. -/
def member (tag : UInt8) (i : Nat) : Val objects → M objects roots fields (Val objects)
  | .obj o => fun h =>
    let h := h.check (visiting l h o (· == tag) && i < (l.members o).length)
    match (l.members o)[i]? with
    | some m => take g h m
    | none => (.null, h)
  | _ => fun h => (.null, h.check false)

/-- Whether no member of `o` still holds a reference. -/
def released (h : Heap objects roots fields) (o : Fin objects) : Bool :=
  (l.members o).all fun m => match m with | .field f => !h.own.contains (.field f) | _ => true

/-- A terminal effect, which reclaims a visited object of a kind `ok` accepts. -/
def reclaim (ok : UInt8 → Bool) : Val objects → M objects roots fields Unit
  | .obj o => fun h =>
    ((), { (h.setCell o .freed).check (visiting l h o ok && released l h o) with
      freed := o :: h.freed })
  | _ => fun h => ((), h.check false)

/-- The object operations of the cascade on the graph. -/
abbrev adapter : Ops (M objects roots fields) (Val objects) (Val objects × Nat) where
  isScalar v := v == .scalar
  isNull v := v == .null
  null := .null
  getRc := getRc
  decRc := decRc
  releaseMt := releaseMt
  setNext := setNext
  getNext := getNext
  tag := readTag l
  ctorObjs := slots l (· ≤ LeanMaxCtorTag)
  ctorNumObjs := numSlots l (· ≤ LeanMaxCtorTag)
  closureFixed := slots l (· == LeanClosure)
  closureNumFixed := numSlots l (· == LeanClosure)
  arrayElems := slots l (· == LeanArray)
  arraySize := numSlots l (· == LeanArray)
  nextSlot c := (c.1, c.2 + 1)
  getSlot := getSlot g l
  thunkClosure := member g l LeanThunk 0
  thunkValue := member g l LeanThunk 1
  refValue := member g l LeanRef 0
  freeSmall := reclaim l fun t => t ≤ LeanMaxCtorTag || t == LeanThunk || t == LeanRef
  freeClosure := reclaim l (· == LeanClosure)
  freeArray := reclaim l (· == LeanArray)
  freeSarray := reclaim l (· == LeanScalarArray)
  freeString := reclaim l (· == LeanString)
  freeMpz := reclaim l (· == LeanMPZ)
  freeExternal := reclaim l (· == LeanExternal)
  deactivateTask := reclaim l (· == LeanTask)
  deactivatePromise := reclaim l (· == LeanPromise)
  unreachable _ := fun h => ((), h.check false)

end Ops

/-! ## Releasing a root -/

/--
`lean_dec_ref` on root `d`. The root's token leaves the heap, since its reference is the one the
caller releases. `decRef` of `rc_model` is the decision of `lean_dec_ref` and `lean_dec_ref_cold`
on the count; when the reference was the last, the cascade deletes the object.
-/
def decRoot (g : Graph α objects roots fields) (l : Layout objects fields)
    (s : State objects roots fields) (d : Fin roots) : Heap objects roots fields :=
  if Token.root d ∈ s.own then
    let h := Heap.ofState { s with own := s.own.erase (.root d) }
    match s.rc (g.root d) with
    | some rc =>
      match decRef rc with
      | some rc' => h.setCell (g.root d) (.live rc')
      | none => ((cascade (adapter g l) (.obj (g.root d))).run (h.setCell (g.root d) .last)).2
    | none => h
  else Heap.ofState s

/-- The ownership state after releasing root `d`. -/
def collect (g : Graph α objects roots fields) (l : Layout objects fields)
    (s : State objects roots fields) (d : Fin roots) : State objects roots fields :=
  (decRoot g l s d).state []

end RcGraph
