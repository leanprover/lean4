/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.ExternAttr

public section
/-!
Implements (extended) λPure and λRc proposed in the article
"Counting Immutable Beans", Sebastian Ullrich and Leonardo de Moura.

The Lean to IR transformation produces λPure code, and
this part is implemented in C++. The procedures described in the paper
above are implemented in Lean.
-/
namespace Lean.IR

/-- Function identifier -/
abbrev FunId := Name
abbrev Index := Nat
/-- Variable identifier -/
structure VarId where
  idx : Index
  deriving Inhabited, BEq, Hashable, Repr

/-- Join point identifier -/
structure JoinPointId where
  idx : Index
  deriving Inhabited, BEq, Hashable, Repr

abbrev Index.lt (a b : Index) : Bool := a < b

instance : ToString VarId := ⟨fun a => "x_" ++ toString a.idx⟩
instance : ToString JoinPointId := ⟨fun a => "block_" ++ toString a.idx⟩

/-- Low Level IR types. Most are self explanatory.

   - `usize` represents the C++ `size_t` Type. We have it here
      because it is 32-bit in 32-bit machines, and 64-bit in 64-bit machines,
      and we want the C++ backend for our Compiler to generate platform independent code.

   - `erased` for Lean types, propositions and proofs.

   - `object` a pointer to a value in the heap.

   - `tagged` a tagged pointer (i.e., the least significant bit is 1) storing a scalar value.

   - `tobject` an `object` or a `tagged` pointer

   - `void` is used to identify uses of the state token from `BaseIO` which do no longer need
     to be passed around etc. at this point in the pipeline.

   - `struct` and `union` are used for unboxed values that should be stored on the stack
     (e.g., `Option`, `Prod`, `Except`). Note that `struct` and `union` are stored boxed
     (i.e. as `lean_ctor_object`s) in the interpreter.

Remark: the RC operations for `tobject` are slightly more expensive because we
first need to test whether the `tobject` is really a pointer or not.

Remark: the Lean runtime assumes that `sizeof(void*) == sizeof(size_t)`.
Lean cannot be compiled on old platforms where this is not true.
-/
inductive IRType where
  | float | uint8 | uint16 | uint32 | uint64 | usize
  | erased | object | tobject
  | float32
  /--
  Unboxed structures representing a particular constructor of an inductive type.
  The type `objects[i]` is the type of `proj[0, i] x` where `x` is a value of this type, or more
  generally `proj[c, i]` when this type is the `c`-th constructor of a `union` type. Thus, the
  amount of `objects` should be exactly `CtorInfo.size` for the corresponding constructor.

  `usize` and `ssize` each are the number of `size_t` values and the amount of bytes spent by other
  scalars respectively and should be equivalent to the values in `CtorInfo.usize` and
  `CtorInfo.ssize` for the corresponding constructor.

  There are two different models of `struct` types: the interpreter model, which stores `struct`s
  as `lean_ctor_object`s that have their own reference count, and the compiled model, in which
  `struct`s are stored as corresponding C `struct`s and RC operations on a `struct` correspond to
  RC operations on every field.
  -/
  | struct (leanTypeName : Option Name)
    (objects : Array IRType) (usize ssize : Nat) : IRType
  /--
  Unboxed tagged unions of multiple IR types. Each type in `types` should be a `struct`
  corresponding to a constructor of the inductive type `leanTypeName`.
  -/
  | union (leanTypeName : Name) (types : Array IRType) : IRType
  -- TODO: Move this upwards after a stage0 update.
  | tagged
  | void
  deriving Inhabited, BEq, Repr

namespace IRType

def isScalar : IRType → Bool
  | float | float32 | uint8 | uint16 | uint32 | uint64 | usize => true
  | _ => false

def isObj : IRType → Bool
  | object | tagged | tobject | void => true
  | _ => false

def isStruct : IRType → Bool
  | struct _ _ _ _ | union _ _ => true
  | _ => false

def isObjOrStruct : IRType → Bool
  | object | tagged | tobject | void | struct .. | union .. => true
  | _ => false

def isScalarOrStruct : IRType → Bool
  | float | float32 | uint8 | uint16 | uint32 | uint64 | usize
  | struct _ _ _ _ | union _ _ => true
  | _ => false

def isPossibleRef : IRType → Bool
  | object | tobject | struct .. | union .. => true
  | _ => false

def isDefiniteRef : IRType → Bool
  | object => true
  | union _ tys => tys.all (!· matches struct _ #[] 0 0)
  | struct _ #[] 0 0 => false
  | struct .. => true
  | _ => false

def isErased : IRType → Bool
  | erased => true
  | _ => false

def isVoid : IRType → Bool
  | void => true
  | _ => false

/--
Returns `tagged`, `object` or `tobject` depending on whether the provided type is a definite
reference and/or a possible reference in boxed form. For details on boxing, see `Expr.box`.
-/
def boxed : IRType → IRType
  | object | float | float32 => object
  | void | erased | tagged | uint8 | uint16 => tagged
  | union _ tys => if tys.any (· matches struct _ #[] 0 0) then tobject else object
  | struct _ #[] 0 0 => tagged
  | struct .. => object
  | tobject | uint32 | uint64 | usize => tobject

/--
Normalize the object parts of the IR type, i.e. convert it into a type that is `compatibleWith` the
provided type but with all occurrences of `object` and `tagged` replaced by `tobject` and all
occurrences of `void` replaced by `erased`.
-/
def normalizeObject : IRType → IRType
  | object | tagged => tobject
  | struct nm tys us ss => struct nm (tys.map normalizeObject) us ss
  | union nm tys => union nm (tys.map normalizeObject)
  | void => erased
  | ty => ty

/--
Returns whether the two types have compatible representation, that is they are equal modulo
different reference types. If `strict` is `false` (default), object types (`object`, `tobject`,
`tagged`) are considered to be compatible with erased types (`erased`, `void`).
-/
partial def compatibleWith (a b : IRType) (strict : Bool := false) : Bool :=
  match a, b with
  | float, float => true
  | uint8, uint8 => true
  | uint16, uint16 => true
  | uint32, uint32 => true
  | uint64, uint64 => true
  | usize, usize => true
  | float32, float32 => true
  | erased, t | void, t =>
    (t matches erased | void) || (!strict && t matches object | tobject | tagged)
  | object, t | tobject, t | tagged, t =>
    (t matches object | tobject | tagged) || (!strict && t matches erased | void)
  | struct _ tys us ss, struct _ tys' us' ss' =>
    us == us' && ss == ss' && tys.isEqv tys' (compatibleWith (strict := true))
  | union _ tys, union _ tys' =>
    tys.isEqv tys' (compatibleWith (strict := false))
  | _, _ => false

end IRType

/-- Arguments to applications, constructors, etc.
   We use `erased` for Lean types, propositions and proofs that have been erased.
   Recall that for a Function `f`, we also generate `f._rarg` which does not take
   `erased` arguments. However, `f._rarg` is only safe to be used in full applications. -/
inductive Arg where
  | var (id : VarId)
  | erased
  deriving Inhabited, BEq, Repr

protected def Arg.beq : Arg → Arg → Bool
  | var x,      var y      => x == y
  | erased, erased         => true
  | _,          _          => false

inductive LitVal where
  | num (v : Nat)
  | str (v : String)
  deriving Inhabited, BEq

/-- Constructor information.

   - `name` is the Name of the Constructor in Lean.
   - `cidx` is the Constructor index (aka tag).
   - `size` is the number of arguments of type `object/tobject`.
   - `usize` is the number of arguments of type `usize`.
   - `ssize` is the number of bytes used to store scalar values.

Recall that a Constructor object contains a header, then a sequence of
pointers to other Lean objects, a sequence of `USize` (i.e., `size_t`)
scalar values, and a sequence of other scalar values. -/
structure CtorInfo where
  name : Name
  cidx : Nat
  size : Nat
  usize : Nat
  ssize : Nat
  deriving Inhabited, BEq, Repr

def CtorInfo.isRef (info : CtorInfo) : Bool :=
  info.size > 0 || info.usize > 0 || info.ssize > 0

def CtorInfo.isScalar (info : CtorInfo) : Bool :=
  !info.isRef

def CtorInfo.type (info : CtorInfo) : IRType :=
  if info.isRef then .object else .tagged

inductive Expr where
  /--
  `let x : obj := ctor[i] ys...` allocates a `lean_ctor_object` with the tag `i.cidx` and a scalar
  capacity of `i.usize * sizeof(size_t) + i.ssize`. If `i.isScalar` is true, instead returns
  `lean_box(i.cidx)`. All arguments should be boxed values.

  This instruction is also used to create `struct` and `union` values where `i.cidx` is used for
  the tag and `ys` should have types corresponding to the `objects` parameter of `IRType.struct`.
  -/
  | ctor (i : CtorInfo) (ys : Array Arg)
  | reset (n : Nat) (x : VarId)
  /-- `reuse x in ctor_i ys` instruction in the paper. -/
  | reuse (x : VarId) (i : CtorInfo) (updtHeader : Bool) (ys : Array Arg)
  /-- Extract the `tobject` value at Position `sizeof(void*)*i` from `x`. When `x` is represented
  as a `union`, `cidx` is used to determine which part of the union to access. -/
  | proj (cidx : Nat) (i : Nat) (x : VarId)
  /-- Extract the `usize` value at Position `sizeof(void*)*i` from `x`. -/
  | uproj (cidx : Nat) (i : Nat) (x : VarId)
  /-- Extract the scalar value at Position `sizeof(void*)*n + offset` from `x`. -/
  | sproj (cidx : Nat) (n : Nat) (offset : Nat) (x : VarId)
  /-- Full application. -/
  | fap (c : FunId) (ys : Array Arg)
  /-- Partial application that creates a `pap` value (aka closure in our nonstandard terminology). -/
  | pap (c : FunId) (ys : Array Arg)
  /-- Application. `x` must be a `pap` value. -/
  | ap  (x : VarId) (ys : Array Arg)
  /--
  Converts an owned value into another owned value. The `box` instruction comes in three variants:
  1. Given `x : ty` where `ty` is a scalar type, return a value of type `tobject`.
     For small scalar values, the result is a tagged pointer, and no memory allocation is performed.
  2. Given `x : ty` where `ty` is a struct/union type, return a value of type `object` or `tobject`
     (depending on whether `ty` has scalar constructors). This operation is the identity function
     in the interpreter model and is an allocation is the compiled model.
  3. Given `x : ty` where `ty` is a struct/union type, return a value of another struct/union type
     where different parts are boxed/unboxed. This variant is called a *reshape* and can contain
     both boxing and unboxing. For example, `let y : {{tobj, tobj}, obj} := box x` with
     `x : {obj, {tobj, tobj}}` unboxes the first component of `x` and boxes the second component
     of `x` into a `lean_ctor_object`. This is also the identity function in the interpreter.

  The last two variants are distinguished by the type of the variable declaration.
  -/
  | box (ty : IRType) (x : VarId)
  /--
  Unboxed a boxed (`tagged` / `object` / `tobject`) value into a scalar or `struct` / `union` value.
  The input value is taken borrowed and the result value is borrowed from the input value.
  That is, no reference counting operations are performed and the RC of the result value may need
  to be manually incremented and the RC of the input value may need to be decremented.

  In the interpreter, unboxing into a `struct` or `union` is the identity function since `struct`
  and `union` values are stored boxed in the interpreter.
  -/
  | unbox (x : VarId)
  | lit (v : LitVal)
  /-- Return `1 : uint8` Iff `RC(x) > 1` -/
  | isShared (x : VarId)
  deriving Inhabited

structure Param where
  x : VarId
  borrow : Bool
  ty : IRType
  deriving Inhabited, Repr

mutual

inductive Alt where
  | ctor (info : CtorInfo) (b : FnBody) : Alt
  | default (b : FnBody) : Alt

inductive FnBody where
  /-- `let x : ty := e; b` -/
  | vdecl (x : VarId) (ty : IRType) (e : Expr) (b : FnBody)
  /-- Join point Declaration `block_j (xs) := e; b` -/
  | jdecl (j : JoinPointId) (xs : Array Param) (v : FnBody) (b : FnBody)
  /-- Store `y` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
  This operation is not part of λPure is only used during optimization. -/
  | set (x : VarId) (i : Nat) (y : Arg) (b : FnBody)
  | setTag (x : VarId) (cidx : Nat) (b : FnBody)
  /-- Store `y : usize` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object or
  `struct`/`union` with tag `cidx` and `RC(x)` must be 1. -/
  | uset (x : VarId) (cidx : Nat) (i : Nat) (y : VarId) (b : FnBody)
  /-- Store `y : ty` at Position `sizeof(void*)*i + offset` in `x`. `x` must be a Constructor object
  or `struct`/`union` with tag `cidx` and `RC(x)` must be 1. `ty` must be a scalar type but not
  `usize`. -/
  | sset (x : VarId) (cidx : Nat) (i : Nat) (offset : Nat) (y : VarId) (ty : IRType) (b : FnBody)
  /-- RC increment for `object`. If c is `true`, then `inc` must check whether `x` is a tagged
  pointer or not. If `persistent` is `true` then `x` is statically known to be a persistent object
  and this operation does not need to be performed in compiled code. In compiled code, if the type
  of `x` is a `struct` or `union` type, then instead all fields are incremented. -/
  | inc (x : VarId) (n : Nat) (c : Bool) (persistent : Bool) (b : FnBody)
  /-- RC decrement for `object`. If c is `true`, then `inc` must check whether `x` is a tagged
  pointer or not. If `persistent` is `true` then `x` is statically known to be a persistent object
  and this operation does not need to be performed in compiled code. In compiled code, if the type
  of `x` is a `struct` or `union` type, then instead all fields are decremented. -/
  | dec (x : VarId) (n : Nat) (c : Bool) (persistent : Bool) (b : FnBody)
  | del (x : VarId) (b : FnBody)
  | case (tid : Name) (x : VarId) (xType : IRType) (cs : Array Alt)
  | ret (x : Arg)
  /-- Jump to join point `j` -/
  | jmp (j : JoinPointId) (ys : Array Arg)
  | unreachable
  deriving Inhabited

end

deriving instance Inhabited for Alt

abbrev FnBody.nil := FnBody.unreachable

def FnBody.isTerminal : FnBody → Bool
  | FnBody.case _ _ _ _  => true
  | FnBody.ret _         => true
  | FnBody.jmp _ _       => true
  | FnBody.unreachable   => true
  | _                    => false

def FnBody.body : FnBody → FnBody
  | FnBody.vdecl _ _ _ b      => b
  | FnBody.jdecl _ _ _ b      => b
  | FnBody.set _ _ _ b        => b
  | FnBody.uset _ _ _ _ b     => b
  | FnBody.sset _ _ _ _ _ _ b => b
  | FnBody.setTag _ _ b       => b
  | FnBody.inc _ _ _ _ b      => b
  | FnBody.dec _ _ _ _ b      => b
  | FnBody.del _ b            => b
  | other                     => other

def FnBody.setBody : FnBody → FnBody → FnBody
  | FnBody.vdecl x t v _,      b => FnBody.vdecl x t v b
  | FnBody.jdecl j xs v _,     b => FnBody.jdecl j xs v b
  | FnBody.set x i y _,        b => FnBody.set x i y b
  | FnBody.uset x c i y _,     b => FnBody.uset x c i y b
  | FnBody.sset x c i o y t _, b => FnBody.sset x c i o y t b
  | FnBody.setTag x i _,       b => FnBody.setTag x i b
  | FnBody.inc x n c p _,      b => FnBody.inc x n c p b
  | FnBody.dec x n c p _,      b => FnBody.dec x n c p b
  | FnBody.del x _,            b => FnBody.del x b
  | other,                     _ => other

@[inline] def FnBody.resetBody (b : FnBody) : FnBody :=
  b.setBody FnBody.nil

/-- If b is a non terminal, then return a pair `(c, b')` s.t. `b == c <;> b'`,
   and c.body == FnBody.nil -/
@[inline] def FnBody.split (b : FnBody) : FnBody × FnBody :=
  let b' := b.body
  let c  := b.resetBody
  (c, b')

def Alt.body : Alt → FnBody
  | Alt.ctor _ b  => b
  | Alt.default b => b

def Alt.setBody : Alt → FnBody → Alt
  | Alt.ctor c _, b  => Alt.ctor c b
  | Alt.default _, b => Alt.default b

@[inline] def Alt.modifyBody (f : FnBody → FnBody) : Alt → Alt
  | Alt.ctor c b  => Alt.ctor c (f b)
  | Alt.default b => Alt.default (f b)

@[inline] def Alt.modifyBodyM {m : Type → Type} [Monad m] (f : FnBody → m FnBody) : Alt → m Alt
  | Alt.ctor c b  => Alt.ctor c <$> f b
  | Alt.default b => Alt.default <$> f b

def Alt.isDefault : Alt → Bool
  | Alt.ctor _ _  => false
  | Alt.default _ => true

def push (bs : Array FnBody) (b : FnBody) : Array FnBody :=
  let b := b.resetBody
  bs.push b

partial def flattenAux (b : FnBody) (r : Array FnBody) : (Array FnBody) × FnBody :=
  if b.isTerminal then (r, b)
  else flattenAux b.body (push r b)

def FnBody.flatten (b : FnBody) : (Array FnBody) × FnBody :=
  flattenAux b #[]

partial def reshapeAux (a : Array FnBody) (i : Nat) (b : FnBody) : FnBody :=
  if i == 0 then b
  else
    let i         := i - 1
    let (curr, a) := a.swapAt! i default
    let b         := curr.setBody b
    reshapeAux a i b

def reshape (bs : Array FnBody) (term : FnBody) : FnBody :=
  reshapeAux bs bs.size term

@[inline] def modifyJPs (bs : Array FnBody) (f : FnBody → FnBody) : Array FnBody :=
  bs.map fun b => match b with
    | FnBody.jdecl j xs v k => FnBody.jdecl j xs (f v) k
    | other                 => other

@[inline] def modifyJPsM {m : Type → Type} [Monad m] (bs : Array FnBody) (f : FnBody → m FnBody) : m (Array FnBody) :=
  bs.mapM fun b => match b with
    | FnBody.jdecl j xs v k => return FnBody.jdecl j xs (← f v) k
    | other                 => return other

/-- Extra information associated with a declaration. -/
structure DeclInfo where
  /-- If `some <blame>`, then declaration depends on `<blame>` which uses a `sorry` axiom. -/
  sorryDep? : Option Name := none

inductive Decl where
  | fdecl  (f : FunId) (xs : Array Param) (type : IRType) (body : FnBody) (info : DeclInfo)
  | extern (f : FunId) (xs : Array Param) (type : IRType) (ext : ExternAttrData)
  deriving Inhabited

namespace Decl

def name : Decl → FunId
  | .fdecl f ..  => f
  | .extern f .. => f

def params : Decl → Array Param
  | .fdecl (xs := xs) ..  => xs
  | .extern (xs := xs) .. => xs

def resultType : Decl → IRType
  | .fdecl (type := t) ..  => t
  | .extern (type := t) .. => t

def isExtern : Decl → Bool
  | .extern .. => true
  | _ => false

def getInfo : Decl → DeclInfo
  | .fdecl (info := info) .. => info
  | _ => {}

def updateBody! (d : Decl) (bNew : FnBody) : Decl :=
  match d with
  | Decl.fdecl f xs t _ info => Decl.fdecl f xs t bNew info
  | _ => panic! "expected definition"

end Decl

-- Hack: we use this declaration as a stub for declarations annotated with `implemented_by` or `init`
def mkDummyExternDecl (f : FunId) (xs : Array Param) (ty : IRType) : Decl :=
  Decl.fdecl f xs ty FnBody.unreachable {}

/-- Set of variable and join point names -/
abbrev IndexSet := Std.TreeSet Index

def mkIndexSet (idx : Index) : IndexSet :=
  Std.TreeSet.empty.insert idx

inductive LocalContextEntry where
  | param     : IRType → LocalContextEntry
  | localVar  : IRType → Expr → LocalContextEntry
  | joinPoint : Array Param → FnBody → LocalContextEntry

abbrev LocalContext := Std.TreeMap Index LocalContextEntry

def LocalContext.addLocal (ctx : LocalContext) (x : VarId) (t : IRType) (v : Expr) : LocalContext :=
  ctx.insert x.idx (LocalContextEntry.localVar t v)

def LocalContext.addJP (ctx : LocalContext) (j : JoinPointId) (xs : Array Param) (b : FnBody) : LocalContext :=
  ctx.insert j.idx (LocalContextEntry.joinPoint xs b)

def LocalContext.addParam (ctx : LocalContext) (p : Param) : LocalContext :=
  ctx.insert p.x.idx (LocalContextEntry.param p.ty)

def LocalContext.addParams (ctx : LocalContext) (ps : Array Param) : LocalContext :=
  ps.foldl LocalContext.addParam ctx

def LocalContext.isJP (ctx : LocalContext) (idx : Index) : Bool :=
  match ctx.get? idx with
  | some (LocalContextEntry.joinPoint _ _) => true
  | _     => false

def LocalContext.getJPBody (ctx : LocalContext) (j : JoinPointId) : Option FnBody :=
  match ctx.get? j.idx with
  | some (LocalContextEntry.joinPoint _ b) => some b
  | _     => none

def LocalContext.getJPParams (ctx : LocalContext) (j : JoinPointId) : Option (Array Param) :=
  match ctx.get? j.idx with
  | some (LocalContextEntry.joinPoint ys _) => some ys
  | _     => none

def LocalContext.isParam (ctx : LocalContext) (idx : Index) : Bool :=
  match ctx.get? idx with
  | some (LocalContextEntry.param _) => true
  | _     => false

def LocalContext.isLocalVar (ctx : LocalContext) (idx : Index) : Bool :=
  match ctx.get? idx with
  | some (LocalContextEntry.localVar _ _) => true
  | _     => false

def LocalContext.contains (ctx : LocalContext) (idx : Index) : Bool :=
  Std.TreeMap.contains ctx idx

def LocalContext.eraseJoinPointDecl (ctx : LocalContext) (j : JoinPointId) : LocalContext :=
  ctx.erase j.idx

def LocalContext.getType (ctx : LocalContext) (x : VarId) : Option IRType :=
  match ctx.get? x.idx with
  | some (LocalContextEntry.param t) => some t
  | some (LocalContextEntry.localVar t _) => some t
  | _     => none

def LocalContext.getValue (ctx : LocalContext) (x : VarId) : Option Expr :=
  match ctx.get? x.idx with
  | some (LocalContextEntry.localVar _ v) => some v
  | _     => none

abbrev IndexRenaming := Std.TreeMap Index Index

class AlphaEqv (α : Type) where
  aeqv : IndexRenaming → α → α → Bool

export AlphaEqv (aeqv)

def VarId.alphaEqv (ρ : IndexRenaming) (v₁ v₂ : VarId) : Bool :=
  match ρ.get? v₁.idx with
  | some v => v == v₂.idx
  | none   => v₁ == v₂

instance : AlphaEqv VarId := ⟨VarId.alphaEqv⟩

def Arg.alphaEqv (ρ : IndexRenaming) : Arg → Arg → Bool
  | .var v₁,     .var v₂     => aeqv ρ v₁ v₂
  | .erased,     .erased     => true
  | _,           _           => false

instance : AlphaEqv Arg := ⟨Arg.alphaEqv⟩

def args.alphaEqv (ρ : IndexRenaming) (args₁ args₂ : Array Arg) : Bool :=
  Array.isEqv args₁ args₂ (fun a b => aeqv ρ a b)

instance: AlphaEqv (Array Arg) := ⟨args.alphaEqv⟩

def Expr.alphaEqv (ρ : IndexRenaming) : Expr → Expr → Bool
  | Expr.ctor i₁ ys₁,        Expr.ctor i₂ ys₂        => i₁ == i₂ && aeqv ρ ys₁ ys₂
  | Expr.reset n₁ x₁,        Expr.reset n₂ x₂        => n₁ == n₂ && aeqv ρ x₁ x₂
  | Expr.reuse x₁ i₁ u₁ ys₁, Expr.reuse x₂ i₂ u₂ ys₂ => aeqv ρ x₁ x₂ && i₁ == i₂ && u₁ == u₂ && aeqv ρ ys₁ ys₂
  | Expr.proj _ i₁ x₁,       Expr.proj _ i₂ x₂       => i₁ == i₂ && aeqv ρ x₁ x₂
  | Expr.uproj _ i₁ x₁,      Expr.uproj _ i₂ x₂      => i₁ == i₂ && aeqv ρ x₁ x₂
  | Expr.sproj _ n₁ o₁ x₁,   Expr.sproj _ n₂ o₂ x₂   => n₁ == n₂ && o₁ == o₂ && aeqv ρ x₁ x₂
  | Expr.fap c₁ ys₁,         Expr.fap c₂ ys₂         => c₁ == c₂ && aeqv ρ ys₁ ys₂
  | Expr.pap c₁ ys₁,         Expr.pap c₂ ys₂         => c₁ == c₂ && aeqv ρ ys₁ ys₂
  | Expr.ap x₁ ys₁,          Expr.ap x₂ ys₂          => aeqv ρ x₁ x₂ && aeqv ρ ys₁ ys₂
  | Expr.box ty₁ x₁,         Expr.box ty₂ x₂         => ty₁ == ty₂ && aeqv ρ x₁ x₂
  | Expr.unbox x₁,           Expr.unbox x₂           => aeqv ρ x₁ x₂
  | Expr.lit v₁,             Expr.lit v₂             => v₁ == v₂
  | Expr.isShared x₁,        Expr.isShared x₂        => aeqv ρ x₁ x₂
  | _,                        _                      => false

instance : AlphaEqv Expr := ⟨Expr.alphaEqv⟩

def addVarRename (ρ : IndexRenaming) (x₁ x₂ : Nat) :=
  if x₁ == x₂ then ρ else ρ.insert x₁ x₂

def addParamRename (ρ : IndexRenaming) (p₁ p₂ : Param) : Option IndexRenaming :=
  if p₁.ty == p₂.ty && p₁.borrow = p₂.borrow then
    some (addVarRename ρ p₁.x.idx p₂.x.idx)
  else
    none

def addParamsRename (ρ : IndexRenaming) (ps₁ ps₂ : Array Param) : Option IndexRenaming := do
  if ps₁.size != ps₂.size then
    failure
  else
    let mut ρ := ρ
    for i in *...ps₁.size do
      ρ ← addParamRename ρ ps₁[i]! ps₂[i]!
    pure ρ

partial def FnBody.alphaEqv : IndexRenaming → FnBody → FnBody → Bool
  | ρ, FnBody.vdecl x₁ t₁ v₁ b₁,        FnBody.vdecl x₂ t₂ v₂ b₂        =>
    t₁ == t₂ && aeqv ρ v₁ v₂ && alphaEqv (addVarRename ρ x₁.idx x₂.idx) b₁ b₂
  | ρ, FnBody.jdecl j₁ ys₁ v₁ b₁,       FnBody.jdecl j₂ ys₂ v₂ b₂       =>
    match addParamsRename ρ ys₁ ys₂ with
    | some ρ' => alphaEqv ρ' v₁ v₂ && alphaEqv (addVarRename ρ j₁.idx j₂.idx) b₁ b₂
    | none    => false
  | ρ, FnBody.set x₁ i₁ y₁ b₁,          FnBody.set x₂ i₂ y₂ b₂          =>
    aeqv ρ x₁ x₂ && i₁ == i₂ && aeqv ρ y₁ y₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.uset x₁ _ i₁ y₁ b₁,       FnBody.uset x₂ _ i₂ y₂ b₂       =>
    aeqv ρ x₁ x₂ && i₁ == i₂ && aeqv ρ y₁ y₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.sset x₁ _ i₁ o₁ y₁ t₁ b₁, FnBody.sset x₂ _ i₂ o₂ y₂ t₂ b₂ =>
    aeqv ρ x₁ x₂ && i₁ = i₂ && o₁ = o₂ && aeqv ρ y₁ y₂ && t₁ == t₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.setTag x₁ i₁ b₁,          FnBody.setTag x₂ i₂ b₂          =>
    aeqv ρ x₁ x₂ && i₁ == i₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.inc x₁ n₁ c₁ p₁ b₁,       FnBody.inc x₂ n₂ c₂ p₂ b₂       =>
    aeqv ρ x₁ x₂ && n₁ == n₂ && c₁ == c₂ && p₁ == p₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.dec x₁ n₁ c₁ p₁ b₁,       FnBody.dec x₂ n₂ c₂ p₂ b₂       =>
    aeqv ρ x₁ x₂ && n₁ == n₂ && c₁ == c₂ && p₁ == p₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.del x₁ b₁,                FnBody.del x₂ b₂                =>
    aeqv ρ x₁ x₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.case n₁ x₁ _ alts₁,       FnBody.case n₂ x₂ _ alts₂       =>
    n₁ == n₂ && aeqv ρ x₁ x₂ && Array.isEqv alts₁ alts₂ (fun alt₁ alt₂ =>
     match alt₁, alt₂ with
     | Alt.ctor i₁ b₁, Alt.ctor i₂ b₂ => i₁ == i₂ && alphaEqv ρ b₁ b₂
     | Alt.default b₁, Alt.default b₂ => alphaEqv ρ b₁ b₂
     | _,              _              => false)
  | ρ, FnBody.jmp j₁ ys₁,               FnBody.jmp j₂ ys₂               =>
    j₁ == j₂ && aeqv ρ ys₁ ys₂
  | ρ, FnBody.ret x₁,                   FnBody.ret x₂                   =>
    aeqv ρ x₁ x₂
  | _, FnBody.unreachable,              FnBody.unreachable              =>
    true
  | _, _,                               _                               =>
    false

def FnBody.beq (b₁ b₂ : FnBody) : Bool :=
  FnBody.alphaEqv ∅ b₁ b₂

instance : BEq FnBody := ⟨FnBody.beq⟩

abbrev VarIdSet := Std.TreeSet VarId (fun x y => compare x.idx y.idx)

def mkIf (x : VarId) (t e : FnBody) : FnBody :=
  FnBody.case `Bool x IRType.uint8 #[
    Alt.ctor {name := ``Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0} e,
    Alt.ctor {name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0} t
  ]

def getUnboxOpName (t : IRType) : String :=
  match t with
  | IRType.usize    => "lean_unbox_usize"
  | IRType.uint32   => "lean_unbox_uint32"
  | IRType.uint64   => "lean_unbox_uint64"
  | IRType.float    => "lean_unbox_float"
  | IRType.float32  => "lean_unbox_float32"
  | _               => "lean_unbox"

end Lean.IR
