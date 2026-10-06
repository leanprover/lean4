/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.ExternAttr
import Init.Data.Range.Polymorphic.Iterators

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

   - `struct` and `union` are used to return small values (e.g., `Option`, `Prod`, `Except`)
      on the stack.

Remark: the RC operations for `tobject` are slightly more expensive because we
first need to test whether the `tobject` is really a pointer or not.

Remark: the Lean runtime assumes that sizeof(void*) == sizeof(sizeT).
Lean cannot be compiled on old platforms where this is not True.

Since values of type `struct` and `union` are only used to return values,
We assume they must be used/consumed "linearly". We use the term "linear" here
to mean "exactly once" in each execution. That is, given `x : S`, where `S` is a struct,
then one of the following must hold in each (execution) branch.
1- `x` occurs only at a single `ret x` instruction. That is, it is being consumed by being returned.
2- `x` occurs only at a single `ctor`. That is, it is being "consumed" by being stored into another `struct/union`.
3- We extract (aka project) every single field of `x` exactly once. That is, we are consuming `x` by consuming each
   of one of its components. Minor refinement: we don't need to consume scalar fields or struct/union
   fields that do not contain object fields.
-/
inductive IRType where
  | float | uint8 | uint16 | uint32 | uint64 | usize
  | erased | object | tobject
  | float32
  | struct (leanTypeName : Option Name) (types : Array IRType) : IRType
  | union (leanTypeName : Name) (types : Array IRType) : IRType
  -- TODO: Move this upwards after a stage0 update.
  | tagged
  | void
  deriving Inhabited, BEq, Repr

namespace IRType

def isScalar : IRType → Bool
  | float    => true
  | float32  => true
  | uint8    => true
  | uint16   => true
  | uint32   => true
  | uint64   => true
  | usize    => true
  | _        => false

def isObj : IRType → Bool
  | object  => true
  | tagged  => true
  | tobject => true
  | void    => true
  | _       => false

def isPossibleRef : IRType → Bool
  | object | tobject => true
  | _ => false

def isDefiniteRef : IRType → Bool
  | object => true
  | _ => false

def isErased : IRType → Bool
  | erased => true
  | _ => false

def isVoid : IRType → Bool
  | void => true
  | _ => false

def boxed : IRType → IRType
  | object | float | float32 => object
  | void | tagged | uint8 | uint16 => tagged
  | _ => tobject

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
  /-- We use `ctor` mainly for constructing Lean object/tobject values `lean_ctor_object` in the runtime.
  This instruction is also used to creat `struct` and `union` return values.
  For `union`, only `i.cidx` is relevant. For `struct`, `i` is irrelevant. -/
  | ctor (tgt : VarId) (b : FnBody) (i : CtorInfo) (ys : Array Arg)
  | reset (tgt : VarId) (b : FnBody) (n : Nat) (x : VarId)
  /-- `reuse x in ctor_i ys` instruction in the paper. -/
  | reuse (tgt : VarId) (b : FnBody) (x : VarId) (i : CtorInfo) (updtHeader : Bool) (ys : Array Arg)
  /-- Extract the `tobject` value at Position `sizeof(void*)*i` from `x`.
  We also use `proj` for extracting fields from `struct` return values, and casting `union` return values. -/
  | proj (tgt : VarId) (b : FnBody) (i : Nat) (x : VarId)
  /-- Extract the `Usize` value at Position `sizeof(void*)*i` from `x`. -/
  | uproj (tgt : VarId) (b : FnBody) (i : Nat) (x : VarId)
  /-- Extract the scalar value at Position `sizeof(void*)*n + offset` from `x`. -/
  | sproj (tgt : VarId) (b : FnBody) (ty : IRType) (n : Nat) (offset : Nat) (x : VarId)
  /-- Full application. -/
  | fap (tgt : VarId) (b : FnBody) (ty : IRType) (c : FunId) (ys : Array Arg)
  /-- Partial application that creates a `pap` value (aka closure in our nonstandard terminology). -/
  | pap (tgt : VarId) (b : FnBody) (c : FunId) (ys : Array Arg)
  /-- Application. `x` must be a `pap` value. -/
  | ap (tgt : VarId) (b : FnBody) (x : VarId) (ys : Array Arg)
  /-- Given `x : ty` where `ty` is a scalar type, this operation returns a value of Type `tobject`.
  For small scalar values, the Result is a tagged pointer, and no memory allocation is performed. -/
  | box (tgt : VarId) (b : FnBody) (ty : IRType) (x : VarId)
  /-- Given `x : [t]object`, obtain the scalar value. -/
  | unbox (tgt : VarId) (b : FnBody) (ty : IRType) (x : VarId)
  | uint8Lit (tgt : VarId) (b : FnBody) (v : UInt8)
  | uint16Lit (tgt : VarId) (b : FnBody) (v : UInt16)
  | uint32Lit (tgt : VarId) (b : FnBody) (v : UInt32)
  | uint64Lit (tgt : VarId) (b : FnBody) (v : UInt64)
  | usizeLit (tgt : VarId) (b : FnBody) (v : UInt64)
  | natLit (tgt : VarId) (b : FnBody) (v : Nat)
  | strLit (tgt : VarId) (b : FnBody) (v : String)
  /-- Return `1 : uint8` Iff `RC(x) > 1` -/
  | isShared (tgt : VarId) (b : FnBody) (x : VarId) -- type is always UInt8
  /-- Join point Declaration `block_j (xs) := e; b` -/
  | jdecl (j : JoinPointId) (xs : Array Param) (v : FnBody) (b : FnBody)
  /-- Store `y` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
  This operation is not part of λPure is only used during optimization. -/
  | set (x : VarId) (i : Nat) (y : Arg) (b : FnBody)
  | setTag (x : VarId) (cidx : Nat) (b : FnBody)
  /-- Store `y : Usize` at Position `sizeof(void*)*i` in `x`. `x` must be a Constructor object and `RC(x)` must be 1. -/
  | uset (x : VarId) (i : Nat) (y : VarId) (b : FnBody)
  /-- Store `y : ty` at Position `sizeof(void*)*i + offset` in `x`. `x` must be a Constructor object and `RC(x)` must be 1.
  `ty` must not be `object`, `tobject`, `erased` nor `Usize`. -/
  | sset (x : VarId) (i : Nat) (offset : Nat) (y : VarId) (ty : IRType) (b : FnBody)
  /-- RC increment for `object`. If c == `true`, then `inc` must check whether `x` is a tagged pointer or not.
  If `persistent == true` then `x` is statically known to be a persistent object. -/
  | inc (x : VarId) (n : Nat) (c : Bool) (persistent : Bool) (b : FnBody)
  /-- RC decrement for `object`. If c == `true`, then `inc` must check whether `x` is a tagged pointer or not.
  If `persistent == true` then `x` is statically known to be a persistent object. -/
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

def FnBody.isVarDecl : FnBody → Bool
  | FnBody.ctor ..
  | FnBody.reset ..
  | FnBody.reuse ..
  | FnBody.proj ..
  | FnBody.uproj ..
  | FnBody.sproj ..
  | FnBody.fap ..
  | FnBody.pap ..
  | FnBody.ap ..
  | FnBody.box ..
  | FnBody.unbox ..
  | FnBody.uint8Lit ..
  | FnBody.uint16Lit ..
  | FnBody.uint32Lit ..
  | FnBody.uint64Lit ..
  | FnBody.usizeLit ..
  | FnBody.natLit ..
  | FnBody.strLit ..
  | FnBody.isShared .. => true
  | _ => false

def FnBody.targetVar : FnBody → VarId
  | FnBody.ctor v ..
  | FnBody.reset v ..
  | FnBody.reuse v ..
  | FnBody.proj v ..
  | FnBody.uproj v ..
  | FnBody.sproj v ..
  | FnBody.fap v ..
  | FnBody.pap v ..
  | FnBody.ap v ..
  | FnBody.box v ..
  | FnBody.unbox v ..
  | FnBody.uint8Lit v ..
  | FnBody.uint16Lit v ..
  | FnBody.uint32Lit v ..
  | FnBody.uint64Lit v ..
  | FnBody.usizeLit v ..
  | FnBody.natLit v ..
  | FnBody.strLit v ..
  | FnBody.isShared v .. => v
  | _ => panic! "expected var decl"

def FnBody.targetType : FnBody → IRType
  | .ctor _ _ i _ => i.type
  | .reset .. => .tobject
  | .reuse .. => .object
  | .proj .. => .tobject
  | .uproj .. => .usize
  | .sproj _ _ ty .. => ty
  | .fap _ _ ty .. => ty
  | .pap .. => .object
  | .ap .. => .tobject
  | .box _ _ ty .. =>
    match ty with
    | .uint8 | .uint16 => .tagged
    | .uint32 => .tobject
    | .uint64 | .usize | .float | .float32 => .object
    | _ => .tobject
  | .unbox _ _ ty _ => ty
  | .uint8Lit .. => .uint8
  | .uint16Lit .. => .uint16
  | .uint32Lit .. => .uint32
  | .uint64Lit .. => .uint64
  | .usizeLit .. => .usize
  | .natLit _ _ n => if n < UInt32.size / 2 then .tagged else .tobject
  | .strLit .. => .object
  | .isShared .. => .uint8
  | _ => panic! "expected var decl"

def FnBody.setTargetVar : FnBody → VarId → FnBody
  | .ctor _tgt b i ys,               tgt => .ctor tgt b i ys
  | .reset _tgt b n x,               tgt => .reset tgt b n x
  | .reuse _tgt b x i updtHeader ys, tgt => .reuse tgt b x i updtHeader ys
  | .proj _tgt b i x,                tgt => .proj tgt b i x
  | .uproj _tgt b i x,               tgt => .uproj tgt b i x
  | .sproj _tgt b ty n offset x,     tgt => .sproj tgt b ty n offset x
  | .fap _tgt b ty c ys,             tgt => .fap tgt b ty c ys
  | .pap _tgt b c ys,                tgt => .pap tgt b c ys
  | .ap _tgt b x ys,                 tgt => .ap tgt b x ys
  | .box _tgt b ty x,                tgt => .box tgt b ty x
  | .unbox _tgt b ty x,              tgt => .unbox tgt b ty x
  | .uint8Lit _tgt b v,              tgt => .uint8Lit tgt b v
  | .uint16Lit _tgt b v,             tgt => .uint16Lit tgt b v
  | .uint32Lit _tgt b v,             tgt => .uint32Lit tgt b v
  | .uint64Lit _tgt b v,             tgt => .uint64Lit tgt b v
  | .usizeLit _tgt b v,              tgt => .usizeLit tgt b v
  | .natLit _tgt b v,                tgt => .natLit tgt b v
  | .strLit _tgt b v,                tgt => .strLit tgt b v
  | .isShared _tgt b x,              tgt => .isShared tgt b x
  | _, _ => panic! "expected var decl"


def FnBody.body : FnBody → FnBody
  | FnBody.ctor _ b ..      => b
  | FnBody.reset _ b ..     => b
  | FnBody.reuse _ b ..     => b
  | FnBody.proj _ b ..      => b
  | FnBody.uproj _ b ..     => b
  | FnBody.sproj _ b ..     => b
  | FnBody.fap _ b ..       => b
  | FnBody.pap _ b ..       => b
  | FnBody.ap _ b ..        => b
  | FnBody.box _ b ..       => b
  | FnBody.unbox _ b ..     => b
  | FnBody.uint8Lit _ b ..  => b
  | FnBody.uint16Lit _ b .. => b
  | FnBody.uint32Lit _ b .. => b
  | FnBody.uint64Lit _ b .. => b
  | FnBody.usizeLit _ b ..  => b
  | FnBody.natLit _ b ..    => b
  | FnBody.strLit _ b ..    => b
  | FnBody.isShared _ b ..  => b
  | FnBody.jdecl _ _ _ b    => b
  | FnBody.set _ _ _ b      => b
  | FnBody.uset _ _ _ b     => b
  | FnBody.sset _ _ _ _ _ b => b
  | FnBody.setTag _ _ b     => b
  | FnBody.inc _ _ _ _ b    => b
  | FnBody.dec _ _ _ _ b    => b
  | FnBody.del _ b          => b
  | other                   => other

def FnBody.setBody : FnBody → FnBody → FnBody
  | .ctor tgt _b i ys,               b => .ctor tgt b i ys
  | .reset tgt _b n x,               b => .reset tgt b n x
  | .reuse tgt _b x i updtHeader ys, b => .reuse tgt b x i updtHeader ys
  | .proj tgt _b i x,                b => .proj tgt b i x
  | .uproj tgt _b i x,               b => .uproj tgt b i x
  | .sproj tgt _b ty n offset x,     b => .sproj tgt b ty n offset x
  | .fap tgt _b ty c ys,             b => .fap tgt b ty c ys
  | .pap tgt _b c ys,                b => .pap tgt b c ys
  | .ap tgt _b x ys,                 b => .ap tgt b x ys
  | .box tgt _b ty x,                b => .box tgt b ty x
  | .unbox tgt _b ty x,              b => .unbox tgt b ty x
  | .uint8Lit tgt _b v,              b => .uint8Lit tgt b v
  | .uint16Lit tgt _b v,             b => .uint16Lit tgt b v
  | .uint32Lit tgt _b v,             b => .uint32Lit tgt b v
  | .uint64Lit tgt _b v,             b => .uint64Lit tgt b v
  | .usizeLit tgt _b v,              b => .usizeLit tgt b v
  | .natLit tgt _b v,                b => .natLit tgt b v
  | .strLit tgt _b v,                b => .strLit tgt b v
  | .isShared tgt _b x,              b => .isShared tgt b x
  | .jdecl j xs v _b,                b => .jdecl j xs v b
  | .set x i y _b,                   b => .set x i y b
  | .setTag x cidx _b,               b => .setTag x cidx b
  | .uset x i y _b,                  b => .uset x i y b
  | .sset x i offset y ty _b,        b => .sset x i offset y ty b
  | .inc x n c persistent _b,        b => .inc x n c persistent b
  | .dec x n c persistent _b,        b => .dec x n c persistent b
  | .del x _b,                       b => .del x b
  | other,                           _ => other

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
  maxJp : Nat
  maxVar : Nat

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
  | _ => { maxJp := 0, maxVar := 0 }

def updateBody! (d : Decl) (bNew : FnBody) : Decl :=
  match d with
  | Decl.fdecl f xs t _ info => Decl.fdecl f xs t bNew info
  | _ => panic! "expected definition"

end Decl

-- Hack: we use this declaration as a stub for declarations annotated with `implemented_by` or `init`
def mkDummyExternDecl (f : FunId) (xs : Array Param) (ty : IRType) : Decl :=
  Decl.fdecl f xs ty FnBody.unreachable { maxJp := 0, maxVar := 0 }

/-- Set of variable and join point names -/
abbrev IndexSet := Std.TreeSet Index

def mkIndexSet (idx : Index) : IndexSet :=
  Std.TreeSet.empty.insert idx

inductive LocalContextEntry where
  | param     : IRType → LocalContextEntry
  | localVar  : IRType → FnBody → LocalContextEntry

structure LocalContext where
  vars : Std.TreeMap Index LocalContextEntry := {}
  jps : Std.TreeMap Index (Array Param × FnBody) := {}

def LocalContext.addLocal (ctx : LocalContext) (x : VarId) (t : IRType) (v : FnBody) : LocalContext :=
  { ctx with vars := ctx.vars.insert x.idx (LocalContextEntry.localVar t v) }

def LocalContext.addJP (ctx : LocalContext) (j : JoinPointId) (xs : Array Param) (b : FnBody) : LocalContext :=
  { ctx with jps := ctx.jps.insert j.idx (xs, b) }

def LocalContext.addParam (ctx : LocalContext) (p : Param) : LocalContext :=
  { ctx with vars := ctx.vars.insert p.x.idx (LocalContextEntry.param p.ty) }

def LocalContext.addParams (ctx : LocalContext) (ps : Array Param) : LocalContext :=
  ps.foldl LocalContext.addParam ctx

def LocalContext.isJP (ctx : LocalContext) (j : JoinPointId) : Bool :=
  ctx.jps.contains j.idx

def LocalContext.getJPBody (ctx : LocalContext) (j : JoinPointId) : Option FnBody :=
  ctx.jps.get? j.idx |>.map (·.2)

def LocalContext.getJPParams (ctx : LocalContext) (j : JoinPointId) : Option (Array Param) :=
  ctx.jps.get? j.idx |>.map (·.1)

def LocalContext.isParam (ctx : LocalContext) (x : VarId) : Bool :=
  match ctx.vars.get? x.idx with
  | some (LocalContextEntry.param _) => true
  | _     => false

def LocalContext.isLocalVar (ctx : LocalContext) (x : VarId) : Bool :=
  match ctx.vars.get? x.idx with
  | some (LocalContextEntry.localVar _ _) => true
  | _     => false

def LocalContext.eraseJoinPointDecl (ctx : LocalContext) (j : JoinPointId) : LocalContext :=
  { ctx with jps := ctx.jps.erase j.idx }

def LocalContext.getType (ctx : LocalContext) (x : VarId) : Option IRType :=
  match ctx.vars.get? x.idx with
  | some (LocalContextEntry.param t) => some t
  | some (LocalContextEntry.localVar t _) => some t
  | _     => none

def LocalContext.getValue (ctx : LocalContext) (x : VarId) : Option FnBody :=
  match ctx.vars.get? x.idx with
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

instance : AlphaEqv (Array Arg) := ⟨args.alphaEqv⟩

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
  | ρ, FnBody.ctor tgt₁ b₁ i₁ ys₁,        .ctor tgt₂ b₂ i₂ ys₂        => i₁ == i₂ && aeqv ρ ys₁ ys₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.reset tgt₁ b₁ n₁ x₁,        .reset tgt₂ b₂ n₂ x₂        => n₁ == n₂ && aeqv ρ x₁ x₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.reuse tgt₁ b₁ x₁ i₁ u₁ ys₁, .reuse tgt₂ b₂ x₂ i₂ u₂ ys₂ => aeqv ρ x₁ x₂ && i₁ == i₂ && u₁ == u₂ && aeqv ρ ys₁ ys₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.proj tgt₁ b₁ i₁ x₁,         .proj tgt₂ b₂ i₂ x₂         => i₁ == i₂ && aeqv ρ x₁ x₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.uproj tgt₁ b₁ i₁ x₁,        .uproj tgt₂ b₂ i₂ x₂        => i₁ == i₂ && aeqv ρ x₁ x₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.sproj tgt₁ b₁ ty₁ n₁ o₁ x₁, .sproj tgt₂ b₂ ty₂ n₂ o₂ x₂ => ty₁ == ty₂ && n₁ == n₂ && o₁ == o₂ && aeqv ρ x₁ x₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.fap tgt₁ b₁ ty₁ c₁ ys₁,     .fap tgt₂ b₂ ty₂ c₂ ys₂     => ty₁ == ty₂ && c₁ == c₂ && aeqv ρ ys₁ ys₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.pap tgt₁ b₁ c₁ ys₁,         .pap tgt₂ b₂ c₂ ys₂         => c₁ == c₂ && aeqv ρ ys₁ ys₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.ap tgt₁ b₁ x₁ ys₁,          .ap tgt₂ b₂ x₂ ys₂          => aeqv ρ x₁ x₂ && aeqv ρ ys₁ ys₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.box tgt₁ b₁ ty₁ x₁,         .box tgt₂ b₂ ty₂ x₂         => ty₁ == ty₂ && aeqv ρ x₁ x₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.unbox tgt₁ b₁ ty₁ x₁,       .unbox tgt₂ b₂ ty₂ x₂       => ty₁ == ty₂ && aeqv ρ x₁ x₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.uint8Lit tgt₁ b₁ v₁,        .uint8Lit tgt₂ b₂ v₂        => v₁ == v₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.uint16Lit tgt₁ b₁ v₁,       .uint16Lit tgt₂ b₂ v₂       => v₁ == v₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.uint32Lit tgt₁ b₁ v₁,       .uint32Lit tgt₂ b₂ v₂       => v₁ == v₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.uint64Lit tgt₁ b₁ v₁,       .uint64Lit tgt₂ b₂ v₂       => v₁ == v₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.usizeLit tgt₁ b₁ v₁,        .usizeLit tgt₂ b₂ v₂        => v₁ == v₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.natLit tgt₁ b₁ v₁,          .natLit tgt₂ b₂ v₂          => v₁ == v₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.strLit tgt₁ b₁ v₁,          .strLit tgt₂ b₂ v₂          => v₁ == v₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.isShared tgt₁ b₁ x₁,        .isShared tgt₂ b₂ x₂        => aeqv ρ x₁ x₂ && alphaEqv (addVarRename ρ tgt₁.idx tgt₂.idx) b₁ b₂
  | ρ, FnBody.jdecl j₁ ys₁ v₁ b₁,  FnBody.jdecl j₂ ys₂ v₂ b₂        => match addParamsRename ρ ys₁ ys₂ with
    | some ρ' => alphaEqv ρ' v₁ v₂ && alphaEqv (addVarRename ρ j₁.idx j₂.idx) b₁ b₂
    | none    => false
  | ρ, FnBody.set x₁ i₁ y₁ b₁,        FnBody.set x₂ i₂ y₂ b₂        => aeqv ρ x₁ x₂ && i₁ == i₂ && aeqv ρ y₁ y₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.uset x₁ i₁ y₁ b₁,       FnBody.uset x₂ i₂ y₂ b₂       => aeqv ρ x₁ x₂ && i₁ == i₂ && aeqv ρ y₁ y₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.sset x₁ i₁ o₁ y₁ t₁ b₁, FnBody.sset x₂ i₂ o₂ y₂ t₂ b₂ =>
    aeqv ρ x₁ x₂ && i₁ = i₂ && o₁ = o₂ && aeqv ρ y₁ y₂ && t₁ == t₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.setTag x₁ i₁ b₁,        FnBody.setTag x₂ i₂ b₂        => aeqv ρ x₁ x₂ && i₁ == i₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.inc x₁ n₁ c₁ p₁ b₁,     FnBody.inc x₂ n₂ c₂ p₂ b₂     => aeqv ρ x₁ x₂ && n₁ == n₂ && c₁ == c₂ && p₁ == p₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.dec x₁ n₁ c₁ p₁ b₁,     FnBody.dec x₂ n₂ c₂ p₂ b₂     => aeqv ρ x₁ x₂ && n₁ == n₂ && c₁ == c₂ && p₁ == p₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.del x₁ b₁,              FnBody.del x₂ b₂              => aeqv ρ x₁ x₂ && alphaEqv ρ b₁ b₂
  | ρ, FnBody.case n₁ x₁ _ alts₁,     FnBody.case n₂ x₂ _ alts₂     => n₁ == n₂ && aeqv ρ x₁ x₂ && Array.isEqv alts₁ alts₂ (fun alt₁ alt₂ =>
     match alt₁, alt₂ with
     | Alt.ctor i₁ b₁, Alt.ctor i₂ b₂ => i₁ == i₂ && alphaEqv ρ b₁ b₂
     | Alt.default b₁, Alt.default b₂ => alphaEqv ρ b₁ b₂
     | _,              _              => false)
  | ρ, FnBody.jmp j₁ ys₁,             FnBody.jmp j₂ ys₂             => j₁ == j₂ && aeqv ρ ys₁ ys₂
  | ρ, FnBody.ret x₁,                 FnBody.ret x₂                 => aeqv ρ x₁ x₂
  | _, FnBody.unreachable,            FnBody.unreachable            => true
  | _, _,                             _                             => false

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
