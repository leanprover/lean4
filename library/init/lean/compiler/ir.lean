/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import init.lean.name init.lean.kvmap
prelude

/-
Implements (extended) λ_pure and λ_RC proposed in the article
"Counting Immutable Beans", Sebastian Ullrich and Leonardo de Moura.

The Lean to IR transformation produces λ_pure code. That is,
then transformed using the procedures described in the paper above.
-/
namespace lean
namespace ir

/- Variable identifier -/
abbreviation varid := name
/- Function identifier -/
abbreviation fid := name
/- Join point identifier -/
abbreviation jpid := name

/- Low level IR types. Most are self explanatory.

   - `usize` represents the C++ `size_t` type. We have it here
      because it is 32-bit in 32-bit machines, and 64-bit in 64-bit machines,
      and we want the C++ backend for our compiler to generate platform independent code.

   - `irrelevant` for Lean types, propositions and proofs.

   - `object` a pointer to a value in the heap.

   - `tobject` a pointer to a value in the heap or tagged pointer
      (i.e., the least significant bit is 1) storing a scalar value.

Remark: the RC operations for `tobject` are slightly more expensive because we
first need to test whether the `tobject` is really a pointer or not.

Remark: the Lean runtime assumes that sizeof(void*) == sizeof(size_t).
Lean cannot be compiled on old platforms where this is not true. -/
inductive type
| float | uint8 | uint16 | uint32 | uint64 | usize
| irrelevant | object | tobject

def type.beq : type → type → bool
| type.float      type.float      := tt
| type.uint8      type.uint8      := tt
| type.uint16     type.uint16     := tt
| type.uint32     type.uint32     := tt
| type.uint64     type.uint64     := tt
| type.usize      type.usize      := tt
| type.irrelevant type.irrelevant := tt
| type.object     type.object     := tt
| type.tobject    type.tobject    := tt
| _               _               := ff

instance type.has_beq : has_beq type := ⟨type.beq⟩

/- Arguments to applications, constructors, etc.
   We use `irrelevant` for Lean types, propositions and proofs that have been erased.
   Recall that for a function `f`, we also generate `f._rarg` which does not take
   `irrelevant` arguments. However, `f._rarg` is only safe to be used in full applications. -/
inductive arg
| var (id : varid)
| irrelevant

inductive litval
| num (v : nat)
| str (v : string)

def litval.beq : litval → litval → bool
| (litval.num v₁) (litval.num v₂) := v₁ = v₂
| (litval.str v₁) (litval.str v₂) := v₁ = v₂
| _               _               := ff

instance litval.has_beq : has_beq litval := ⟨litval.beq⟩

/- Constructor information.

   - `id` is the name of the constructor in Lean.
   - `cidx` is the constructor index (aka tag).
   - `usize` is the number of arguments of type `usize`.
   - `ssize` is the number of bytes used to store scalar values.

Recall that a constructor object contains a header, then a sequence of
pointers to other Lean objects, a sequence of `usize` (i.e., `size_t`)
scalar values, and a sequence of other scalar values. -/
structure ctor_info :=
(id : name) (cidx : nat) (usize : nat) (ssize : nat)

def ctor_info.beq : ctor_info → ctor_info → bool
| ⟨id₁, cidx₁, usize₁, ssize₁⟩ ⟨id₂, cidx₂, usize₂, ssize₂⟩ :=
  id₁ = id₂ && cidx₁ = cidx₂ && usize₁ = usize₂ && ssize₁ = ssize₂

instance ctor_info.has_beq : has_beq ctor_info := ⟨ctor_info.beq⟩

inductive expr
| ctor (i : ctor_info) (ys : list arg)
| reset (x : varid)
/- `reuse x in ctor_i ys` instruction in the paper. -/
| reuse (x : varid) (i : ctor_info) (ys : list arg)
/- Extract the `tobject` value at position `sizeof(void)*i` from `x`. -/
| proj (i : nat) (x : varid)
/- Extract the `usize` value at position `sizeof(void)*i` from `x`. -/
| uproj (i : nat) (x : varid)
/- Extract the scalar value at position `n` (in bytes) from `x`. -/
| sproj (n : nat) (x : varid)
/- Full application. -/
| fap (c : fid) (ys : list arg)
/- Partial application that creates a `pap` value (aka closure in our nonstandard terminology). -/
| pap (c : fid) (ys : list arg)
/- Application. `x` must be a `pap` value. -/
| ap  (x : varid) (ys : list arg)
/- Given `x : ty` where `ty` is a scalar type, this operation returns a value of type `tobject`.
   For small scalar values, the result is a tagged pointer, and no memory allocation is performed. -/
| box (ty : type) (x : varid)
/- Given `x : [t]object`, obtain the scalar value. -/
| unbox (x : varid)
| lit (v : litval)
/- Return `1 : uint8` iff `RC(x) > 1` -/
| is_shared (x : varid)
/- Return `1 : uint8` iff `x : tobject` is a tagged pointer (storing a scalar value). -/
| is_tagged_ptr (x : varid)

structure param :=
(x : name) (borrowed : bool) (ty : type)

inductive alt_core (fnbody : Type) : Type
| ctor (info : ctor_info) (b : fnbody) : alt_core
| default (b : fnbody) : alt_core

inductive fnbody
/- `let x : ty := e; b` -/
| vdecl (x : varid) (ty : type) (e : expr) (b : fnbody)
/- Join point declaration `let j (xs) : ty := e; b` -/
| jdecl (j : jpid) (xs : list param) (ty : type) (v : fnbody) (b : fnbody)
/- Store `y` at position `sizeof(void*)*i` in `x`. `x` must be a constructor object and `RC(x)` must be 1.
   This operation is not part of λ_pure is only used during optimization. -/
| set (x : varid) (i : nat) (y : varid) (b : fnbody)
/- Store `y : usize` at position `sizeof(void*)*i` in `x`. `x` must be a constructor object and `RC(x)` must be 1. -/
| uset (x : varid) (i : nat) (y : varid) (b : fnbody)
/- Store `y : ty` at position `sizeof(void*)*i + offset` in `x`. `x` must be a constructor object and `RC(x)` must be 1.
   `ty` must not be `object`, `tobject`, `irrelevant` nor `usize`. -/
| sset (x : varid) (i : nat) (offset : nat) (y : varid) (ty : type) (b : fnbody)
| release (x : varid) (i : nat) (b : fnbody)
/- RC increment for `object`. If c = `tt`, then `inc` must check whether `x` is a tagged pointer or not. -/
| inc (x : varid) (n : nat) (c : bool) (b : fnbody)
/- RC decrement for `object`. If c = `tt`, then `inc` must check whether `x` is a tagged pointer or not. -/
| dec (x : varid) (n : nat) (c : bool) (b : fnbody)
| mdata (d : kvmap) (b : fnbody)
| case (tid : name) (x : varid) (cs : list (alt_core fnbody))
| ret (x : varid)
/- Jump to join point `j` -/
| jmp (j : jpid) (ys : list arg)
| unreachable

abbreviation alt := alt_core fnbody
@[pattern] abbreviation alt.ctor    := @alt_core.ctor fnbody
@[pattern] abbreviation alt.default := @alt_core.default fnbody

inductive decl
| fdecl  (f : fid) (xs : list param) (ty : type) (b : fnbody)
| extern (f : fid) (xs : list param) (ty : type)

/-- `expr.is_pure e` return `tt` iff `e` is in the `λ_pure` fragment. -/
def expr.is_pure : expr → bool
| (expr.ctor _ _)  := tt
| (expr.proj _ _)  := tt
| (expr.uproj _ _) := tt
| (expr.sproj _ _) := tt
| (expr.fap _ _)   := tt
| (expr.pap _ _)   := tt
| (expr.ap _ _)    := tt
| (expr.lit _)     := tt
| _                := ff

/-- `fnbody.is_pure b` return `tt` iff `b` is in the `λ_pure` fragment. -/
mutual def fnbody.is_pure, alts.is_pure, alt.is_pure
with fnbody.is_pure : fnbody → bool
| (fnbody.vdecl _ _ e b)    := e.is_pure && b.is_pure
| (fnbody.jdecl _ _ _ e b)  := e.is_pure && b.is_pure
| (fnbody.uset _ _ _ b)     := b.is_pure
| (fnbody.sset _ _ _ _ _ b) := b.is_pure
| (fnbody.mdata _ b)        := b.is_pure
| (fnbody.case _ _ cs)      := alts.is_pure cs
| (fnbody.ret _)            := tt
| (fnbody.jmp _ _)          := tt
| fnbody.unreachable        := tt
| _                         := ff
with alts.is_pure : list alt → bool
| []      := tt
| (a::as) := a.is_pure && alts.is_pure as
with alt.is_pure : alt → bool
| (alt.ctor _ b)  := b.is_pure
| (alt.default b) := ff

abbreviation var_renaming := name_map name

class has_alpha_eqv (α : Type) :=
(aeqv : var_renaming → α → α → bool)

local notation a `=[`:50 ρ `]=`:0 b:50 := has_alpha_eqv.aeqv ρ a b

def varid.alpha_eqv (ρ : var_renaming) (v₁ v₂ : varid) : bool :=
match ρ.find v₁ with
| some v := v = v₂
| none   := v₁ = v₂

instance varid.has_aeqv : has_alpha_eqv varid := ⟨varid.alpha_eqv⟩

def arg.alpha_eqv (ρ : var_renaming) : arg → arg → bool
| (arg.var v₁)   (arg.var v₂)   := v₁ =[ρ]= v₂
| arg.irrelevant arg.irrelevant := tt
| _              _              := ff

instance arg.has_aeqv : has_alpha_eqv arg := ⟨arg.alpha_eqv⟩

def args.alpha_eqv (ρ : var_renaming) : list arg → list arg → bool
| []      []      := tt
| (a::as) (b::bs) := a =[ρ]= b && args.alpha_eqv as bs
| _       _       := ff

instance args.has_aeqv : has_alpha_eqv (list arg) := ⟨args.alpha_eqv⟩

def expr.alpha_eqv (ρ : var_renaming) : expr → expr → bool
| (expr.ctor i₁ ys₁)      (expr.ctor i₂ ys₂)      := i₁ == i₂ && ys₁ =[ρ]= ys₂
| (expr.reset x₁)         (expr.reset x₂)         := x₁ =[ρ]= x₂
| (expr.reuse x₁ i₁ ys₁)  (expr.reuse x₂ i₂ ys₂)  := x₁ =[ρ]= x₂ && i₁ == i₂ && ys₁ =[ρ]= ys₂
| (expr.proj i₁ x₁)       (expr.proj i₂ x₂)       := i₁ = i₂ && x₁ =[ρ]= x₂
| (expr.uproj i₁ x₁)      (expr.uproj i₂ x₂)      := i₁ = i₂ && x₁ =[ρ]= x₂
| (expr.sproj n₁ x₁)      (expr.sproj n₂ x₂)      := n₁ = n₂ && x₁ =[ρ]= x₂
| (expr.fap c₁ ys₁)       (expr.fap c₂ ys₂)       := c₁ = c₂ && ys₁ =[ρ]= ys₂
| (expr.pap c₁ ys₁)       (expr.pap c₂ ys₂)       := c₁ = c₂ && ys₂ =[ρ]= ys₂
| (expr.ap x₁ ys₁)        (expr.ap x₂ ys₂)        := x₁ =[ρ]= x₂ && ys₁ =[ρ]= ys₂
| (expr.box ty₁ x₁)       (expr.box ty₂ x₂)       := ty₁ == ty₂ && x₁ =[ρ]= x₂
| (expr.unbox x₁)         (expr.unbox x₂)         := x₁ =[ρ]= x₂
| (expr.lit v₁)           (expr.lit v₂)           := v₁ == v₂
| (expr.is_shared x₁)     (expr.is_shared x₂)     := x₁ =[ρ]= x₂
| (expr.is_tagged_ptr x₁) (expr.is_tagged_ptr x₂) := x₁ =[ρ]= x₂
| _                        _                      := ff

instance expr.has_aeqv : has_alpha_eqv expr:= ⟨expr.alpha_eqv⟩

def add_var_rename (ρ : var_renaming) (x₁ x₂ : name) :=
if x₁ = x₂ then ρ else ρ.insert x₁ x₂

def add_param_rename (ρ : var_renaming) (p₁ p₂ : param) : option var_renaming :=
if p₁.ty == p₂.ty && p₁.borrowed = p₂.borrowed then some (add_var_rename ρ p₁.x p₂.x)
else none

def add_params_rename : var_renaming → list param → list param → option var_renaming
| ρ (p₁::ps₁) (p₂::ps₂) := do ρ ← add_param_rename ρ p₁ p₂, add_params_rename ρ ps₁ ps₂
| ρ []        []        := some ρ
| _ _         _         := none

mutual def fnbody.alpha_eqv, alts.alpha_eqv, alt.alpha_eqv
with fnbody.alpha_eqv : var_renaming → fnbody → fnbody → bool
| ρ (fnbody.vdecl x₁ t₁ v₁ b₁)      (fnbody.vdecl x₂ t₂ v₂ b₂)        := t₁ == t₂ && v₁ =[ρ]= v₂ && fnbody.alpha_eqv (add_var_rename ρ x₁ x₂) b₁ b₂
| ρ (fnbody.jdecl j₁ ys₁ t₁ v₁ b₁)  (fnbody.jdecl j₂ ys₂ t₂ v₂ b₂)    :=
  (match add_params_rename ρ ys₁ ys₂ with
   | some ρ' := t₁ == t₂ && fnbody.alpha_eqv ρ' v₁ v₂ && fnbody.alpha_eqv (add_var_rename ρ j₁ j₂) b₁ b₂
   | none    := ff)
| ρ (fnbody.set x₁ i₁ y₁ b₁)        (fnbody.set x₂ i₂ y₂ b₂)          := x₁ =[ρ]= x₂ && i₁ = i₂ && y₁ =[ρ]= y₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (fnbody.uset x₁ i₁ y₁ b₁)       (fnbody.uset x₂ i₂ y₂ b₂)         := x₁ =[ρ]= x₂ && i₁ = i₂ && y₁ =[ρ]= y₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (fnbody.sset x₁ i₁ o₁ y₁ t₁ b₁) (fnbody.sset x₂ i₂ o₂ y₂ t₂ b₂)   :=
  x₁ =[ρ]= x₂ && i₁ = i₂ && o₁ = o₂ && y₁ =[ρ]= y₂ && t₁ == t₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (fnbody.release x₁ i₁ b₁)       (fnbody.release x₂ i₂ b₂)         := x₁ =[ρ]= x₂ && i₁ = i₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (fnbody.inc x₁ n₁ c₁ b₁)        (fnbody.inc x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ = n₂ && c₁ = c₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (fnbody.dec x₁ n₁ c₁ b₁)        (fnbody.dec x₂ n₂ c₂ b₂)          := x₁ =[ρ]= x₂ && n₁ = n₂ && c₁ = c₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (fnbody.mdata m₁ b₁)            (fnbody.mdata m₂ b₂)              := m₁ == m₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (fnbody.case n₁ x₁ as₁)         (fnbody.case n₂ x₂ as₂)           := n₁ = n₂ && x₁ =[ρ]= x₂ && alts.alpha_eqv ρ as₁ as₂
| ρ (fnbody.jmp j₁ ys₁)             (fnbody.jmp j₂ ys₂)               := j₁ = j₂ && ys₁ =[ρ]= ys₂
| ρ (fnbody.ret x₁)                 (fnbody.ret x₂)                   := x₁ =[ρ]= x₂
| _ fnbody.unreachable              fnbody.unreachable                := tt
| _ _                               _                                 := ff
with alts.alpha_eqv : var_renaming → list alt → list alt → bool
| _ []        []        := tt
| ρ (a₁::as₁) (a₂::as₂) := alt.alpha_eqv ρ a₁ a₂ && alts.alpha_eqv ρ as₁ as₂
| _ _         _         := ff
with alt.alpha_eqv : var_renaming → alt → alt → bool
| ρ (alt.ctor i₁ b₁) (alt.ctor i₂ b₂) := i₁ == i₂ && fnbody.alpha_eqv ρ b₁ b₂
| ρ (alt.default b₁) (alt.default b₂) := fnbody.alpha_eqv ρ b₁ b₂
| _ _                _                := ff

def fnbody.beq (b₁ b₂ : fnbody) : bool :=
fnbody.alpha_eqv mk_name_map b₁ b₂

instance fnbody.has_beq : has_beq fnbody := ⟨fnbody.beq⟩

abbreviation var_set := name_set

section free_variables
abbreviation collector := name_set → name_set → name_set

@[inline] private def skip : collector :=
λ bv fv, fv

@[inline] private def var.collect (x : varid) : collector :=
λ bv fv, if bv.contains x then fv else fv.insert x

@[inline] private def with_bv (x : varid) : collector → collector :=
λ k bv fv, k (bv.insert x) fv

@[inline] private def with_params (ys : list param) : collector → collector :=
λ k bv fv, k (ys.foldl (λ bv ⟨x, _, _⟩, bv.insert x) bv) fv

@[inline] private def seq : collector → collector → collector :=
λ k₁ k₂ bv fv, k₂ bv (k₁ bv fv)

local infix *> := seq

private def arg.collect : arg → collector
| (arg.var x) := var.collect x
| irrelevant  := skip

private def args.collect : list arg → collector
| []      := skip
| (a::as) := arg.collect a *> args.collect as

private def expr.collect : expr → collector
| (expr.ctor i ys)       := args.collect ys
| (expr.reset x)         := var.collect x
| (expr.reuse x i ys)    := var.collect x *> args.collect ys
| (expr.proj i x)        := var.collect x
| (expr.uproj i x)       := var.collect x
| (expr.sproj n x)       := var.collect x
| (expr.fap c ys)        := args.collect ys
| (expr.pap c ys)        := args.collect ys
| (expr.ap x ys)         := var.collect x *> args.collect ys
| (expr.box ty x)        := var.collect x
| (expr.unbox x)         := var.collect x
| (expr.lit v)           := skip
| (expr.is_shared x)     := var.collect x
| (expr.is_tagged_ptr x) := var.collect x

private mutual def fnbody.collect, alts.collect, alt.collect
with fnbody.collect : fnbody → collector
| (fnbody.vdecl x _ v b)    := expr.collect v *> with_bv x (fnbody.collect b)
| (fnbody.jdecl j ys _ v b) := with_params ys (fnbody.collect v) *> with_bv j (fnbody.collect b)
| (fnbody.set x _ y b)      := var.collect x *> var.collect y *> fnbody.collect b
| (fnbody.uset x _ y b)     := var.collect x *> var.collect y *> fnbody.collect b
| (fnbody.sset x _ _ y _ b) := var.collect x *> var.collect y *> fnbody.collect b
| (fnbody.release x _ b)    := var.collect x *> fnbody.collect b
| (fnbody.inc x _ _ b)      := var.collect x *> fnbody.collect b
| (fnbody.dec x _ _ b)      := var.collect x *> fnbody.collect b
| (fnbody.mdata _ b)        := fnbody.collect b
| (fnbody.case _ x as)      := var.collect x *> alts.collect as
| (fnbody.jmp j ys)         := var.collect j *> args.collect ys
| (fnbody.ret x)            := var.collect x
| fnbody.unreachable        := skip
with alts.collect : list alt → collector
| []      := skip
| (a::as) := alt.collect a *> alts.collect as
with alt.collect : alt → collector
| (alt.ctor _ b)  := fnbody.collect b
| (alt.default b) := fnbody.collect b

def free_vars (b : fnbody) : var_set :=
fnbody.collect b mk_name_set mk_name_set

end free_variables

end ir
end lean
