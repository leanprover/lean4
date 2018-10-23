/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.instances init.lean.ir.format init.control.combinators

namespace lean
namespace ir
/-- Return `tt` iff `ty` is a type that may occur in signed arithmetical operations. -/
def is_signed_arith_ty (ty : type) : bool :=
match ty with
| type.int16  := tt | type.int32 := tt  | type.int64 := tt
| type.float  := tt | type.double := tt
| _ := ff

/-- Return `tt` iff `ty` is a type that may occur in arithmetical operations. -/
def is_arith_ty (ty : type) : bool :=
ty ≠ type.bool -- Recall that type.object may be encoding a big num.

/-- Return `tt` iff `ty` is a type that may occur in non floating point arithmetical operations. -/
def is_nonfloat_arith_ty (ty : type) : bool :=
is_arith_ty ty && ty ≠ type.float && ty ≠ type.double

/-- Return `tt` iff `ty` is a type that may occur in bitwise/logical operations. -/
def is_bitwise_ty (ty : type) : bool :=
match ty with
| type.bool   := tt | type.byte := tt
| type.uint16 := tt | type.uint32 := tt | type.uint64 := tt | type.usize := tt
| type.object := tt
| _ := ff

/-- Return `tt` iff `ty` is a type that may occur in bitshift operations. -/
def is_bitshift_ty (ty : type) : bool :=
match ty with
| type.byte   := tt
| type.int16  := tt | type.int32 := tt  | type.int64  := tt
| type.uint16 := tt | type.uint32 := tt | type.uint64 := tt | type.usize := tt
| _ := ff

/-- Return `tt` iff the instruction `x : r := op y` is type correct where `y : t` -/
def valid_assign_unop_types (op : assign_unop) (r : type) (t : type) : bool :=
match op with
| assign_unop.not           := t = r && is_bitwise_ty t
| assign_unop.neg           := t = r && is_signed_arith_ty t
| assign_unop.ineg          := t = r && t = type.object
| assign_unop.nat2int       := t = r && t = type.object
| assign_unop.is_scalar     := t = type.object && r = type.bool
| assign_unop.is_shared     := t = type.object && r = type.bool
| assign_unop.is_null       := t = type.object && r = type.bool
| assign_unop.array_copy    := t = type.object && r = type.object
| assign_unop.sarray_copy   := t = type.object && r = type.object
| assign_unop.unbox         := t = type.object && (r = type.uint32 || r = type.int32)
| assign_unop.box           := r = type.object && (t = type.uint32 || t = type.int32)
| assign_unop.cast          := r ≠ type.object && r ≠ type.object
| assign_unop.array_size    := r = type.usize && t = type.object
| assign_unop.sarray_size   := r = type.usize && t = type.object
| assign_unop.string_len    := r = type.usize && t = type.object
| assign_unop.succ          := r = type.object && t = type.object
| assign_unop.tag           := r = type.uint32 && t = type.object
| assign_unop.tag_ref       := r = type.uint32 && t = type.object

/-- Return `tt` iff the instruction `x : r := op y z` is type correct where `y z : t` -/
def valid_assign_binop_types (op : assign_binop) (r : type) (t₁ t₂ : type) : bool :=
match op with
| assign_binop.add  := r = t₁ && r = t₂ && is_arith_ty r
| assign_binop.sub  := r = t₁ && r = t₂ && is_arith_ty r
| assign_binop.mul  := r = t₁ && r = t₂ && is_arith_ty r
| assign_binop.div  := r = t₁ && r = t₂ && is_arith_ty r
| assign_binop.mod  := r = t₁ && r = t₂ && is_nonfloat_arith_ty r
| assign_binop.iadd := r = t₁ && r = t₂ && r = type.object
| assign_binop.isub := r = t₁ && r = t₂ && r = type.object
| assign_binop.imul := r = t₁ && r = t₂ && r = type.object
| assign_binop.idiv := r = t₁ && r = t₂ && r = type.object
| assign_binop.imod := r = t₁ && r = t₂ && r = type.object
| assign_binop.shl  := r = t₁ && r = t₂ && is_bitshift_ty r
| assign_binop.shr  := r = t₁ && r = t₂ && is_bitshift_ty r
| assign_binop.and  := r = t₁ && r = t₂ && is_bitwise_ty r
| assign_binop.or   := r = t₁ && r = t₂ && is_bitwise_ty r
| assign_binop.xor  := r = t₁ && r = t₂ && is_bitwise_ty r
| assign_binop.le   := r = type.bool && t₁ = t₂ && is_arith_ty t₁
| assign_binop.lt   := r = type.bool && t₁ = t₂ && is_arith_ty t₁
| assign_binop.eq   := r = type.bool && t₁ = t₂
| assign_binop.ne   := r = type.bool && t₁ = t₂
| assign_binop.ile  := r = type.bool && t₁ = t₂ && t₁ = type.object
| assign_binop.ilt  := r = type.bool && t₁ = t₂ && t₁ = type.object
| assign_binop.ieq  := r = type.bool && t₁ = t₂ && t₁ = type.object
| assign_binop.ine  := r = type.bool && t₁ = t₂ && t₁ = type.object
| assign_binop.array_read    := t₁ = type.object && t₂ = type.usize
| assign_binop.array_push    := r = type.object && t₁ = type.object
| assign_binop.string_push   := r = type.object && t₁ = type.object && t₂ = type.uint32
| assign_binop.string_append := r = type.object && t₁ = type.object && t₂ = type.object

@[reducible] def type_checker_m := except_t format (reader_t (environment × result) (state_t context id))

def type_checker_m.run {α} (a : type_checker_m α) (env : environment) (r : result) : except format α :=
run a (env, r) mk_context

def match_type (x : var) (t expected : type) : type_checker_m unit :=
unless (t = expected) $
  throw ("type mismatch, variable `" ++ to_fmt x ++ "` has type `" ++ to_fmt t ++ "`" ++
         ", but is expected to have type `" ++ to_fmt expected ++ "`")

def get_type (x : var) : type_checker_m type :=
do m ← get,
   match m.find x with
   | some t := pure t
   | none   := throw ("undefined variable `" ++ to_fmt x ++ "`")

def set_type (x : var) (t : type) : type_checker_m unit :=
do m ← get,
   match m.find x with
   | some t' := match_type x t' t
   | none    := put (m.insert x t)

def check_type (x : var) (t : type) : type_checker_m unit :=
do m ← get,
   match m.find x with
   | some t' := match_type x t' t
   | none    := throw ("type for variable `" ++ to_fmt x ++ "` is not available")

def check_ne_type (x : var) (t : type) : type_checker_m unit :=
do m ← get,
   match m.find x with
   | some t' := unless (t' ≠ t) $ throw ("variable `" ++ to_fmt x ++ "` must not have type `" ++ to_fmt t ++ "`")
   | none    := throw ("type for variable `" ++ to_fmt x ++ "` is not available")

def invalid_literal : type_checker_m unit :=
throw "invalid literal"

def literal.check (l : literal) (t : type) : type_checker_m unit :=
match l with
| literal.bool _  := unless (t = type.bool) invalid_literal
| literal.str  _  := unless (t = type.object) invalid_literal
| literal.num  v  := unless (is_nonfloat_arith_ty t) invalid_literal *>
                     when (v < 0) (unless (is_signed_arith_ty t) invalid_literal)
| literal.float _ := unless (t = type.float || t = type.double) invalid_literal

def get_decl (f : fnid) : type_checker_m decl :=
do (env, _) ← read,
   match env f with
   | some d := pure d
   | none   := throw ("unknown function `" ++ to_fmt f ++ "`")

def set_result_types : var → result → type_checker_m unit
| x ⟨t⟩ := set_type x t

def instr.infer_types (ins : instr) : type_checker_m unit :=
ins.decorate_error $
match ins with
| (instr.assign x t y)            := set_type x t
| (instr.assign_lit x t l)        := set_type x t
| (instr.assign_unop x t op y)    := set_type x t
| (instr.assign_binop x t op y z) := set_type x t
| (instr.call x f ys)      := do d ← get_decl f, set_result_types x d.header.return
| (instr.cnstr o _ _ _)    := set_type o type.object
| (instr.get x o _)        := set_type x type.object
| (instr.sget x t o _)     := set_type x t
| (instr.closure x f ys)   := set_type x type.object
| (instr.apply x ys)       := set_type x type.object
| (instr.array a sz c)     := set_type a type.object
| (instr.sarray a t sz c)  := set_type a type.object
| other                    := pure ()

def phi.infer_types (p : phi) : type_checker_m unit :=
p.decorate_error $ set_type p.x p.ty

def arg.infer_types (a : arg) : type_checker_m unit :=
set_type a.n a.ty

def block.infer_types (b : block) : type_checker_m unit :=
b.decorate_error $ b.phis.mfor phi.infer_types *> b.instrs.mfor instr.infer_types

def decl.infer_types : decl → type_checker_m context
| (decl.defn h bs) := h.decorate_error $ h.args.mfor arg.infer_types *> bs.mfor block.infer_types *> get
| _                := get

/-- Return context with the type of variables used in the given declaration.
    It does not check whether instructions are being used correctly. -/
def infer_types (d : decl) (env : environment) : except format context :=
d.infer_types.run env d.header.return

def check_arg_types : list var → list arg → type_checker_m unit
| []      []      := pure ()
| (x::xs) (t::ts) := check_type x t.ty *> check_arg_types xs ts
| _       _       := throw "unexpected number of arguments"

/-- Check whether the given instruction is type correct or not. It assumes the context already contains
    the type of all variables. -/
def instr.check (ins : instr) : type_checker_m unit :=
ins.decorate_error $
match ins with
| (instr.assign x t y)             := do t₁ ← get_type y, unless (t = t₁) (throw "invalid assignment")
| (instr.assign_lit x t l)         := l.check t
| (instr.assign_unop x t op y)     := do t₁ ← get_type y, unless (valid_assign_unop_types op t t₁) $ throw "invalid unary operation"
| (instr.assign_binop x t op y z)  := do t₁ ← get_type y, t₂ ← get_type z, unless (valid_assign_binop_types op t t₁ t₂) $ throw "invalid binary operation"
| (instr.unop _ x)          := check_type x type.object
| (instr.call xs f ys)      := do d ← get_decl f, check_arg_types ys d.header.args
| (instr.cnstr o _ _ _)     := pure ()
| (instr.set o _ x)         := check_type o type.object *> check_type x type.object
| (instr.get x o _)         := check_type o type.object
| (instr.sset o _ x)        := check_type o type.object *> check_ne_type x type.object
| (instr.sget x t o _)      := check_type o type.object *> check_ne_type x type.object
| (instr.closure x f ys)    := do ys.mfor (flip check_type type.object), d ← get_decl f,
                                 unless (d.header.args.length ≥ ys.length) $ throw "too many arguments",
                                 d.header.args.mfor (λ a, unless (a.ty = type.object) $ throw "invalid closure, arguments must have type object")
| (instr.apply x ys)        := ys.mfor (flip check_type type.object)
| (instr.array a sz c)      := check_type sz type.usize *> check_type c type.usize
| (instr.sarray a t sz c)   := check_type sz type.usize *> check_type c type.usize *> unless (t ≠ type.object) (throw "invalid scalar array")
| (instr.array_write a i _) := check_type a type.object *> check_type i type.usize

def phi.check (p : phi) : type_checker_m unit :=
p.decorate_error $ p.ys.mfor (flip check_type p.ty)

def check_result_type : var → result → type_checker_m unit
| x ⟨t⟩ := check_type x t

def terminator.check (term : terminator) : type_checker_m unit :=
term.decorate_error $
match term with
| (terminator.ret y)    := do (_, r) ← read, check_result_type y r
| (terminator.case x _) := do t ← get_type x, unless (t = type.bool || t = type.uint32) $ throw "variable must be an uint32 or bool"
| (terminator.jmp _)    := pure ()

def block.check (b : block) : type_checker_m unit :=
b.decorate_error $ b.phis.mfor phi.check *> b.instrs.mfor instr.check *> b.term.check

def decl.check : decl → type_checker_m unit
| (decl.defn h bs) := bs.mfor block.check
| _                := pure ()

def type_check (d : decl) (env : environment := λ _, none) : except format context :=
(d.infer_types *> d.check *> get).run env d.header.return

end ir
end lean
