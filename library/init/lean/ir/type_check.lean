/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.ir init.lean.ir.format init.control.combinators

namespace lean
namespace ir
/-- Return `tt` iff `ty` is a type that may occur in signed arithmetical operations. -/
def is_signed_arith_ty (ty : type) : bool :=
match ty with
| type.int16  := tt | type.int32 := tt  | type.int64 := tt
| type.float  := tt | type.double := tt
| type.object := tt -- big numbers
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
def valid_unop_types (op : unop) (r : type) (t : type) : bool :=
match op with
| unop.not          := t = r && is_bitwise_ty t
| unop.neg          := t = r && is_signed_arith_ty t
| unop.is_scalar    := t = type.object && r = type.bool
| unop.is_shared    := t = type.object && r = type.bool
| unop.array_copy   := t = type.object && r = type.object
| unop.sarray_copy  := t = type.object && r = type.object
| unop.unbox        := t = type.object && (r = type.uint32 || r = type.int32)
| unop.box          := r = type.object && (t = type.uint32 || t = type.int32)
| unop.cast         := r ≠ type.object && r ≠ type.object

/-- Return `tt` iff the instruction `x : r := op y z` is type correct where `y z : t` -/
def valid_binop_types (op : binop) (r : type) (t₁ t₂ : type) : bool :=
match op with
| binop.add  := r = t₁ && r = t₂ && is_arith_ty r
| binop.sub  := r = t₁ && r = t₂ && is_arith_ty r
| binop.mul  := r = t₁ && r = t₂ && is_arith_ty r
| binop.div  := r = t₁ && r = t₂ && is_arith_ty r
| binop.mod  := r = t₁ && r = t₂ && is_nonfloat_arith_ty r
| binop.shl  := r = t₁ && r = t₂ && is_bitshift_ty r
| binop.shr  := r = t₁ && r = t₂ && is_bitshift_ty r
| binop.and  := r = t₁ && r = t₂ && is_bitwise_ty r
| binop.or   := r = t₁ && r = t₂ && is_bitwise_ty r
| binop.xor  := r = t₁ && r = t₂ && is_bitwise_ty r
| binop.le   := r = type.bool && t₁ = t₂ && is_arith_ty t₁
| binop.ge   := r = type.bool && t₁ = t₂ && is_arith_ty t₁
| binop.lt   := r = type.bool && t₁ = t₂ && is_arith_ty t₁
| binop.gt   := r = type.bool && t₁ = t₂ && is_arith_ty t₁
| binop.eq   := r = type.bool && t₁ = t₂
| binop.ne   := r = type.bool && t₁ = t₂
| binop.read := t₁ = type.object && t₂ = type.usize

@[reducible] def type_checker_m := except_t format (reader_t (environment × list result) (state_t context id))

def type_checker_m.run {α} (a : type_checker_m α) (env : environment) (r : list result) : except format α :=
run a (env, r) mk_context

def match_type (x : var) (t expected : type) : type_checker_m unit :=
unless (t = expected) $
  throw ("type mismatch, variable `" ++ to_fmt x ++ "` has type `" ++ to_fmt t ++ "`" ++
         ", but is expected to have type `" ++ to_fmt expected ++ "`")

def get_type (x : var) : type_checker_m type :=
do m ← get,
   match m.find x with
   | some t := return t
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
| literal.num  v  := unless (is_nonfloat_arith_ty t) invalid_literal >>
                     when (v < 0) (unless (is_signed_arith_ty t) invalid_literal)
| literal.float _ := unless (t = type.float || t = type.double) invalid_literal

def get_decl (f : fnid) : type_checker_m decl :=
do (env, _) ← read,
   match env f with
   | some d := return d
   | none   := throw ("unknown function `" ++ to_fmt f ++ "`")

def set_result_types : list var → list result → type_checker_m unit
| []      []      := return ()
| (x::xs) (t::ts) := set_type x t.ty >> set_result_types xs ts
| _       _       := throw "unexpected number of return values"

def instr.infer_types (ins : instr) : type_checker_m unit :=
ins.decorate_error $
match ins with
| (instr.lit x t l)        := set_type x t
| (instr.unop x t op y)    := set_type x t
| (instr.binop x t op y z) := set_type x t
| (instr.call xs f ys)     := do d ← get_decl f, set_result_types xs d.header.return
| (instr.cnstr o _ _ _)    := set_type o type.object
| (instr.get x o _)        := set_type x type.object
| (instr.sget x t o _)     := set_type x t
| (instr.closure x f ys)   := set_type x type.object
| (instr.apply x ys)       := set_type x type.object
| (instr.array a sz c)     := set_type a type.object
| (instr.sarray a t sz c)  := set_type a type.object
| other                    := return ()

def phi.infer_types (p : phi) : type_checker_m unit :=
p.decorate_error $ set_type p.x p.ty

def arg.infer_types (a : arg) : type_checker_m unit :=
set_type a.n a.ty

def block.infer_types (b : block) : type_checker_m unit :=
b.decorate_error $ b.phis.mfor phi.infer_types >> b.instrs.mfor instr.infer_types

def decl.infer_types : decl → type_checker_m context
| (decl.defn h bs) := h.decorate_error $ h.args.mfor arg.infer_types >> bs.mfor block.infer_types >> get
| _                := get

/-- Return context with the type of variables used in the given declaration.
    It does not check whether instructions are being used correctly. -/
def infer_types (d : decl) (env : environment) : except format context :=
d.infer_types.run env d.header.return

def check_arg_types : list var → list arg → type_checker_m unit
| []      []      := return ()
| (x::xs) (t::ts) := check_type x t.ty >> check_arg_types xs ts
| _       _       := throw "unexpected number of arguments"

/-- Check whether the given instruction is type correct or not. It assumes the context already contains
    the type of all variables. -/
def instr.check (ins : instr) : type_checker_m unit :=
ins.decorate_error $
match ins with
| (instr.lit x t l)        := l.check t
| (instr.unop x t op y)    := do t₁ ← get_type y, unless (valid_unop_types op t t₁) $ throw "invalid unary operation"
| (instr.binop x t op y z) := do t₁ ← get_type y, t₂ ← get_type z, unless (valid_binop_types op t t₁ t₂) $ throw "invalid binary operation"
| (instr.call xs f ys)     := do d ← get_decl f, check_arg_types ys d.header.args
| (instr.cnstr o _ _ _)    := return ()
| (instr.set o _ x)        := check_type o type.object >> check_type x type.object
| (instr.get x o _)        := check_type o type.object
| (instr.sset o _ x)       := check_type o type.object >> check_ne_type x type.object
| (instr.sget x t o _)     := check_type o type.object >> check_ne_type x type.object
| (instr.closure x f ys)   := do ys.mfor (flip check_type type.object), d ← get_decl f,
                                 unless (d.header.return.length = 1) $ throw "unexpected number of return values",
                                 unless (d.header.args.length = ys.length) $ throw "unexpected number of arguments",
                                 d.header.args.mfor (λ a, unless (a.ty = type.object) $ throw "invalid closure, arguments must have type object")
| (instr.apply x ys)       := ys.mfor (flip check_type type.object)
| (instr.array a sz c)     := check_type sz type.usize >> check_type c type.usize
| (instr.write a i v)      := check_type a type.object >> check_type i type.usize >> check_type v type.object
| (instr.sarray a t sz c)  := check_type sz type.usize >> check_type c type.usize >> unless (t ≠ type.object) (throw "invalid scalar array")
| (instr.swrite a i v)     := check_type a type.object >> check_type i type.usize >> check_ne_type v type.object
| (instr.unary _ x)        := check_type x type.object

def phi.check (p : phi) : type_checker_m unit :=
p.decorate_error $ p.ys.mfor (flip check_type p.ty)

def check_result_types : list var → list result → type_checker_m unit
| []      []      := return ()
| (x::xs) (t::ts) := check_type x t.ty >> check_result_types xs ts
| _       _       := throw "unexpected number of return values"

def terminator.check (term : terminator) : type_checker_m unit :=
term.decorate_error $
match term with
| (terminator.ret ys)   := do (_, rs) ← read, check_result_types ys rs
| (terminator.case x _) := do t ← get_type x, unless (t = type.object || t = type.bool) $ throw "variable must be an object or bool"
| (terminator.jmp _)    := return ()

def block.check (b : block) : type_checker_m unit :=
b.decorate_error $ b.phis.mfor phi.check >> b.instrs.mfor instr.check >> b.term.check

def decl.check : decl → type_checker_m unit
| (decl.defn h bs) := h.decorate_error $ bs.mfor block.check
| _                := return ()

def type_check (d : decl) (env : environment := λ _, none) : except format context :=
(d.infer_types >> d.check >> get).run env d.header.return

end ir
end lean
