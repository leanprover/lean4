/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.format init.lean.parser.identifier
import init.lean.ir.reserved init.lean.ir.ir

namespace lean
namespace ir
open lean.format

def should_escape_aux : nat → bool → string.iterator → bool
| 0     _ _   := ff
| (n+1) tt it := !is_id_first it.curr || should_escape_aux n ff it.next
| (n+1) ff it := !is_id_rest it.curr  || should_escape_aux n ff it.next

def should_escape (s : string) : bool :=
should_escape_aux s.length tt s.mk_iterator

def escape_string (s : string) : string :=
to_string id_begin_escape ++ s ++ to_string id_end_escape

def id_part.to_string (s : string) : string :=
if should_escape s then escape_string s else s

def id.to_string : name → string
| name.anonymous                     := escape_string ""
| (name.mk_string name.anonymous s)  := if is_reserved s then escape_string s else id_part.to_string s
| (name.mk_numeral name.anonymous v) := escape_string (to_string v)
| (name.mk_string n s)               := id.to_string n ++ "." ++ id_part.to_string s
| (name.mk_numeral n v)              := id.to_string n ++ "." ++ escape_string (to_string v)

instance var.has_to_format : has_to_format var         := ⟨λ v, id.to_string v⟩
instance blockid.has_to_format : has_to_format blockid := ⟨λ b, id.to_string b⟩
instance fnid.has_to_format : has_to_format fnid       := ⟨λ f, id.to_string f⟩
instance fnid.has_to_string : has_to_string fnid       := ⟨λ f, id.to_string f⟩
instance tag.has_to_format : has_to_format tag         := infer_instance_as (has_to_format uint16)
instance tag.has_to_string : has_to_string tag         := infer_instance_as (has_to_string uint16)

def type.to_format : type → format
| type.bool   := "bool"   | type.byte   := "byte"
| type.uint16 := "uint16" | type.uint32 := "uint32" | type.uint64 := "uint64" | type.usize := "usize"
| type.int16  := "int16"  | type.int32  := "int32"   | type.int64  := "int64"
| type.float  := "float"  | type.double := "double"  | type.object := "object"

instance type.has_to_format : has_to_format type := ⟨type.to_format⟩
instance type.has_to_string : has_to_string type := ⟨pretty ∘ to_fmt⟩

def assign_unop.to_format : assign_unop → format
| assign_unop.not           := "not"        | assign_unop.neg          := "neg"       | assign_unop.ineg    := "ineg"
| assign_unop.nat2int       := "nat2int"
| assign_unop.is_scalar     := "is_scalar"  | assign_unop.is_shared    := "is_shared" | assign_unop.is_null := "is_null"
| assign_unop.box           := "box"        | assign_unop.unbox        := "unbox"
| assign_unop.cast          := "cast"
| assign_unop.array_copy    := "array_copy" | assign_unop.sarray_copy  := "sarray_copy"
| assign_unop.array_size    := "array_size" | assign_unop.sarray_size  := "sarray_size"
| assign_unop.string_len    := "string_len" | assign_unop.succ         := "succ"
| assign_unop.tag           := "tag"        | assign_unop.tag_ref      := "tag_ref"

instance assign_unop.has_to_format : has_to_format assign_unop := ⟨assign_unop.to_format⟩
instance assign_unop.has_to_string : has_to_string assign_unop := ⟨pretty ∘ to_fmt⟩

def assign_binop.to_format : assign_binop → format
| assign_binop.add  := "add"  | assign_binop.sub  := "sub"  | assign_binop.mul  := "mul"   | assign_binop.div   := "div"  | assign_binop.mod  := "mod"
| assign_binop.iadd := "iadd" | assign_binop.isub := "isub" | assign_binop.imul := "imul"  | assign_binop.idiv  := "idiv" | assign_binop.imod := "imod"
| assign_binop.shl  := "shl"  | assign_binop.shr  := "shr"
| assign_binop.and  := "and"  | assign_binop.or   := "or"   | assign_binop.xor  := "xor"
| assign_binop.le   := "le"   | assign_binop.lt   := "lt"   | assign_binop.eq   := "eq"  | assign_binop.ne   := "ne"
| assign_binop.ile  := "ile"  | assign_binop.ilt  := "ilt"  | assign_binop.ieq  := "ieq" | assign_binop.ine  := "ine"
| assign_binop.array_read    := "array_read"
| assign_binop.array_push    := "array_push"
| assign_binop.string_push   := "string_push"
| assign_binop.string_append := "string_append"

instance assign_binop.has_to_format : has_to_format assign_binop := ⟨assign_binop.to_format⟩
instance assign_binop.has_to_string : has_to_string assign_binop := ⟨pretty ∘ to_fmt⟩

def unop.to_format : unop → format
| unop.inc_ref   := "inc_ref"   | unop.dec_ref := "dec_ref"  | unop.dec_sref := "dec_sref"
| unop.inc       := "inc"       | unop.dec     := "dec"
| unop.free      := "free"      | unop.dealloc := "dealloc"
| unop.array_pop := "array_pop" | unop.sarray_pop := "sarray_pop"

instance unop.has_to_format : has_to_format unop := ⟨unop.to_format⟩
instance unop.has_to_string : has_to_string unop := ⟨pretty ∘ to_fmt⟩

def literal.to_format : literal → format
| (literal.bool b)  := to_fmt b
| (literal.str s)   := repr s
| (literal.num n)   := to_fmt n
| (literal.float n) := to_fmt n

instance literal.has_to_format : has_to_format literal := ⟨literal.to_format⟩
instance literal.has_to_string : has_to_string literal := ⟨pretty ∘ to_fmt⟩

def sizet_entry.to_format : nat × type → format
| (1, ty) := to_fmt ty
| (n, ty) := to_fmt n ++ ":" ++ to_fmt ty

def instr.to_format : instr → format
| (instr.assign x ty y)             := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt y
| (instr.assign_lit x ty lit)       := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt lit
| (instr.assign_unop x ty op y)     := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt op ++ " " ++ to_fmt y
| (instr.assign_binop x ty op y z)  := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt op ++ " " ++ to_fmt y ++ " " ++ to_fmt z
| (instr.unop op x)                 := to_fmt op ++ " " ++ to_fmt x
| (instr.call x fn ys)              := to_fmt x ++ " := call " ++ to_fmt fn ++ prefix_join " " ys
| (instr.cnstr o t n sz)            := to_fmt o ++ " := cnstr " ++ to_fmt t ++ " " ++ to_fmt n ++ " " ++ to_fmt sz
| (instr.set o i x)                 := to_fmt "set " ++ to_fmt o ++ " " ++ to_fmt i ++ " " ++ to_fmt x
| (instr.get x o i)                 := to_fmt x ++ " := get " ++ to_fmt o ++ " " ++ to_fmt i
| (instr.sset o d v)                := to_fmt "sset " ++ to_fmt o ++ " " ++ to_fmt d ++ " " ++ to_fmt v
| (instr.sget x ty o d)             := to_fmt x ++ " : " ++ to_fmt ty ++ " := sget " ++ to_fmt o ++ " " ++ to_fmt d
| (instr.closure x f ys)            := to_fmt x ++ " := closure " ++ to_fmt f ++ prefix_join " " ys
| (instr.apply x ys)                := to_fmt x ++ " := apply " ++ join_sep ys " "
| (instr.array a sz c)              := to_fmt a ++ " := array " ++ to_fmt sz ++ " " ++ to_fmt c
| (instr.sarray a ty sz c)          := to_fmt a ++ " := sarray " ++ to_fmt ty ++ " " ++ to_fmt sz ++ " " ++ to_fmt c
| (instr.array_write a i v)         := "array_write " ++ to_fmt a ++ " " ++ to_fmt i ++ " " ++ to_fmt v

instance instr.has_to_format : has_to_format instr := ⟨instr.to_format⟩
instance instr.has_to_string : has_to_string instr := ⟨pretty ∘ to_fmt⟩

def phi.to_format : phi → format
| {x := x, ty := ty, ys := ys} := to_fmt x ++ " : " ++ to_fmt ty ++  " := phi " ++ join_sep ys " "

instance phi.has_to_format : has_to_format phi := ⟨phi.to_format⟩
instance phi.has_to_string : has_to_string phi := ⟨pretty ∘ to_fmt⟩

def terminator.to_format : terminator → format
| (terminator.ret y)     := "ret " ++ to_fmt y
| (terminator.case x bs) := "case " ++ to_fmt x ++ " " ++ to_fmt bs
| (terminator.jmp b)     := "jmp " ++ to_fmt b

instance terminator.has_to_format : has_to_format terminator := ⟨terminator.to_format⟩
instance terminator.has_to_string : has_to_string terminator := ⟨pretty ∘ to_fmt⟩

def block.to_format : block → format
| {id := id, phis := ps, instrs := is, term := t} :=
  to_fmt id ++ ":" ++ nest 2 (line ++ join_suffix ps (";" ++ line) ++ join_suffix is (";" ++ line) ++ to_fmt t ++ ";")

instance block.has_to_format : has_to_format block := ⟨block.to_format⟩
instance block.has_to_string : has_to_string block := ⟨pretty ∘ to_fmt⟩

def arg.to_format : arg → format
| {n := n, ty := ty} := "(" ++ to_fmt n ++ " : " ++ to_fmt ty ++ ")"

instance arg.has_to_format : has_to_format arg := ⟨arg.to_format⟩
instance arg.has_to_string : has_to_string arg := ⟨pretty ∘ to_fmt⟩

def result.to_format : result → format
| {ty := ty, ..} := to_fmt ty

instance result.has_to_format : has_to_format result := ⟨result.to_format⟩
instance result.has_to_string : has_to_string result := ⟨pretty ∘ to_fmt⟩

def header.to_format (h : header) : format :=
to_fmt h.name ++ " " ++ join_sep h.args " " ++ " : " ++ to_fmt h.return

instance header.has_to_format : has_to_format header := ⟨header.to_format⟩
instance header.has_to_string : has_to_string header := ⟨pretty ∘ to_fmt⟩

def decl.to_format : decl → format
| (decl.defn h bs)  := "def " ++ to_fmt h ++ " := " ++ line ++ join_sep bs line ++ line
| (decl.external h) := "external " ++ to_fmt h

instance decl.has_to_format : has_to_format decl := ⟨decl.to_format⟩
instance decl.has_to_string : has_to_string decl := ⟨pretty ∘ to_fmt⟩

@[inline] def phi.decorate_error {α m} [monad_except format m] (p : phi) (a : m α) : m α :=
catch a (λ e, throw ("at phi '" ++ to_fmt p ++ "'" ++ line ++ e))

@[inline] def instr.decorate_error {α m} [monad_except format m] (ins : instr) (a : m α) : m α :=
catch a (λ e, throw ("at instruction '" ++ to_fmt ins ++ "'" ++ line ++ e))

@[inline] def terminator.decorate_error {α m} [monad_except format m] (t : terminator) (a : m α) : m α :=
catch a (λ e, throw ("at terminator '" ++ to_fmt t ++ "'" ++ line ++ e))

@[inline] def block.decorate_error {α m} [monad_except format m] (b : block) (a : m α) : m α :=
catch a (λ e, throw ("at block '" ++ to_fmt b.id ++ "'" ++ line ++ e))

@[inline] def header.decorate_error {α m} [monad_except format m] (h : header) (a : m α) : m α :=
catch a (λ e, throw ("error at declaration '" ++ to_fmt h.name ++ "'" ++ line ++ e))

@[inline] def decl.decorate_error {α m} [monad_except format m] (d : decl) (a : m α) : m α :=
d.header.decorate_error a

end ir
end lean
