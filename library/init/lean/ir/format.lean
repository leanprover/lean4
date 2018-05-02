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
instance tag.has_to_format : has_to_format tag         := infer_instance_as (has_to_format uint16)

def type.to_format : type → format
| type.bool   := "bool"   | type.byte   := "byte"
| type.uint16 := "uint16" | type.uint32 := "uint32" | type.uint64 := "uint64"
| type.int16  := "int16"  | type.int32  := "int32"   | type.int64  := "int64"
| type.float  := "float"  | type.double := "double"  | type.object := "object"

instance type.has_to_format : has_to_format type := ⟨type.to_format⟩
instance type.has_to_string : has_to_string type := ⟨pretty ∘ to_fmt⟩

def unop.to_format : unop → format
| unop.not         := "not"        | unop.neg         := "neg"
| unop.scalar      := "scalar"     | unop.shared      := "shared"
| unop.unbox       := "unbox"      | unop.box         := "box"
| unop.copy_array  := "copy_array" | unop.copy_sarray := "copy_sarray"

instance unop.has_to_format : has_to_format unop := ⟨unop.to_format⟩
instance unop.has_to_string : has_to_string unop := ⟨pretty ∘ to_fmt⟩

def binop.to_format : binop → format
| binop.add  := "add"  | binop.sub  := "sub" | binop.mul  := "mul"  | binop.div  := "div"
| binop.mod  := "mod"  | binop.shl  := "shl" | binop.shr  := "shr"  | binop.ashr := "ashr"
| binop.and  := "and"  | binop.or   := "or"  | binop.xor  := "xor"  | binop.le   := "le"
| binop.ge   := "ge"   | binop.lt   := "lt"  | binop.gt   := "gt"   | binop.eq   := "eq"
| binop.ne   := "ne"

instance binop.has_to_format : has_to_format binop := ⟨binop.to_format⟩
instance binop.has_to_string : has_to_string binop := ⟨pretty ∘ to_fmt⟩

def literal.to_format : literal → format
| (literal.bool b)  := to_fmt b
| (literal.str s)   := repr s
| (literal.num n)   := to_fmt n
| (literal.float n) := to_fmt n

instance literal.has_to_format : has_to_format literal := ⟨literal.to_format⟩
instance literal.has_to_string : has_to_string literal := ⟨pretty ∘ to_fmt⟩

def instr.to_format : instr → format
| (instr.lit x ty lit)       := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt lit
| (instr.cast x ty y)        := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt y
| (instr.unop x ty op y)     := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt op ++ " " ++ to_fmt y
| (instr.binop x ty op y z)  := to_fmt x ++ " : " ++ to_fmt ty ++ " := " ++ to_fmt op ++ " " ++ to_fmt y ++ " " ++ to_fmt z
| (instr.call xs fn ys)      := join_with xs " " ++ " := call " ++ to_fmt fn ++ " " ++ join_with ys " "
| (instr.cnstr o t n sz)     := to_fmt o ++ " := cnstr " ++ to_fmt t ++ " " ++ to_fmt n ++ " " ++ to_fmt sz
| (instr.set o i x)          := to_fmt "set " ++ to_fmt o ++ " " ++ to_fmt i ++ " " ++ to_fmt x
| (instr.get x o i)          := to_fmt x ++ " := get " ++ to_fmt o ++ " " ++ to_fmt i
| (instr.sset o d v)         := to_fmt "sset " ++ to_fmt o ++ " " ++ to_fmt d ++ " " ++ to_fmt v
| (instr.sget x ty o d)      := to_fmt x ++ " : " ++ to_fmt ty ++ " := sget " ++ to_fmt o ++ " " ++ to_fmt d
| (instr.closure x f ys)     := to_fmt x ++ " := closure " ++ to_fmt f ++ join_with ys " "
| (instr.apply x ys)         := to_fmt x ++ " := apply " ++ join_with ys " "
| (instr.array a sz c)       := to_fmt a ++ " := array " ++ to_fmt sz ++ " " ++ to_fmt c
| (instr.write a i v)        := "write " ++ to_fmt a ++ " " ++ to_fmt i ++ " " ++ to_fmt v
| (instr.read x a i)         := to_fmt x ++ " := read " ++ to_fmt a ++ " " ++ to_fmt i
| (instr.sarray a ty sz c)   := to_fmt a ++ " := sarray " ++ to_fmt ty ++ " " ++ to_fmt sz ++ " " ++ to_fmt c
| (instr.swrite a i v)       := "swrite " ++ to_fmt a ++ " " ++ to_fmt i ++ " " ++ to_fmt v
| (instr.sread x ty a i)     := to_fmt x ++ " : " ++ to_fmt ty  ++ " := sread " ++ to_fmt a ++ " " ++ to_fmt i
| (instr.inc x)              := "inc " ++ to_fmt x
| (instr.decs x)             := "decs " ++ to_fmt x
| (instr.free x)             := "free " ++ to_fmt x
| (instr.dec x)              := "dec " ++ to_fmt x

instance instr.has_to_format : has_to_format instr := ⟨instr.to_format⟩
instance instr.has_to_string : has_to_string instr := ⟨pretty ∘ to_fmt⟩

def phi.to_format : phi → format
| {x := x, ty := ty, ys := ys} := to_fmt x ++ " : " ++ to_fmt ty ++  " := phi " ++ join_with ys " "

instance phi.has_to_format : has_to_format phi := ⟨phi.to_format⟩
instance phi.has_to_string : has_to_string phi := ⟨pretty ∘ to_fmt⟩

def terminator.to_format : terminator → format
| (terminator.ret ys)    := "ret " ++ join_with ys " "
| (terminator.case x bs) := "case " ++ to_fmt x ++ " " ++ to_fmt bs
| (terminator.jmp b)     := "jmp " ++ to_fmt b

instance terminator.has_to_format : has_to_format terminator := ⟨terminator.to_format⟩
instance terminator.has_to_string : has_to_string terminator := ⟨pretty ∘ to_fmt⟩

def block.to_format : block → format
| {id := id, phis := ps, instrs := is, term := t} :=
  to_fmt id ++ ":" ++ line ++ join_with ps line ++ join_with is line ++ to_fmt t

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

def decl.to_format : decl → format
| {n := f, as := as, rs := rs, bs := bs} := "decl " ++ to_fmt f ++ " " ++ join_with as " " ++ " : " ++ join_with rs " " ++ " := " ++ line ++ join_with bs line ++ line ++ "end"

instance decl.has_to_format : has_to_format decl := ⟨decl.to_format⟩
instance decl.has_to_string : has_to_string decl := ⟨pretty ∘ to_fmt⟩

end ir
end lean
