/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.ir init.lean.parser.parsec
import init.lean.parser.identifier init.lean.parser.string_literal
import init.lean.ir.reserved

namespace lean
namespace ir
open lean.parser
open lean.parser.monad_parsec

def symbol (s : string) : parsec unit :=
(str s >> whitespace) <?> ("'" ++ s ++ "'")

def keyword (s : string) : parsec unit :=
(try $ str s >> not_followed_by_sat is_id_rest >> whitespace) <?> ("'" ++ s ++ "'")

def parse_type : parsec type :=
    (keyword "bool" >> return type.bool)
<|> (keyword "byte" >> return type.byte)
<|> (keyword "uint16" >> return type.uint16)
<|> (keyword "uint32" >> return type.uint32)
<|> (keyword "uint64" >> return type.uint64)
<|> (keyword "usize" >> return type.usize)
<|> (keyword "int16" >> return type.int16)
<|> (keyword "int32" >> return type.int32)
<|> (keyword "int64" >> return type.int64)
<|> (keyword "float" >> return type.float)
<|> (keyword "double" >> return type.double)
<|> (keyword "object" >> return type.object)

def parse_assign_unop : parsec assign_unop :=
    (keyword "not" >> return assign_unop.not)
<|> (keyword "neg" >> return assign_unop.neg)
<|> (keyword "ineg" >> return assign_unop.ineg)
<|> (keyword "nat2int" >> return assign_unop.nat2int)
<|> (keyword "is_scalar" >> return assign_unop.is_scalar)
<|> (keyword "is_shared" >> return assign_unop.is_shared)
<|> (keyword "is_null" >> return assign_unop.is_null)
<|> (keyword "array_copy" >> return assign_unop.array_copy)
<|> (keyword "sarray_copy" >> return assign_unop.sarray_copy)
<|> (keyword "box" >> return assign_unop.box)
<|> (keyword "unbox" >> return assign_unop.unbox)
<|> (keyword "cast" >> return assign_unop.cast)
<|> (keyword "array_size" >> return assign_unop.array_size)
<|> (keyword "sarray_size" >> return assign_unop.sarray_size)
<|> (keyword "string_len" >> return assign_unop.string_len)
<|> (keyword "succ" >> return assign_unop.succ)
<|> (keyword "tag" >> return assign_unop.tag)
<|> (keyword "tag_ref" >> return assign_unop.tag_ref)

def parse_assign_binop : parsec assign_binop :=
    (keyword "add" >> return assign_binop.add)
<|> (keyword "sub" >> return assign_binop.sub)
<|> (keyword "mul" >> return assign_binop.mul)
<|> (keyword "div" >> return assign_binop.div)
<|> (keyword "mod" >> return assign_binop.mod)
<|> (keyword "iadd" >> return assign_binop.iadd)
<|> (keyword "isub" >> return assign_binop.isub)
<|> (keyword "imul" >> return assign_binop.imul)
<|> (keyword "idiv" >> return assign_binop.idiv)
<|> (keyword "imod" >> return assign_binop.imod)
<|> (keyword "shl" >> return assign_binop.shl)
<|> (keyword "shr" >> return assign_binop.shr)
<|> (keyword "and" >> return assign_binop.and)
<|> (keyword "or" >> return assign_binop.or)
<|> (keyword "xor" >> return assign_binop.xor)
<|> (keyword "le" >> return assign_binop.le)
<|> (keyword "lt" >> return assign_binop.lt)
<|> (keyword "eq" >> return assign_binop.eq)
<|> (keyword "ne" >> return assign_binop.ne)
<|> (keyword "ile" >> return assign_binop.ile)
<|> (keyword "ilt" >> return assign_binop.ilt)
<|> (keyword "ieq" >> return assign_binop.ieq)
<|> (keyword "ine" >> return assign_binop.ine)
<|> (keyword "array_read" >> return assign_binop.array_read)
<|> (keyword "array_push" >> return assign_binop.array_push)
<|> (keyword "string_push" >> return assign_binop.string_push)
<|> (keyword "string_append" >> return assign_binop.string_append)

def parse_unop : parsec unop :=
    (keyword "inc_ref" >> return unop.inc_ref)
<|> (keyword "dec_ref" >> return unop.dec_ref)
<|> (keyword "inc" >> return unop.inc)
<|> (keyword "dec" >> return unop.dec)
<|> (keyword "dec_sref" >> return unop.dec_sref)
<|> (keyword "free" >> return unop.free)
<|> (keyword "dealloc" >> return unop.dealloc)
<|> (keyword "array_pop" >> return unop.array_pop)
<|> (keyword "sarray_pop" >> return unop.sarray_pop)

def parse_literal : parsec literal :=
    (keyword "tt" >> return (literal.bool tt))
<|> (keyword "ff" >> return (literal.bool ff))
<|> (do n ← lexeme num <?> "numeral", return (literal.num n))
<|> (do n ← (ch '-' >> lexeme num), return (literal.num (- n)))
<|> literal.str <$> parse_string_literal

def parse_uint16 : parsec uint16 :=
try (do p ← pos,
        n ← lexeme num,
        when (n ≥ uint16_sz) $ unexpected_at "big numeral, it does not fit in an uint16" p,
        return $ uint16.of_nat n)
<?> "uint16"

def parse_usize : parsec usize :=
try (do p ← pos,
        n ← lexeme num,
        when (n ≥ usize_sz) $ unexpected_at "big numeral, it does not fit in an usize" p,
        return $ usize.of_nat n)
<?> "usize"

def identifier : parsec name :=
try (do p ← pos,
        n ← lean.parser.identifier,
        when (is_reserved_name n) $ unexpected_at "keyword" p,
        return n)
<?> "identifier"

def parse_var : parsec var :=
lexeme identifier <?> "variable"

def parse_fnid : parsec fnid :=
lexeme identifier <?> "function name"

def parse_blockid : parsec blockid :=
lexeme identifier <?> "label"

def parse_nary_call (x : var) : parsec instr :=
do xs  ← many1 parse_var,
   symbol ":=",
   keyword "call",
   fid ← parse_fnid,
   ys  ← many parse_var,
   return $ instr.call ([x] ++ xs) fid ys

def parse_typed_assignment (x : var) : parsec instr :=
do  symbol ":",
    ty ← parse_type,
    symbol ":=",
    (keyword "sget" >> instr.sget x ty <$> parse_var <*> parse_usize)
<|> (instr.assign x ty <$> parse_var)
<|> (instr.assign_unop x ty <$> parse_assign_unop <*> parse_var)
<|> (instr.assign_binop x ty <$> parse_assign_binop <*> parse_var <*> parse_var)
<|> (instr.assign_lit x ty <$> parse_literal)

def parse_untyped_assignment (x : var) : parsec instr :=
do  symbol ":=",
    (keyword "closure" >> instr.closure x <$> parse_fnid <*> many parse_var)
<|> (keyword "apply"   >> instr.apply x <$> many1 parse_var)
<|> (keyword "get"     >> instr.get x <$> parse_var <*> parse_uint16)
<|> (keyword "call"    >> instr.call [x] <$> parse_fnid <*> many parse_var)
<|> (keyword "cnstr"   >> instr.cnstr x <$> parse_uint16 <*> parse_uint16 <*> parse_usize)
<|> (keyword "array"   >> instr.array x <$> parse_var <*> parse_var)
<|> (keyword "sarray"  >> instr.sarray x <$> parse_type <*> parse_var <*> parse_var)

def parse_assignment : parsec instr :=
do x ← parse_var,
   c ← curr,
   if c = ':' then (parse_untyped_assignment x <|> parse_typed_assignment x)
   else parse_nary_call x

def parse_instr : parsec instr :=
    (keyword "array_write" >> instr.array_write <$> parse_var <*> parse_var <*> parse_var)
<|> (keyword "set" >> instr.set <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (keyword "sset" >> instr.sset <$> parse_var <*> parse_usize <*> parse_var)
<|> (keyword "call" >> instr.call [] <$> parse_fnid <*> many parse_var)
<|> (instr.unop <$> parse_unop <*> parse_var)
<|> parse_assignment

def parse_phi : parsec phi :=
do (x, ty) ← try $ do { x ← parse_var, symbol ":", ty ← parse_type, symbol ":=", keyword "phi", return (x, ty) },
   ys ← many1 parse_var,
   return {x := x, ty := ty, ys := ys}

def parse_terminator : parsec terminator :=
    (keyword "jmp" >> terminator.jmp <$> parse_blockid)
<|> (keyword "ret" >> terminator.ret <$> many parse_var)
<|> (keyword "case" >> terminator.case <$> parse_var <*> (symbol "[" >> sep_by1 parse_blockid (symbol ",") <* symbol "]"))

def parse_block : parsec block :=
do id ← try (parse_blockid <* symbol ":"),
   ps ← many (parse_phi <* symbol ";"),
   is ← many (parse_instr <* symbol ";"),
   t  ← parse_terminator <* symbol ";",
   return { id := id, phis := ps, instrs := is, term := t }

def parse_arg : parsec arg :=
do symbol "(", x ← parse_var, symbol ":", ty ← parse_type, symbol ")", return {n := x, ty := ty}

def parse_header (is_const : bool) : parsec header :=
do n ← parse_fnid,
   as ← if is_const then return [] else many parse_arg,
   r ← if is_const
       then do symbol ":", t ← parse_type, return [result.mk t]
       else try (symbol ":" >> many1 (result.mk <$> parse_type)) <|> return [],
   return { name := n, args := as, return := r, is_const := is_const }

def parse_def : parsec decl :=
keyword "def" >> decl.defn <$> parse_header ff <*> (symbol ":=" >> many parse_block)

def parse_defconst : parsec decl :=
keyword "defconst" >> decl.defn <$> parse_header tt <*> (symbol ":=" >> many parse_block)

def parse_external : parsec decl :=
keyword "external" >> decl.external <$> parse_header ff

def parse_decl : parsec decl :=
parse_def <|> parse_defconst <|> parse_external

end ir
end lean
