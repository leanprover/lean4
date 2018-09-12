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

def symbol (s : string) : parsec' unit :=
(str s >> whitespace) <?> ("'" ++ s ++ "'")

def keyword (s : string) : parsec' unit :=
(try $ str s >> not_followed_by_sat is_id_rest >> whitespace) <?> ("'" ++ s ++ "'")

def parse_type : parsec' type :=
    (keyword "bool" >> pure type.bool)
<|> (keyword "byte" >> pure type.byte)
<|> (keyword "uint16" >> pure type.uint16)
<|> (keyword "uint32" >> pure type.uint32)
<|> (keyword "uint64" >> pure type.uint64)
<|> (keyword "usize" >> pure type.usize)
<|> (keyword "int16" >> pure type.int16)
<|> (keyword "int32" >> pure type.int32)
<|> (keyword "int64" >> pure type.int64)
<|> (keyword "float" >> pure type.float)
<|> (keyword "double" >> pure type.double)
<|> (keyword "object" >> pure type.object)

def parse_assign_unop : parsec' assign_unop :=
    (keyword "not" >> pure assign_unop.not)
<|> (keyword "neg" >> pure assign_unop.neg)
<|> (keyword "ineg" >> pure assign_unop.ineg)
<|> (keyword "nat2int" >> pure assign_unop.nat2int)
<|> (keyword "is_scalar" >> pure assign_unop.is_scalar)
<|> (keyword "is_shared" >> pure assign_unop.is_shared)
<|> (keyword "is_null" >> pure assign_unop.is_null)
<|> (keyword "array_copy" >> pure assign_unop.array_copy)
<|> (keyword "sarray_copy" >> pure assign_unop.sarray_copy)
<|> (keyword "box" >> pure assign_unop.box)
<|> (keyword "unbox" >> pure assign_unop.unbox)
<|> (keyword "cast" >> pure assign_unop.cast)
<|> (keyword "array_size" >> pure assign_unop.array_size)
<|> (keyword "sarray_size" >> pure assign_unop.sarray_size)
<|> (keyword "string_len" >> pure assign_unop.string_len)
<|> (keyword "succ" >> pure assign_unop.succ)
<|> (keyword "tag" >> pure assign_unop.tag)
<|> (keyword "tag_ref" >> pure assign_unop.tag_ref)

def parse_assign_binop : parsec' assign_binop :=
    (keyword "add" >> pure assign_binop.add)
<|> (keyword "sub" >> pure assign_binop.sub)
<|> (keyword "mul" >> pure assign_binop.mul)
<|> (keyword "div" >> pure assign_binop.div)
<|> (keyword "mod" >> pure assign_binop.mod)
<|> (keyword "iadd" >> pure assign_binop.iadd)
<|> (keyword "isub" >> pure assign_binop.isub)
<|> (keyword "imul" >> pure assign_binop.imul)
<|> (keyword "idiv" >> pure assign_binop.idiv)
<|> (keyword "imod" >> pure assign_binop.imod)
<|> (keyword "shl" >> pure assign_binop.shl)
<|> (keyword "shr" >> pure assign_binop.shr)
<|> (keyword "and" >> pure assign_binop.and)
<|> (keyword "or" >> pure assign_binop.or)
<|> (keyword "xor" >> pure assign_binop.xor)
<|> (keyword "le" >> pure assign_binop.le)
<|> (keyword "lt" >> pure assign_binop.lt)
<|> (keyword "eq" >> pure assign_binop.eq)
<|> (keyword "ne" >> pure assign_binop.ne)
<|> (keyword "ile" >> pure assign_binop.ile)
<|> (keyword "ilt" >> pure assign_binop.ilt)
<|> (keyword "ieq" >> pure assign_binop.ieq)
<|> (keyword "ine" >> pure assign_binop.ine)
<|> (keyword "array_read" >> pure assign_binop.array_read)
<|> (keyword "array_push" >> pure assign_binop.array_push)
<|> (keyword "string_push" >> pure assign_binop.string_push)
<|> (keyword "string_append" >> pure assign_binop.string_append)

def parse_unop : parsec' unop :=
    (keyword "inc_ref" >> pure unop.inc_ref)
<|> (keyword "dec_ref" >> pure unop.dec_ref)
<|> (keyword "inc" >> pure unop.inc)
<|> (keyword "dec" >> pure unop.dec)
<|> (keyword "dec_sref" >> pure unop.dec_sref)
<|> (keyword "free" >> pure unop.free)
<|> (keyword "dealloc" >> pure unop.dealloc)
<|> (keyword "array_pop" >> pure unop.array_pop)
<|> (keyword "sarray_pop" >> pure unop.sarray_pop)

def parse_literal : parsec' literal :=
    (keyword "tt" >> pure (literal.bool tt))
<|> (keyword "ff" >> pure (literal.bool ff))
<|> (do n ← lexeme num <?> "numeral", pure (literal.num n))
<|> (do n ← (ch '-' >> lexeme num), pure (literal.num (- n)))
<|> literal.str <$> parse_string_literal

def parse_uint16 : parsec' uint16 :=
try (do it ← left_over,
        n ← lexeme num,
        when (n ≥ uint16_sz) $ unexpected_at "big numeral, it does not fit in an uint16" it,
        pure $ uint16.of_nat n)
<?> "uint16"

def parse_usize : parsec' usize :=
try (do it ← left_over,
        n ← lexeme num,
        when (n ≥ usize_sz) $ unexpected_at "big numeral, it does not fit in an usize" it,
        pure $ usize.of_nat n)
<?> "usize"

def identifier : parsec' name :=
try (do it ← left_over,
        n ← lean.parser.identifier,
        when (is_reserved_name n) $ unexpected_at "keyword" it,
        pure n)
<?> "identifier"

def parse_var : parsec' var :=
lexeme identifier <?> "variable"

def parse_fnid : parsec' fnid :=
lexeme identifier <?> "function name"

def parse_blockid : parsec' blockid :=
lexeme identifier <?> "label"

def parse_nary_call (x : var) : parsec' instr :=
do xs  ← many1 parse_var,
   symbol ":=",
   keyword "call",
   fid ← parse_fnid,
   ys  ← many parse_var,
   pure $ instr.call ([x] ++ xs) fid ys

def parse_typed_assignment (x : var) : parsec' instr :=
do  symbol ":",
    ty ← parse_type,
    symbol ":=",
    (keyword "sget" >> instr.sget x ty <$> parse_var <*> parse_usize)
<|> (instr.assign x ty <$> parse_var)
<|> (instr.assign_unop x ty <$> parse_assign_unop <*> parse_var)
<|> (instr.assign_binop x ty <$> parse_assign_binop <*> parse_var <*> parse_var)
<|> (instr.assign_lit x ty <$> parse_literal)

def parse_untyped_assignment (x : var) : parsec' instr :=
do  symbol ":=",
    (keyword "closure" >> instr.closure x <$> parse_fnid <*> many parse_var)
<|> (keyword "apply"   >> instr.apply x <$> many1 parse_var)
<|> (keyword "get"     >> instr.get x <$> parse_var <*> parse_uint16)
<|> (keyword "call"    >> instr.call [x] <$> parse_fnid <*> many parse_var)
<|> (keyword "cnstr"   >> instr.cnstr x <$> parse_uint16 <*> parse_uint16 <*> parse_usize)
<|> (keyword "array"   >> instr.array x <$> parse_var <*> parse_var)
<|> (keyword "sarray"  >> instr.sarray x <$> parse_type <*> parse_var <*> parse_var)

def parse_assignment : parsec' instr :=
do x ← parse_var,
   c ← curr,
   if c = ':' then (parse_untyped_assignment x <|> parse_typed_assignment x)
   else parse_nary_call x

def parse_instr : parsec' instr :=
    (keyword "array_write" >> instr.array_write <$> parse_var <*> parse_var <*> parse_var)
<|> (keyword "set" >> instr.set <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (keyword "sset" >> instr.sset <$> parse_var <*> parse_usize <*> parse_var)
<|> (keyword "call" >> instr.call [] <$> parse_fnid <*> many parse_var)
<|> (instr.unop <$> parse_unop <*> parse_var)
<|> parse_assignment

def parse_phi : parsec' phi :=
do (x, ty) ← try $ do { x ← parse_var, symbol ":", ty ← parse_type, symbol ":=", keyword "phi", pure (x, ty) },
   ys ← many1 parse_var,
   pure {x := x, ty := ty, ys := ys}

def parse_terminator : parsec' terminator :=
    (keyword "jmp" >> terminator.jmp <$> parse_blockid)
<|> (keyword "ret" >> terminator.ret <$> many parse_var)
<|> (keyword "case" >> terminator.case <$> parse_var <*> (symbol "[" >> sep_by1 parse_blockid (symbol ",") <* symbol "]"))

def parse_block : parsec' block :=
do id ← try (parse_blockid <* symbol ":"),
   ps ← many (parse_phi <* symbol ";"),
   is ← many (parse_instr <* symbol ";"),
   t  ← parse_terminator <* symbol ";",
   pure { id := id, phis := ps, instrs := is, term := t }

def parse_arg : parsec' arg :=
do symbol "(", x ← parse_var, symbol ":", ty ← parse_type, symbol ")", pure {n := x, ty := ty}

def parse_header (is_const : bool) : parsec' header :=
do n ← parse_fnid,
   as ← if is_const then pure [] else many parse_arg,
   r ← if is_const
       then do symbol ":", t ← parse_type, pure [result.mk t]
       else try (symbol ":" >> many1 (result.mk <$> parse_type)) <|> pure [],
   pure { name := n, args := as, return := r, is_const := is_const }

def parse_def : parsec' decl :=
keyword "def" >> decl.defn <$> parse_header ff <*> (symbol ":=" >> many parse_block)

def parse_defconst : parsec' decl :=
keyword "defconst" >> decl.defn <$> parse_header tt <*> (symbol ":=" >> many parse_block)

def parse_external : parsec' decl :=
keyword "external" >> decl.external <$> parse_header ff

def parse_decl : parsec' decl :=
parse_def <|> parse_defconst <|> parse_external

end ir
end lean
