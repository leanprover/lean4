/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.ir init.lean.parser.parser
import init.lean.parser.identifier init.lean.parser.string_literal
import init.lean.ir.reserved

namespace lean
namespace ir
open lean.parser

def symbol (s : string) : parser unit :=
(str s >> whitespace) <?> ("'" ++ s ++ "'")

def keyword (s : string) : parser unit :=
(try $ str s >> not_followed_by_sat is_id_rest >> whitespace) <?> ("'" ++ s ++ "'")

def parse_type : parser type :=
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

def parse_unop : parser unop :=
    (keyword "not" >> return unop.not)
<|> (keyword "neg" >> return unop.neg)
<|> (keyword "is_scalar" >> return unop.is_scalar)
<|> (keyword "is_shared" >> return unop.is_shared)
<|> (keyword "array_copy" >> return unop.array_copy)
<|> (keyword "sarray_copy" >> return unop.sarray_copy)
<|> (keyword "box" >> return unop.box)
<|> (keyword "unbox" >> return unop.unbox)
<|> (keyword "cast" >> return unop.cast)

def parse_binop : parser binop :=
    (keyword "add" >> return binop.add)
<|> (keyword "sub" >> return binop.sub)
<|> (keyword "mul" >> return binop.mul)
<|> (keyword "div" >> return binop.div)
<|> (keyword "mod" >> return binop.mod)
<|> (keyword "shl" >> return binop.shl)
<|> (keyword "shr" >> return binop.shr)
<|> (keyword "and" >> return binop.and)
<|> (keyword "or" >> return binop.or)
<|> (keyword "xor" >> return binop.xor)
<|> (keyword "le" >> return binop.le)
<|> (keyword "ge" >> return binop.ge)
<|> (keyword "lt" >> return binop.lt)
<|> (keyword "gt" >> return binop.gt)
<|> (keyword "eq" >> return binop.eq)
<|> (keyword "ne" >> return binop.ne)
<|> (keyword "array_read" >> return binop.array_read)

def parse_unins : parser unins :=
    (keyword "inc" >> return unins.inc)
<|> (keyword "dec" >> return unins.dec)
<|> (keyword "decs" >> return unins.decs)
<|> (keyword "free" >> return unins.free)
<|> (keyword "dealloc" >> return unins.dealloc)
<|> (keyword "array_pop" >> return unins.array_pop)
<|> (keyword "sarray_pop" >> return unins.sarray_pop)

def parse_literal : parser literal :=
    (keyword "tt" >> return (literal.bool tt))
<|> (keyword "ff" >> return (literal.bool ff))
<|> (do n ← lexeme num <?> "numeral", return (literal.num n))
<|> (do n ← (ch '-' >> lexeme num), return (literal.num (- n)))
<|> literal.str <$> parse_string_literal

def parse_uint16 : parser uint16 :=
try (do p ← pos,
        n ← lexeme num,
        when (n ≥ uint16_sz) $ unexpected_at "big numeral, it does not fit in an uint16" p,
        return $ uint16.of_nat n)
<?> "uint16"

def identifier : parser name :=
try (do p ← pos,
        n ← lean.parser.identifier,
        when (is_reserved_name n) $ unexpected_at "keyword" p,
        return n)
<?> "identifier"

def parse_var : parser var :=
lexeme identifier <?> "variable"

def parse_fnid : parser fnid :=
lexeme identifier <?> "function name"

def parse_blockid : parser blockid :=
lexeme identifier <?> "label"

def parse_nary_call (x : var) : parser instr :=
do xs  ← many1 parse_var,
   symbol ":=",
   keyword "call",
   fid ← parse_fnid,
   ys  ← many parse_var,
   return $ instr.call ([x] ++ xs) fid ys

def parse_sizet_entry : parser (nat × type) :=
(prod.mk 1 <$> parse_type)
<|>
(prod.mk <$> (lexeme num <?> "numeral") <*> (symbol ":" >> parse_type))

def parse_sizet : parser sizet :=
symbol "[" >> sep_by parse_sizet_entry (symbol ",") <* symbol "]"

def parse_typed_assignment (x : var) : parser instr :=
do  symbol ":",
    ty ← parse_type,
    symbol ":=",
    (keyword "sget" >> instr.sget x ty <$> parse_var <*> parse_sizet)
<|> (instr.unop x ty <$> parse_unop <*> parse_var)
<|> (instr.binop x ty <$> parse_binop <*> parse_var <*> parse_var)
<|> (instr.lit x ty <$> parse_literal)

def parse_untyped_assignment (x : var) : parser instr :=
do  symbol ":=",
    (keyword "closure" >> instr.closure x <$> parse_fnid <*> many parse_var)
<|> (keyword "apply"   >> instr.apply x <$> many1 parse_var)
<|> (keyword "get"     >> instr.get x <$> parse_var <*> parse_uint16)
<|> (keyword "call"    >> instr.call [x] <$> parse_fnid <*> many parse_var)
<|> (keyword "cnstr"   >> instr.cnstr x <$> parse_uint16 <*> parse_uint16 <*> parse_sizet)
<|> (keyword "array"   >> instr.array x <$> parse_var <*> parse_var)
<|> (keyword "sarray"  >> instr.sarray x <$> parse_type <*> parse_var <*> parse_var)

def parse_assignment : parser instr :=
do x ← parse_var,
   c ← curr,
   if c = ':' then (parse_untyped_assignment x <|> parse_typed_assignment x)
   else parse_nary_call x

def parse_instr : parser instr :=
    (keyword "array_write" >> instr.array_write <$> parse_var <*> parse_var <*> parse_var)
<|> (keyword "array_push" >> instr.array_push <$> parse_var <*> parse_var)
<|> (keyword "set" >> instr.set <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (keyword "sset" >> instr.sset <$> parse_var <*> parse_sizet <*> parse_var)
<|> (instr.unary <$> parse_unins <*> parse_var)
<|> parse_assignment

def parse_phi : parser phi :=
do (x, ty) ← try $ do { x ← parse_var, symbol ":", ty ← parse_type, symbol ":=", keyword "phi", return (x, ty) },
   ys ← many1 parse_var,
   return {x := x, ty := ty, ys := ys}

def parse_terminator : parser terminator :=
    (keyword "jmp" >> terminator.jmp <$> parse_blockid)
<|> (keyword "ret" >> terminator.ret <$> many parse_var)
<|> (keyword "case" >> terminator.case <$> parse_var <*> (symbol "[" >> sep_by1 parse_blockid (symbol ",") <* symbol "]"))

def parse_block : parser block :=
do id ← parse_blockid,
   symbol ":",
   ps ← many (parse_phi <* symbol ";"),
   is ← many (parse_instr <* symbol ";"),
   t  ← parse_terminator <* symbol ";",
   return { id := id, phis := ps, instrs := is, term := t }

def parse_arg : parser arg :=
do symbol "(", x ← parse_var, symbol ":", ty ← parse_type, symbol ")", return {n := x, ty := ty}

def parse_header : parser header :=
do n ← parse_fnid,
   as ← many parse_arg,
   symbol ":",
   r ← many (result.mk <$> parse_type),
   return { n := n, args := as, return := r }

def parse_def : parser decl :=
symbol "def" >> decl.defn <$> parse_header <*> (symbol ":=" >> many parse_block)

def parse_external : parser decl :=
symbol "external" >> decl.external <$> parse_header

end ir
end lean
