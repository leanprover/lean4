/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.ir init.lean.parser.parser
import init.lean.parser.identifier init.lean.parser.string_literal

namespace lean
namespace ir
open lean.parser

def symbol (s : string) : parser unit :=
(str s >> whitespace) <?> s

def keyword (s : string) : parser unit :=
(try $ str s >> not_followed_by_sat is_id_rest >> whitespace) <?> s

def parse_type : parser type :=
    (keyword "bool" >> return type.bool)
<|> (keyword "byte" >> return type.byte)
<|> (keyword "uint16" >> return type.uint16)
<|> (keyword "uint32" >> return type.uint32)
<|> (keyword "uint64" >> return type.uint64)
<|> (keyword "int16" >> return type.int16)
<|> (keyword "int32" >> return type.int32)
<|> (keyword "int64" >> return type.int64)
<|> (keyword "float" >> return type.float)
<|> (keyword "double" >> return type.double)
<|> (keyword "object" >> return type.object)

def parse_unop : parser unop :=
    (keyword "not" >> return unop.not)
<|> (keyword "neg" >> return unop.neg)
<|> (keyword "scalar" >> return unop.scalar)
<|> (keyword "shared" >> return unop.shared)
<|> (keyword "unbox" >> return unop.unbox)
<|> (keyword "box" >> return unop.box)
<|> (keyword "copy_array" >> return unop.copy_array)
<|> (keyword "copy_sarray" >> return unop.copy_sarray)

def parse_binop : parser binop :=
    (keyword "add" >> return binop.add)
<|> (keyword "sub" >> return binop.sub)
<|> (keyword "mul" >> return binop.mul)
<|> (keyword "div" >> return binop.div)
<|> (keyword "mod" >> return binop.mod)
<|> (keyword "shl" >> return binop.shl)
<|> (keyword "shr" >> return binop.shr)
<|> (keyword "ashr" >> return binop.ashr)
<|> (keyword "and" >> return binop.and)
<|> (keyword "or" >> return binop.or)
<|> (keyword "xor" >> return binop.xor)
<|> (keyword "le" >> return binop.le)
<|> (keyword "ge" >> return binop.ge)
<|> (keyword "lt" >> return binop.lt)
<|> (keyword "gt" >> return binop.gt)
<|> (keyword "eq" >> return binop.eq)
<|> (keyword "ne" >> return binop.ne)

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

def parse_var : parser var :=
lexeme identifier <?> "variable"

def parse_fnid : parser fnid :=
lexeme identifier <?> "function name"

def parse_nary_call (x : var) : parser instr :=
do xs  ← many1 parse_var,
   symbol ":=",
   keyword "call",
   fid ← parse_fnid,
   ys  ← many parse_var,
   return $ instr.call ([x] ++ xs) fid ys

def parse_typed_assignment (x : var) : parser instr :=
do  symbol ":",
    ty ← parse_type,
    symbol ":=",
    (keyword "sget" >> instr.sget x ty <$> parse_var <*> parse_uint16)
<|> (keyword "sread" >> instr.sread x ty <$> parse_var <*> parse_var)
<|> (instr.unop x ty <$> parse_unop <*> parse_var)
<|> (instr.binop x ty <$> parse_binop <*> parse_var <*> parse_var)
<|> (instr.cast x ty <$> parse_var)
<|> (instr.lit x ty <$> parse_literal)

def parse_untyped_assignment (x : var) : parser instr :=
do  symbol ":=",
    (keyword "closure" >> instr.closure x <$> parse_fnid <*> many parse_var)
<|> (keyword "apply"   >> instr.apply x <$> many1 parse_var)
<|> (keyword "read"    >> instr.read x <$> parse_var <*> parse_var)
<|> (keyword "get"     >> instr.get x <$> parse_var <*> parse_uint16)
<|> (keyword "read"    >> instr.read x <$> parse_var <*> parse_var)
<|> (keyword "call"    >> instr.call [x] <$> parse_fnid <*> many parse_var)
<|> (keyword "cnstr"   >> instr.cnstr x <$> parse_uint16 <*> parse_uint16 <*> parse_uint16)
<|> (keyword "array"   >> instr.array x <$> parse_var <*> parse_var)
<|> (keyword "sarray"  >> instr.sarray x <$> parse_type <*> parse_var <*> parse_var)

def parse_assignment : parser instr :=
do x ← parse_var,
   c ← curr,
   if c = ':' then (parse_untyped_assignment x <|> parse_typed_assignment x)
   else parse_nary_call x

def parse_instr : parser instr :=
    (keyword "write" >> instr.write <$> parse_var <*> parse_var <*> parse_var)
<|> (keyword "swrite" >> instr.swrite <$> parse_var <*> parse_var <*> parse_var)
<|> (keyword "set" >> instr.set <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (keyword "sset" >> instr.sset <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (keyword "inc" >> instr.inc <$> parse_var)
<|> (keyword "dec" >> instr.dec <$> parse_var)
<|> (keyword "decs" >> instr.decs <$> parse_var)
<|> (keyword "free" >> instr.free <$> parse_var)
<|> parse_assignment

end ir
end lean
