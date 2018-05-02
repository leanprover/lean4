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
lexeme (str s >> eps) <?> s

def parse_type : parser type :=
    (symbol "bool" >> return type.bool)
<|> (symbol "byte" >> return type.byte)
<|> (symbol "uint16" >> return type.uint16)
<|> (symbol "uint32" >> return type.uint32)
<|> (symbol "uint64" >> return type.uint64)
<|> (symbol "int16" >> return type.int16)
<|> (symbol "int32" >> return type.int32)
<|> (symbol "int64" >> return type.int64)
<|> (symbol "float" >> return type.float)
<|> (symbol "double" >> return type.double)
<|> (symbol "object" >> return type.object)

def parse_unop : parser unop :=
    (symbol "not" >> return unop.not)
<|> (symbol "neg" >> return unop.neg)
<|> (symbol "scalar" >> return unop.scalar)
<|> (symbol "shared" >> return unop.shared)
<|> (symbol "unbox" >> return unop.unbox)
<|> (symbol "box" >> return unop.box)
<|> (symbol "copy_array" >> return unop.copy_array)
<|> (symbol "copy_sarray" >> return unop.copy_sarray)

def parse_binop : parser binop :=
    (symbol "add" >> return binop.add)
<|> (symbol "sub" >> return binop.sub)
<|> (symbol "mul" >> return binop.mul)
<|> (symbol "div" >> return binop.div)
<|> (symbol "mod" >> return binop.mod)
<|> (symbol "shl" >> return binop.shl)
<|> (symbol "shr" >> return binop.shr)
<|> (symbol "ashr" >> return binop.ashr)
<|> (symbol "and" >> return binop.and)
<|> (symbol "or" >> return binop.or)
<|> (symbol "xor" >> return binop.xor)
<|> (symbol "le" >> return binop.le)
<|> (symbol "ge" >> return binop.ge)
<|> (symbol "lt" >> return binop.lt)
<|> (symbol "gt" >> return binop.gt)
<|> (symbol "eq" >> return binop.eq)
<|> (symbol "ne" >> return binop.ne)

def parse_literal : parser literal :=
    (symbol "tt" >> return (literal.bool tt))
<|> (symbol "ff" >> return (literal.bool ff))
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
   symbol "call",
   fid ← parse_fnid,
   ys  ← many parse_var,
   return $ instr.call ([x] ++ xs) fid ys

def parse_typed_assignment (x : var) : parser instr :=
do  symbol ":",
    ty ← parse_type,
    symbol ":=",
    (symbol "sget" >> instr.sget x ty <$> parse_var <*> parse_uint16)
<|> (symbol "sread" >> instr.sread x ty <$> parse_var <*> parse_var)
<|> (instr.unop x ty <$> parse_unop <*> parse_var)
<|> (instr.binop x ty <$> parse_binop <*> parse_var <*> parse_var)
<|> (instr.cast x ty <$> parse_var)
<|> (instr.lit x ty <$> parse_literal)

def parse_untyped_assignment (x : var) : parser instr :=
do  symbol ":=",
    (symbol "closure" >> instr.closure x <$> parse_fnid <*> many parse_var)
<|> (symbol "apply"   >> instr.apply x <$> many1 parse_var)
<|> (symbol "read"    >> instr.read x <$> parse_var <*> parse_var)
<|> (symbol "get"     >> instr.get x <$> parse_var <*> parse_uint16)
<|> (symbol "read"    >> instr.read x <$> parse_var <*> parse_var)
<|> (symbol "call"    >> instr.call [x] <$> parse_fnid <*> many parse_var)
<|> (symbol "cnstr"   >> instr.cnstr x <$> parse_uint16 <*> parse_uint16 <*> parse_uint16)
<|> (symbol "array"   >> instr.array x <$> parse_var <*> parse_var)
<|> (symbol "sarray"  >> instr.sarray x <$> parse_type <*> parse_var <*> parse_var)

def parse_assignment : parser instr :=
do x ← parse_var,
   c ← curr,
   if c = ':' then (parse_untyped_assignment x <|> parse_typed_assignment x)
   else parse_nary_call x

def parse_instr : parser instr :=
    (symbol "write" >> instr.write <$> parse_var <*> parse_var <*> parse_var)
<|> (symbol "swrite" >> instr.swrite <$> parse_var <*> parse_var <*> parse_var)
<|> (symbol "set" >> instr.set <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (symbol "sset" >> instr.sset <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (symbol "inc" >> instr.inc <$> parse_var)
<|> (symbol "decs" >> instr.decs <$> parse_var)
<|> (symbol "dec" >> instr.dec <$> parse_var)
<|> (symbol "free" >> instr.free <$> parse_var)
<|> parse_assignment

end ir
end lean
