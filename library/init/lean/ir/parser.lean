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
(str s *> whitespace) <?> ("'" ++ s ++ "'")

def keyword (s : string) : parsec' unit :=
(try $ str s *> not_followed_by_sat is_id_rest *> whitespace) <?> ("'" ++ s ++ "'")

def parse_key2val {α : Type} (msg : string) : list (string × α) → parsec' α
| []              := error msg
| ((s, v) :: kvs) := (keyword s *> pure v) <|> parse_key2val kvs

def str2type : list (string × type) :=
[ ("object", type.object), ("bool", type.bool), ("byte", type.byte),
  ("uint16", type.uint16), ("uint32", type.uint32), ("uint64", type.uint64), ("usize", type.usize),
  ("int16", type.int16), ("int32", type.int32), ("int64", type.int64),
  ("float", type.float), ("double", type.double) ]

def parse_type : parsec' type :=
parse_key2val "type" str2type

def str2aunop : list (string × assign_unop) :=
[ ("not", assign_unop.not), ("neg", assign_unop.neg), ("ineg", assign_unop.ineg), ("nat2int", assign_unop.nat2int),
  ("is_scalar", assign_unop.is_scalar), ("is_shared", assign_unop.is_shared), ("is_null", assign_unop.is_null),
  ("array_copy", assign_unop.array_copy), ("sarray_copy", assign_unop.sarray_copy), ("box", assign_unop.box),
  ("unbox", assign_unop.unbox), ("cast", assign_unop.cast), ("array_size", assign_unop.array_size),
  ("sarray_size", assign_unop.sarray_size), ("string_len", assign_unop.string_len), ("succ", assign_unop.succ),
  ("tag", assign_unop.tag), ("tag_ref", assign_unop.tag_ref) ]

def parse_assign_unop : parsec' assign_unop :=
parse_key2val "unary operator" str2aunop

def str2abinop : list (string × assign_binop) :=
[ ("add", assign_binop.add), ("sub", assign_binop.sub), ("mul", assign_binop.mul), ("div", assign_binop.div), ("mod", assign_binop.mod),
  ("iadd", assign_binop.iadd), ("isub", assign_binop.isub), ("imul", assign_binop.imul), ("idiv", assign_binop.idiv), ("imod", assign_binop.imod),
  ("shl", assign_binop.shl), ("shr", assign_binop.shr), ("and", assign_binop.and), ("or", assign_binop.or), ("xor", assign_binop.xor), ("le", assign_binop.le),
  ("lt", assign_binop.lt), ("eq", assign_binop.eq), ("ne", assign_binop.ne), ("ile", assign_binop.ile), ("ilt", assign_binop.ilt), ("ieq", assign_binop.ieq),
  ("ine", assign_binop.ine), ("array_read", assign_binop.array_read), ("array_push", assign_binop.array_push), ("string_push", assign_binop.string_push),
  ("string_append", assign_binop.string_append) ]

def parse_assign_binop : parsec' assign_binop :=
parse_key2val "binary operator" str2abinop

def str2unop : list (string × unop) :=
[ ("inc_ref", unop.inc_ref), ("dec_ref", unop.dec_ref), ("inc", unop.inc), ("dec", unop.dec),
  ("dec_sref", unop.dec_sref), ("free", unop.free), ("dealloc", unop.dealloc), ("array_pop", unop.array_pop),
  ("sarray_pop", unop.sarray_pop) ]

def parse_unop : parsec' unop :=
parse_key2val "unary operator" str2unop

def parse_literal : parsec' literal :=
    (keyword "tt" *> pure (literal.bool tt))
<|> (keyword "ff" *> pure (literal.bool ff))
<|> (do n ← lexeme num <?> "numeral", pure (literal.num n))
<|> (do n ← (ch '-' *> lexeme num), pure (literal.num (- n)))
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

def parse_typed_assignment (x : var) : parsec' instr :=
do  symbol ":",
    ty ← parse_type,
    symbol ":=",
    (keyword "sget" *> instr.sget x ty <$> parse_var <*> parse_usize)
<|> (instr.assign x ty <$> parse_var)
<|> (instr.assign_unop x ty <$> parse_assign_unop <*> parse_var)
<|> (instr.assign_binop x ty <$> parse_assign_binop <*> parse_var <*> parse_var)
<|> (instr.assign_lit x ty <$> parse_literal)

def parse_untyped_assignment (x : var) : parsec' instr :=
do  symbol ":=",
    (keyword "closure" *> instr.closure x <$> parse_fnid <*> many parse_var)
<|> (keyword "apply"   *> instr.apply x <$> many1 parse_var)
<|> (keyword "get"     *> instr.get x <$> parse_var <*> parse_uint16)
<|> (keyword "call"    *> instr.call x <$> parse_fnid <*> many parse_var)
<|> (keyword "cnstr"   *> instr.cnstr x <$> parse_uint16 <*> parse_uint16 <*> parse_usize)
<|> (keyword "array"   *> instr.array x <$> parse_var <*> parse_var)
<|> (keyword "sarray"  *> instr.sarray x <$> parse_type <*> parse_var <*> parse_var)

def parse_assignment : parsec' instr :=
do x ← parse_var,
   (parse_untyped_assignment x <|> parse_typed_assignment x)

def parse_instr : parsec' instr :=
    (keyword "array_write" *> instr.array_write <$> parse_var <*> parse_var <*> parse_var)
<|> (keyword "set" *> instr.set <$> parse_var <*> parse_uint16 <*> parse_var)
<|> (keyword "sset" *> instr.sset <$> parse_var <*> parse_usize <*> parse_var)
<|> (instr.unop <$> parse_unop <*> parse_var)
<|> parse_assignment

def parse_phi : parsec' phi :=
do (x, ty) ← try $ do { x ← parse_var, symbol ":", ty ← parse_type, symbol ":=", keyword "phi", pure (x, ty) },
   ys ← many1 parse_var,
   pure {x := x, ty := ty, ys := ys}

def parse_terminator : parsec' terminator :=
    (keyword "jmp" *> terminator.jmp <$> parse_blockid)
<|> (keyword "ret" *> terminator.ret <$> parse_var)
<|> (keyword "case" *> terminator.case <$> parse_var <*> (symbol "[" *> sep_by1 parse_blockid (symbol ",") <* symbol "]"))

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
   r ← symbol ":" *> result.mk <$> parse_type,
   pure { name := n, args := as, return := r, is_const := is_const }

def parse_def : parsec' decl :=
keyword "def" *> decl.defn <$> parse_header ff <*> (symbol ":=" *> many parse_block)

def parse_defconst : parsec' decl :=
keyword "defconst" *> decl.defn <$> parse_header tt <*> (symbol ":=" *> many parse_block)

def parse_external : parsec' decl :=
keyword "external" *> decl.external <$> parse_header ff

def parse_decl : parsec' decl :=
parse_def <|> parse_defconst <|> parse_external

end ir
end lean
