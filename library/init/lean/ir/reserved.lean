/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbtree.basic init.lean.name

namespace lean
namespace ir

def reserved := [ "bool", "byte", "uint16", "uint32", "uint64", "usize",
 "int16", "int32", "int64", "float", "double", "object", "not", "neg",
 "is_scalar", "is_shared", "is_null", "unbox", "box", "cast",
 "array_copy", "sarray_copy", "array_size", "sarray_size", "string_len",
 "succ", "tag", "tag_ref",
 "add", "sub", "mul", "div", "mod", "shl", "shr", "and",
 "or", "xor", "le", "lt", "eq", "ne", "array_read", "array_push",
 "string_push", "string_append", "inc_ref", "dec_ref", "dec_sref",
 "inc", "dec", "free", "dealloc", "array_pop", "sarray_pop",
 "call", "cnstr", "set", "get", "sset", "sget", "closure", "apply",
 "array", "sarray", "array_write", "phi", "ret", "case", "jmp",
 "def", "external"]

def reserved_set : rbtree string (<) :=
reserved.foldl rbtree.insert (mk_rbtree string (<))

def is_reserved (s : string) : bool :=
reserved_set.contains s

def is_reserved_name : name → bool
| (name.mk_string p s) := is_reserved s
| _                    := ff

end ir
end lean
