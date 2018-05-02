/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.rbtree.basic init.lean.name

namespace lean
namespace ir

def reserved := [ "bool", "byte", "uint16", "uint32", "uint64",
 "int16", "int32", "int64", "float", "double", "object", "not", "neg",
 "scalar", "shared", "unbox", "box", "copy_array", "copy_sarray",
 "add", "sub", "mul", "div", "mod", "shl", "shr", "ashr", "and",
 "or", "xor", "le", "ge", "lt", "gt", "eq", "ne", "call", "closure",
 "apply", "cnstr", "set", "get", "sset", "sget", "array", "read",
 "write", "sarray", "sread", "swrite", "inc", "decs", "dec", "del",
 "phi", "ret", "case", "jmp", "decl", "end", "tt", "ff"]

def reserved_set : rbtree string (<) :=
reserved.foldl rbtree.insert (mk_rbtree string (<))

def is_reserved (s : string) : bool :=
reserved_set.contains s

end ir
end lean
