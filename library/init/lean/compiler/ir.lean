/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import init.lean.name
prelude

namespace lean
namespace ir

abbreviation varid := name
abbreviation fid := name

inductive type
| float | uint8 | uint16 | uint32 | uint64 | usize
| neutral | object | xobject

inductive arg
| var (id : varid)
| neutral

inductive litval
| num (v : nat)
| str (v : string)

structure ctor_info :=
(id : name) (cidx : nat) (usize : nat) (ssize : nat)

inductive expr
| reset (x : varid)
| reuse (x : varid) (i : ctor_info) (ys : list arg)
| ctor (i : ctor_info) (ys : list arg)
| proj (i : nat) (x : varid)
| uproj (i : nat) (x : varid)
| sproj (n : nat) (x : varid)
| fap (c : fid) (ys : list arg)
| pap (c : fid) (ys : list arg)
| ap  (x : varid) (ys : list arg)
| box (ty : type) (x : varid)
| unbox (x : varid)
| lit (v : litval)
| is_shared (x : varid)
| is_boxed_val (x : varid)

structure param :=
(x : name) (borrowed : bool) (ty : type)

inductive alt (fnbody : Type) : Type
| ctor (info : ctor_info) (b : fnbody) : alt
| default (b : fnbody) : alt

inductive fnbody
| vdecl (x : varid) (ty : type) (e : expr) (b : fnbody)
| jdecl (jp : name) (xs : list param) (e : expr) (b : fnbody)
| set (x : varid) (i : nat) (y : varid) (b : fnbody)
| uset (x : varid) (i : nat) (y : varid) (b : fnbody)
| sset (x : varid) (i : nat) (offset : nat) (ty : type) (y : varid) (b : fnbody)
| release (x : varid) (i : nat) (b : fnbody)
| inc (x : varid) (n : nat) (b : fnbody)
| dec (x : varid) (n : nat) (b : fnbody)
| incref (x : varid) (n : nat) (b : fnbody)
| decref (x : varid) (n : nat) (b : fnbody)
| case (tid : name) (cs : list (alt fnbody))
| ret (x : varid)
| jmp (lbl : name) (ys : list arg)

inductive decl
| fdecl  (f : fid) (xs : list param) (ty : type) (b : fnbody)
| extern (f : fid) (xs : list param) (ty : type)

end ir
end lean
