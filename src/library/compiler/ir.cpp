/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/array_ref.h"
#include "util/nat.h"
#include "library/compiler/util.h"

namespace lean {
namespace ir {

object * mk_var_arg_core(object * id);
object * mk_irrelevant_arg_core;
object * mk_param_core (object * x, uint8 borrowed, uint8 ty);
object * mk_ctor_expr_core(object * n, object * cidx, object * usize, object * ssize, object * ys);
object * mk_proj_expr_core(object * i, object * x);
object * mk_uproj_expr_core(object * i, object * x);
object * mk_sproj_expr_core(object * n, object * o, object * x);
object * mk_fapp_expr_core(object * c, object * ys);
object * mk_papp_expr_core(object * c, object * ys);
object * mk_app_expr_core(object * x, object * ys);
object * mk_num_expr_core(object * v);
object * mk_str_expr_core(object * v);
object * mk_vdecl_core(object * x, uint8 ty, object * e, object * b);
object * mk_jdecl_core(object * j, object * xs, uint8 ty, object * v, object * b);
object * mk_uset_core(object * x, object * i, object * y, object * b);
object * mk_sset_core(object * x, object * i, object * o, object * y, uint8 ty, object * b);
object * mk_case_core(object * tid, object * x, object * cs);
object * mk_ret_core(object * x);
object * mk_jmp_core(object * j, object * ys);
object * mk_unreachable_core;
object * mk_alt_core(object * n, object * cidx, object * usize, object * ssize, object * b);
object * mk_decl_core(object * f, object * xs, uint8 ty, object * b);

/*
inductive IRType
| float | uint8 | uint16 | uint32 | uint64 | usize
| irrelevant | object | tobject
*/
enum class type { Float, UInt8, UInt16, UInt32, UInt64, USize, Irrelevant, Object, TObject };

typedef name       var_id;
typedef name       jp_id;
typedef name       fun_id;
typedef object_ref arg;
typedef object_ref expr;
typedef object_ref param;
typedef object_ref fn_body;
typedef object_ref alt;
typedef object_ref decl;

arg mk_var_arg(var_id const & id) { inc(id.raw()); return arg(mk_var_arg_core(id.raw())); }
arg mk_irrelevant_arg() { return arg(mk_irrelevant_arg_core); }
param mk_param_core (name const & x, type ty) {
    uint8 borrowed = false;
    return param(mk_param_core(x.raw(), borrowed, static_cast<uint8>(ty)));
}
expr mk_ctor(name const & n, unsigned cidx, unsigned usize, unsigned ssize, buffer<arg> const & ys) {
    inc(n.raw());
    return expr(mk_ctor_expr_core(n.raw(), mk_nat_obj(cidx), mk_nat_obj(usize), mk_nat_obj(ssize), to_array(ys)));

}
expr mk_proj(unsigned i, var_id const & x) { inc(x.raw()); return expr(mk_proj_expr_core(mk_nat_obj(i), x.raw())); }
expr mk_uproj(unsigned i, var_id const & x) { inc(x.raw()); return expr(mk_uproj_expr_core(mk_nat_obj(i), x.raw())); }
expr mk_sproj(unsigned i, unsigned o, var_id const & x) { inc(x.raw()); return expr(mk_sproj_expr_core(mk_nat_obj(i), mk_nat_obj(o), x.raw())); }
expr mk_fapp(fun_id const & c, buffer<arg> const & ys) { inc(c.raw()); return expr(mk_fapp_expr_core(c.raw(), to_array(ys))); }
expr mk_papp(fun_id const & c, buffer<arg> const & ys) { inc(c.raw()); return expr(mk_papp_expr_core(c.raw(), to_array(ys))); }
expr mk_app(var_id const & x, buffer<arg> const & ys) { inc(x.raw()); return expr(mk_papp_expr_core(x.raw(), to_array(ys))); }
expr mk_num_lit(nat const & v) { inc(v.raw()); return expr(mk_num_expr_core(v.raw())); }
expr mk_str_lit(string_ref const & v) { inc(v.raw()); return expr(mk_str_expr_core(v.raw())); }

fn_body mk_vdecl(var_id const & x, type ty, expr const & e, fn_body const & b) {
    inc(x.raw()); inc(e.raw()), inc(b.raw());
    return fn_body(mk_vdecl_core(x.raw(), static_cast<uint8>(ty), e.raw(), b.raw()));
}
fn_body mk_jdecl(jp_id const & j, buffer<param> const & xs, type ty, expr const & v, fn_body const & b) {
    inc(j.raw()); inc(v.raw()); inc(b.raw());
    return fn_body(mk_jdecl_core(j.raw(), to_array(xs), static_cast<uint8>(ty), v.raw(), b.raw()));
}
fn_body mk_uset(var_id const & x, unsigned i, var_id const & y, fn_body const & b) {
    inc(x.raw()); inc(y.raw()); inc(b.raw());
    return fn_body(mk_uset_core(x.raw(), mk_nat_obj(i), y.raw(), b.raw()));
}
fn_body mk_sset(var_id const & x, unsigned i, unsigned o, var_id const & y, type ty, fn_body const & b) {
    inc(x.raw()); inc(y.raw()); inc(b.raw());
    return fn_body(mk_sset_core(x.raw(), mk_nat_obj(i), mk_nat_obj(o), y.raw(), static_cast<uint8>(ty), b.raw()));
}
fn_body mk_ret(arg const & x) { inc(x.raw()); return fn_body(mk_ret_core(x.raw())); }
fn_body mk_unreachable() { return fn_body(mk_unreachable_core); }
alt mk_alt(name const & n, unsigned cidx, unsigned usize, unsigned ssize, fn_body const & b) {
    inc(n.raw()); inc(b.raw());
    return alt(mk_alt_core(n.raw(), mk_nat_obj(cidx), mk_nat_obj(usize), mk_nat_obj(ssize), b.raw()));
}
fn_body mk_case(name const & tid, var_id const & x, buffer<alt> const & alts) {
    inc(tid.raw()); inc(x.raw());
    return fn_body(mk_case_core(tid.raw(), x.raw(), to_array(alts)));
}
fn_body mk_jmp(jp_id const & j, buffer<arg> const & ys) {
    inc(j.raw());
    return fn_body(mk_jmp_core(j.raw(), to_array(ys)));
}
decl mk_decl(fun_id const & f, buffer<param> const & x, type ty, fn_body const & b) {
    inc(f.raw()); inc(b.raw());
    return decl(mk_decl_core(f.raw(), to_array(x), static_cast<uint8>(ty), b.raw()));
}
}
}
