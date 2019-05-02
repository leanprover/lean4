/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/array_ref.h"
#include "util/nat.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/compiler/util.h"
#include "library/compiler/llnf.h"

namespace lean {
namespace ir {

object * mk_var_arg_core(object * id);
extern object * mk_irrelevant_arg_core;
object * mk_param_core (object * x, uint8 borrowed, uint8 ty);
object * mk_ctor_expr_core(object * n, object * cidx, object * size, object * usize, object * ssize, object * ys);
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
extern object * mk_unreachable_core;
object * mk_alt_core(object * n, object * cidx, object * size, object * usize, object * ssize, object * b);
object * mk_decl_core(object * f, object * xs, uint8 ty, object * b);
object * decl_to_string_core(object * d);
object * decl_max_var_core(object * d);
object * decl_push_proj_core(object * d);
/*
inductive IRType
| float | uint8 | uint16 | uint32 | uint64 | usize
| irrelevant | object | tobject
*/
enum class type { Float, UInt8, UInt16, UInt32, UInt64, USize, Irrelevant, Object, TObject };

typedef nat        var_id;
typedef nat        jp_id;
typedef name       fun_id;
typedef object_ref arg;
typedef object_ref expr;
typedef object_ref param;
typedef object_ref fn_body;
typedef object_ref alt;
typedef object_ref decl;

arg mk_var_arg(var_id const & id) { inc(id.raw()); return arg(mk_var_arg_core(id.raw())); }
arg mk_irrelevant_arg() { return arg(mk_irrelevant_arg_core); }
param mk_param(var_id const & x, type ty) {
    inc(x.raw());
    uint8 borrowed = false;
    return param(mk_param_core(x.raw(), borrowed, static_cast<uint8>(ty)));
}
expr mk_ctor(name const & n, unsigned cidx, unsigned size, unsigned usize, unsigned ssize, buffer<arg> const & ys) {
    inc(n.raw());
    return expr(mk_ctor_expr_core(n.raw(), mk_nat_obj(cidx), mk_nat_obj(size), mk_nat_obj(usize), mk_nat_obj(ssize), to_array(ys)));
}
expr mk_proj(unsigned i, var_id const & x) { inc(x.raw()); return expr(mk_proj_expr_core(mk_nat_obj(i), x.raw())); }
expr mk_uproj(unsigned i, var_id const & x) { inc(x.raw()); return expr(mk_uproj_expr_core(mk_nat_obj(i), x.raw())); }
expr mk_sproj(unsigned i, unsigned o, var_id const & x) { inc(x.raw()); return expr(mk_sproj_expr_core(mk_nat_obj(i), mk_nat_obj(o), x.raw())); }
expr mk_fapp(fun_id const & c, buffer<arg> const & ys) { inc(c.raw()); return expr(mk_fapp_expr_core(c.raw(), to_array(ys))); }
expr mk_papp(fun_id const & c, buffer<arg> const & ys) { inc(c.raw()); return expr(mk_papp_expr_core(c.raw(), to_array(ys))); }
expr mk_app(var_id const & x, buffer<arg> const & ys) { inc(x.raw()); return expr(mk_app_expr_core(x.raw(), to_array(ys))); }
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
alt mk_alt(name const & n, unsigned cidx, unsigned size, unsigned usize, unsigned ssize, fn_body const & b) {
    inc(n.raw()); inc(b.raw());
    return alt(mk_alt_core(n.raw(), mk_nat_obj(cidx), mk_nat_obj(size), mk_nat_obj(usize), mk_nat_obj(ssize), b.raw()));
}
fn_body mk_case(name const & tid, var_id const & x, buffer<alt> const & alts) {
    inc(tid.raw()); inc(x.raw());
    return fn_body(mk_case_core(tid.raw(), x.raw(), to_array(alts)));
}
fn_body mk_jmp(jp_id const & j, buffer<arg> const & ys) {
    inc(j.raw());
    return fn_body(mk_jmp_core(j.raw(), to_array(ys)));
}
decl mk_decl(fun_id const & f, buffer<param> const & xs, type ty, fn_body const & b) {
    inc(f.raw()); inc(b.raw());
    return decl(mk_decl_core(f.raw(), to_array(xs), static_cast<uint8>(ty), b.raw()));
}
std::string decl_to_string(decl const & d) {
    inc(d.raw());
    string_ref r(decl_to_string_core(d.raw()));
    return r.to_std_string();
}
nat decl_max_var(decl const & d) {
    inc(d.raw());
    return nat(decl_max_var_core(d.raw()));
}
decl decl_push_proj(decl const & d) {
    inc(d.raw());
    return decl(decl_push_proj_core(d.raw()));
}
}

class to_ir_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    name                m_x{"x"};
    unsigned            m_next_idx{1};

    environment const & env() const { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    static bool is_jmp(expr const & e) {
        return is_llnf_jmp(get_app_fn(e));
    }

    name next_name() {
        name r(m_x, m_next_idx);
        m_next_idx++;
        return r;
    }

    ir::var_id to_var_id(local_decl const & d) {
        name n = d.get_user_name();
        lean_assert(n.is_numeral());
        return n.get_numeral();
    }

    ir::jp_id to_jp_id(local_decl const & d) {
        return to_var_id(d);
    }

    ir::var_id to_var_id(expr const & e) {
        lean_assert(is_fvar(e));
        return to_var_id(m_lctx.get_local_decl(e));
    }

    ir::jp_id to_jp_id(expr const & e) {
        return to_var_id(e);
    }

    ir::arg to_ir_arg(expr const & e) {
        lean_assert(is_fvar(e) || is_enf_neutral(e));
        if (is_fvar(e))
            return ir::mk_var_arg(to_var_id(e));
        else
            return ir::mk_irrelevant_arg();
    }

    ir::type to_ir_type(expr const & e) {
        if (is_constant(e)) {
            if (e == mk_enf_object_type()) {
                return ir::type::Object;
            } else if (e == mk_enf_neutral_type()) {
                return ir::type::Irrelevant;
            } else if (const_name(e) == get_uint8_name()) {
                return ir::type::UInt8;
            } else if (const_name(e) == get_uint16_name()) {
                return ir::type::UInt16;
            } else if (const_name(e) == get_uint32_name()) {
                return ir::type::UInt32;
            } else if (const_name(e) == get_uint64_name()) {
                return ir::type::UInt64;
            } else if (const_name(e) == get_usize_name()) {
                return ir::type::USize;
            }
        } else if (is_pi(e)) {
            return ir::type::Object;
        }
        throw exception("IR unsupported type");
    }

    ir::type to_ir_result_type(expr e, unsigned arity) {
        for (unsigned i = 0; i < arity; i++) {
            if (!is_pi(e))
                return ir::type::Object;
            e = binding_body(e);
        }
        return to_ir_type(e);
    }

    ir::type size_to_ir_type(unsigned sz) {
        switch (sz) {
        case 1: return ir::type::UInt8;
        case 2: return ir::type::UInt16;
        case 4: return ir::type::UInt32;
        case 8: return ir::type::UInt64;
        default: throw exception("unsupported type size");
        }
    }

    ir::fn_body visit_lambda(expr e, buffer<ir::param> & new_xs) {
        buffer<expr> fvars;
        while (is_lambda(e)) {
            lean_assert(!has_loose_bvars(binding_domain(e)));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), next_name(), binding_domain(e));
            new_xs.push_back(ir::mk_param(to_var_id(new_fvar), to_ir_type(binding_domain(e))));
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        return to_ir_fn_body(instantiate_rev(e, fvars.size(), fvars.data()));
    }

    void to_ir_args(unsigned sz, expr const * args, buffer<ir::arg> & result) {
        for (unsigned i = 0; i < sz; i++) {
            result.push_back(to_ir_arg(args[i]));
        }
    }

    ir::fn_body visit_cases(expr const & e) {
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        lean_assert(is_constant(c));
        name const & I_name = const_name(c).get_prefix();
        buffer<name> cnames;
        get_constructor_names(env(), I_name, cnames);
        lean_assert(args.size() == cnames.size() + 1);
        ir::var_id x = to_var_id(args[0]);
        buffer<ir::alt> alts;
        for (unsigned i = 1; i < args.size(); i++) {
            cnstr_info cinfo = get_cnstr_info(m_st, true, cnames[i-1]);
            ir::fn_body body = to_ir_fn_body(args[i]);
            alts.push_back(ir::mk_alt(cnames[i-1], cinfo.m_cidx, cinfo.m_num_objs, cinfo.m_num_usizes, cinfo.m_scalar_sz, body));
        }
        return ir::mk_case(I_name, x, alts);
    }

    ir::fn_body visit_jmp(expr const & e) {
        buffer<expr> args;
        get_app_args(e, args);
        expr const & jp = args[0];
        lean_assert(is_fvar(jp));
        buffer<ir::arg> ir_args;
        to_ir_args(args.size()-1, args.data()+1, ir_args);
        return ir::mk_jmp(to_jp_id(jp), ir_args);
    }

    ir::fn_body visit_terminal(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases(e);
        } else if (is_jmp(e)) {
            return visit_jmp(e);
        } else if (is_fvar(e)) {
            return ir::mk_ret(to_ir_arg(e));
        } else if (is_enf_unreachable(e)) {
            return ir::mk_unreachable();
        } else {
            lean_unreachable();
        }
    }

    ir::expr visit_lit_val(expr const & val) {
        literal const & l = lit_value(val);
        switch (l.kind()) {
        case literal_kind::Nat:    return ir::mk_num_lit(l.get_nat());
        case literal_kind::String: return ir::mk_str_lit(l.get_string());
        }
        lean_unreachable();
    }

    ir::fn_body mk_vdecl(local_decl const & decl, ir::expr const & val, ir::fn_body const & b) {
        ir::type type = to_ir_type(decl.get_type());
        return ir::mk_vdecl(to_var_id(decl), type, val, b);
    }

    ir::fn_body visit_lit(local_decl const & decl, ir::fn_body const & b) {
        ir::expr val  = visit_lit_val(*decl.get_value());
        return mk_vdecl(decl, val, b);
    }

    ir::fn_body visit_jp(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<ir::param> xs;
        ir::fn_body v = visit_lambda(val, xs);
        ir::type t    = to_ir_result_type(decl.get_type(), xs.size());
        return ir::mk_jdecl(to_jp_id(decl), xs, t, v, b);
    }

    ir::fn_body visit_ctor(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        expr const & fn = get_app_args(val, args);
        name I_name;
        unsigned cidx, num_usizes, num_bytes;
        lean_verify(is_llnf_cnstr(fn, I_name, cidx, num_usizes, num_bytes));
        buffer<name> cnames;
        get_constructor_names(env(), I_name, cnames);
        lean_assert(cidx < cnames.size());
        buffer<ir::arg> ir_args;
        to_ir_args(args.size(), args.data(), ir_args);
        ir::expr v = ir::mk_ctor(cnames[cidx], cidx, args.size(), num_usizes, num_bytes, ir_args);
        return mk_vdecl(decl, v, b);
    }

    ir::fn_body visit_fapp(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        expr const & fn = get_app_args(val, args);
        lean_assert(is_constant(fn));
        buffer<ir::arg> ir_args;
        to_ir_args(args.size(), args.data(), ir_args);
        ir::expr v = ir::mk_fapp(const_name(fn), ir_args);
        return mk_vdecl(decl, v, b);
    }

    ir::fn_body visit_papp(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        get_app_args(val, args);
        lean_assert(is_constant(args[0]));
        buffer<ir::arg> ir_args;
        to_ir_args(args.size()-1, args.data()+1, ir_args);
        ir::expr v = ir::mk_fapp(const_name(args[0]), ir_args);
        return mk_vdecl(decl, v, b);
    }

    ir::fn_body visit_app(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        get_app_args(val, args);
        buffer<ir::arg> ir_args;
        to_ir_args(args.size()-1, args.data()+1, ir_args);
        ir::expr v = ir::mk_app(to_var_id(args[0]), ir_args);
        return mk_vdecl(decl, v, b);
    }

    ir::fn_body visit_sset(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        expr const & fn = get_app_args(val, args);
        lean_assert(args.size() == 2);
        unsigned sz, n, offset;
        lean_verify(is_llnf_sset(fn, sz, n, offset));
        return ir::mk_sset(to_var_id(args[0]), n, offset, to_var_id(args[1]), size_to_ir_type(sz), b);
    }

    ir::fn_body visit_uset(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        expr const & fn = get_app_args(val, args);
        lean_assert(args.size() == 2);
        unsigned n;
        lean_verify(is_llnf_uset(fn, n));
        return ir::mk_uset(to_var_id(args[0]), n, to_var_id(args[1]), b);
    }

    ir::fn_body visit_proj(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        unsigned i;
        lean_verify(is_llnf_proj(get_app_fn(val), i));
        ir::expr v = ir::mk_proj(i, to_var_id(app_arg(val)));
        return mk_vdecl(decl, v, b);
    }

    ir::fn_body visit_sproj(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        unsigned sz, n, offset;
        lean_verify(is_llnf_sproj(get_app_fn(val), sz, n, offset));
        ir::expr v = ir::mk_sproj(n, offset, to_var_id(app_arg(val)));
        return mk_vdecl(decl, v, b);
    }

    ir::fn_body visit_uproj(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        unsigned n;
        lean_verify(is_llnf_uproj(get_app_fn(val), n));
        ir::expr v = ir::mk_uproj(n, to_var_id(app_arg(val)));
        return mk_vdecl(decl, v, b);
    }

    ir::fn_body visit_decl(local_decl const & decl, ir::fn_body const & b) {
        expr val          = *decl.get_value();
        lean_assert(!is_fvar(val));
        if (is_lit(val)) {
            return visit_lit(decl, b);
        } if (is_lambda(val)) {
            return visit_jp(decl, b);
        } else {
            expr const & fn = get_app_fn(val);
            if (is_llnf_cnstr(fn))
                return visit_ctor(decl, b);
            else if (is_enf_unreachable(fn))
                return ir::mk_unreachable();
            else if (is_llnf_apply(fn))
                return visit_app(decl, b);
            else if (is_llnf_closure(fn))
                return visit_papp(decl, b);
            else if (is_llnf_sset(fn))
                return visit_sset(decl, b);
            else if (is_llnf_uset(fn))
                return visit_uset(decl, b);
            else if (is_llnf_proj(fn))
                return visit_proj(decl, b);
            else if (is_llnf_sproj(fn))
                return visit_sproj(decl, b);
            else if (is_llnf_uproj(fn))
                return visit_uproj(decl, b);
            else if (is_constant(fn))
                return visit_fapp(decl, b);
            else
                lean_unreachable();
        }
    }

    ir::fn_body to_ir_fn_body(expr e) {
        buffer<expr> fvars;
        buffer<expr> subst;
        while (is_let(e)) {
            expr type       = let_type(e);
            lean_assert(!has_loose_bvars(type));
            expr val        = instantiate_rev(let_value(e), subst.size(), subst.data());
            if (is_fvar(val)) {
                /* Eliminate `x := y` declarations */
                subst.push_back(val);
            } else {
                name n          = next_name();
                expr new_fvar   = m_lctx.mk_local_decl(ngen(), n, type, val);
                fvars.push_back(new_fvar);
                expr const & op = get_app_fn(val);
                if (is_llnf_sset(op) || is_llnf_uset(op)) {
                    /* In the Lean IR, sset and uset are instructions that perform destructive updates. */
                    subst.push_back(app_arg(app_fn(val)));
                } else {
                    subst.push_back(new_fvar);
                }
            }
            e = let_body(e);
        }
        e = instantiate_rev(e, subst.size(), subst.data());
        ir::fn_body r = visit_terminal(e);
        unsigned i = fvars.size();
        while (i > 0) {
            --i;
            expr const & fvar = fvars[i];
            local_decl decl   = m_lctx.get_local_decl(fvar);
            r = visit_decl(decl, r);
        }
        return r;
    }

    ir::decl to_ir_decl(comp_decl const & d) {
        name const & fn = d.fst();
        expr e          = d.snd();
        buffer<ir::param> xs;
        ir::fn_body b   = visit_lambda(e, xs);
        ir::type type   = to_ir_result_type(get_constant_ll_type(env(), fn), xs.size());
        return ir::mk_decl(fn, xs, type, b);
    }
public:
    to_ir_fn(environment const & env):m_st(env) {}

    ir::decl operator()(comp_decl const & d) { return to_ir_decl(d); }
};

ir::decl to_ir_decl(environment const & env, comp_decl const & d) {
    return to_ir_fn(env)(d);
}
}
