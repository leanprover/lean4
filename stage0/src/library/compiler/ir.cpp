/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/array_ref.h"
#include "util/nat.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/trace.h"
#include "library/compiler/util.h"
#include "library/compiler/llnf.h"
#include "library/compiler/extern_attribute.h"
#include "library/compiler/ir.h"

namespace lean {
namespace ir {
object * irrelevant_arg;
extern "C" object * lean_ir_mk_unreachable(object *);
extern "C" object * lean_ir_mk_var_arg(object * id);
extern "C" object * lean_ir_mk_param(object * x, uint8 borrowed, object * ty);
extern "C" object * lean_ir_mk_ctor_expr(object * n, object * cidx, object * size, object * usize, object * ssize, object * ys);
extern "C" object * lean_ir_mk_proj_expr(object * i, object * x);
extern "C" object * lean_ir_mk_uproj_expr(object * i, object * x);
extern "C" object * lean_ir_mk_sproj_expr(object * n, object * o, object * x);
extern "C" object * lean_ir_mk_fapp_expr(object * c, object * ys);
extern "C" object * lean_ir_mk_papp_expr(object * c, object * ys);
extern "C" object * lean_ir_mk_app_expr(object * x, object * ys);
extern "C" object * lean_ir_mk_num_expr(object * v);
extern "C" object * lean_ir_mk_str_expr(object * v);
extern "C" object * lean_ir_mk_vdecl(object * x, object * ty, object * e, object * b);
extern "C" object * lean_ir_mk_jdecl(object * j, object * xs, object * v, object * b);
extern "C" object * lean_ir_mk_uset(object * x, object * i, object * y, object * b);
extern "C" object * lean_ir_mk_sset(object * x, object * i, object * o, object * y, object * ty, object * b);
extern "C" object * lean_ir_mk_case(object * tid, object * x, object * cs);
extern "C" object * lean_ir_mk_ret(object * x);
extern "C" object * lean_ir_mk_jmp(object * j, object * ys);
extern "C" object * lean_ir_mk_alt(object * n, object * cidx, object * size, object * usize, object * ssize, object * b);
extern "C" object * lean_ir_mk_decl(object * f, object * xs, object * ty, object * b);
extern "C" object * lean_ir_mk_extern_decl(object * f, object * xs, object * ty, object * ext_entry);
extern "C" object * lean_ir_mk_dummy_extern_decl(object * f, object * xs, object * ty);
extern "C" object * lean_ir_decl_to_string(object * d);
extern "C" object * lean_ir_compile(object * env, object * opts, object * decls);
extern "C" object * lean_ir_log_to_string(object * log);
extern "C" object * lean_ir_add_decl(object * env, object * decl);

arg mk_var_arg(var_id const & id) { inc(id.raw()); return arg(lean_ir_mk_var_arg(id.raw())); }
arg mk_irrelevant_arg() { return arg(irrelevant_arg); }
object * box_type(type ty) { return box(static_cast<size_t>(ty)); }
param mk_param(var_id const & x, type ty, bool borrowed = false) {
    return param(lean_ir_mk_param(x.to_obj_arg(), borrowed, box_type(ty)));
}
expr mk_ctor(name const & n, unsigned cidx, unsigned size, unsigned usize, unsigned ssize, buffer<arg> const & ys) {
    return expr(lean_ir_mk_ctor_expr(n.to_obj_arg(), mk_nat_obj(cidx), mk_nat_obj(size), mk_nat_obj(usize), mk_nat_obj(ssize), to_array(ys)));
}
expr mk_proj(unsigned i, var_id const & x) { return expr(lean_ir_mk_proj_expr(mk_nat_obj(i), x.to_obj_arg())); }
expr mk_uproj(unsigned i, var_id const & x) { return expr(lean_ir_mk_uproj_expr(mk_nat_obj(i), x.to_obj_arg())); }
expr mk_sproj(unsigned i, unsigned o, var_id const & x) { return expr(lean_ir_mk_sproj_expr(mk_nat_obj(i), mk_nat_obj(o), x.to_obj_arg())); }
expr mk_fapp(fun_id const & c, buffer<arg> const & ys) { return expr(lean_ir_mk_fapp_expr(c.to_obj_arg(), to_array(ys))); }
expr mk_papp(fun_id const & c, buffer<arg> const & ys) { return expr(lean_ir_mk_papp_expr(c.to_obj_arg(), to_array(ys))); }
expr mk_app(var_id const & x, buffer<arg> const & ys) { return expr(lean_ir_mk_app_expr(x.to_obj_arg(), to_array(ys))); }
expr mk_num_lit(nat const & v) { return expr(lean_ir_mk_num_expr(v.to_obj_arg())); }
expr mk_str_lit(string_ref const & v) { return expr(lean_ir_mk_str_expr(v.to_obj_arg())); }

fn_body mk_vdecl(var_id const & x, type ty, expr const & e, fn_body const & b) {
    return fn_body(lean_ir_mk_vdecl(x.to_obj_arg(), box_type(ty), e.to_obj_arg(), b.to_obj_arg()));
}
fn_body mk_jdecl(jp_id const & j, buffer<param> const & xs, expr const & v, fn_body const & b) {
    return fn_body(lean_ir_mk_jdecl(j.to_obj_arg(), to_array(xs), v.to_obj_arg(), b.to_obj_arg()));
}
fn_body mk_uset(var_id const & x, unsigned i, var_id const & y, fn_body const & b) {
    return fn_body(lean_ir_mk_uset(x.to_obj_arg(), mk_nat_obj(i), y.to_obj_arg(), b.to_obj_arg()));
}
fn_body mk_sset(var_id const & x, unsigned i, unsigned o, var_id const & y, type ty, fn_body const & b) {
    return fn_body(lean_ir_mk_sset(x.to_obj_arg(), mk_nat_obj(i), mk_nat_obj(o), y.to_obj_arg(), box_type(ty), b.to_obj_arg()));
}
fn_body mk_ret(arg const & x) { return fn_body(lean_ir_mk_ret(x.to_obj_arg())); }
fn_body mk_unreachable() { return fn_body(lean_ir_mk_unreachable(box(0))); }
alt mk_alt(name const & n, unsigned cidx, unsigned size, unsigned usize, unsigned ssize, fn_body const & b) {
    return alt(lean_ir_mk_alt(n.to_obj_arg(), mk_nat_obj(cidx), mk_nat_obj(size), mk_nat_obj(usize), mk_nat_obj(ssize), b.to_obj_arg()));
}
fn_body mk_case(name const & tid, var_id const & x, buffer<alt> const & alts) {
    return fn_body(lean_ir_mk_case(tid.to_obj_arg(), x.to_obj_arg(), to_array(alts)));
}
fn_body mk_jmp(jp_id const & j, buffer<arg> const & ys) {
    return fn_body(lean_ir_mk_jmp(j.to_obj_arg(), to_array(ys)));
}
decl mk_decl(fun_id const & f, buffer<param> const & xs, type ty, fn_body const & b) {
    return decl(lean_ir_mk_decl(f.to_obj_arg(), to_array(xs), box_type(ty), b.to_obj_arg()));
}
decl mk_extern_decl(fun_id const & f, buffer<param> const & xs, type ty, extern_attr_data_value const & v) {
    return decl(lean_ir_mk_extern_decl(f.to_obj_arg(), to_array(xs), box_type(ty), v.to_obj_arg()));
}
decl mk_dummy_extern_decl(fun_id const & f, buffer<param> const & xs, type ty) {
    return decl(lean_ir_mk_dummy_extern_decl(f.to_obj_arg(), to_array(xs), box_type(ty)));
}
std::string decl_to_string(decl const & d) {
    string_ref r(lean_ir_decl_to_string(d.to_obj_arg()));
    return r.to_std_string();
}
elab_environment add_decl(elab_environment const & env, decl const & d) {
    return elab_environment(lean_ir_add_decl(env.to_obj_arg(), d.to_obj_arg()));
}
}

static ir::type to_ir_type(expr const & e) {
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
        } else if (const_name(e) == get_float_name()) {
            return ir::type::Float;
        } else if (const_name(e) == get_float32_name()) {
            return ir::type::Float32;
        }
     } else if (is_pi(e)) {
        return ir::type::Object;
    }
    throw exception("IR unsupported type");
}

class to_ir_fn {
    elab_environment    m_env;
    type_checker::state m_st;
    local_ctx           m_lctx;
    name                m_x{"x"};
    unsigned            m_next_idx{1};

    elab_environment const & env() const { return m_env; }

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
        ir::var_id x      = to_var_id(args[0]);
        buffer<ir::alt> alts;
        for (unsigned i = 1; i < args.size(); i++) {
            cnstr_info cinfo = get_cnstr_info(m_st, cnames[i-1]);
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
        } else if (is_fvar(e) || is_enf_neutral(e)) {
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
        return ir::mk_jdecl(to_jp_id(decl), xs, v, b);
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
        ir::expr v = ir::mk_papp(const_name(args[0]), ir_args);
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

    ir::fn_body visit_fset(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        expr const & fn = get_app_args(val, args);
        lean_assert(args.size() == 2);
        unsigned n, offset;
        lean_verify(is_llnf_fset(fn, n, offset));
        return ir::mk_sset(to_var_id(args[0]), n, offset, to_var_id(args[1]), ir::type::Float, b);
    }

    ir::fn_body visit_f32set(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        buffer<expr> args;
        expr const & fn = get_app_args(val, args);
        lean_assert(args.size() == 2);
        unsigned n, offset;
        lean_verify(is_llnf_f32set(fn, n, offset));
        return ir::mk_sset(to_var_id(args[0]), n, offset, to_var_id(args[1]), ir::type::Float32, b);
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

    ir::fn_body visit_fproj(local_decl const & decl, ir::fn_body const & b) {
        expr val = *decl.get_value();
        unsigned n, offset;
        lean_verify(is_llnf_fproj(get_app_fn(val), n, offset));
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
        } else if (optional<nat> const & n = get_num_lit_ext(val)) {
            ir::type type = to_ir_type(decl.get_type());
            ir::expr val  = ir::mk_num_lit(*n);
            return ir::mk_vdecl(to_var_id(decl), type, val, b);
        } else if (is_lambda(val)) {
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
            else if (is_llnf_fset(fn))
                return visit_fset(decl, b);
            else if (is_llnf_f32set(fn))
                return visit_f32set(decl, b);
            else if (is_llnf_uset(fn))
                return visit_uset(decl, b);
            else if (is_llnf_proj(fn))
                return visit_proj(decl, b);
            else if (is_llnf_sproj(fn))
                return visit_sproj(decl, b);
            else if (is_llnf_fproj(fn))
                return visit_fproj(decl, b);
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
            if (is_fvar(val) || is_enf_neutral(val)) {
                /* Eliminate `x := y` and `x := _neutral` declarations */
                subst.push_back(val);
            } else {
                name n          = next_name();
                expr new_fvar   = m_lctx.mk_local_decl(ngen(), n, type, val);
                fvars.push_back(new_fvar);
                expr const & op = get_app_fn(val);
                if (is_llnf_sset(op) || is_llnf_fset(op) || is_llnf_f32set(op) || is_llnf_uset(op)) {
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
    to_ir_fn(elab_environment const & env):m_env(env), m_st(env) {}

    ir::decl operator()(comp_decl const & d) { return to_ir_decl(d); }

    /* Convert extern constant into a IR.Decl */
    ir::decl operator()(name const & fn) {
        buffer<bool> borrow; bool dummy;
        get_extern_borrowed_info(env(), fn, borrow, dummy);
        buffer<ir::param> xs;
        unsigned arity = *get_extern_constant_arity(env(), fn);
        expr type      = get_constant_ll_type(env(), fn);
        for (unsigned i = 0; i < arity; i++) {
            lean_assert(is_pi(type));
            xs.push_back(ir::mk_param(ir::var_id(i), to_ir_type(binding_domain(type)), borrow[i]));
            type = binding_body(type);
        }
        ir::type result_type = to_ir_type(type);
        if (optional<extern_attr_data_value> attr = get_extern_attr_data(env(), fn)) {
            return ir::mk_extern_decl(fn, xs, result_type, *attr);
        } else {
            // Hack: `fn` is marked with `implemented_by` or `init`
            return ir::mk_dummy_extern_decl(fn, xs, result_type);
        }
    }
};

namespace ir {
decl to_ir_decl(elab_environment const & env, comp_decl const & d) {
    return to_ir_fn(env)(d);
}

/*
@[export lean.ir.compile_core]
def compile (env : Environment) (opts : Options) (decls : Array Decl) : Log × (Except String Environment) :=
*/
elab_environment compile(elab_environment const & env, options const & opts, comp_decls const & decls) {
    buffer<decl> ir_decls;
    for (comp_decl const & decl : decls) {
        lean_trace(name({"compiler", "lambda_pure"}),
                   tout() << ">> " << decl.fst() << " := " << trace_pp_expr(decl.snd()) << "\n";);
        ir_decls.push_back(to_ir_decl(env, decl));
    }
    object * r   = lean_ir_compile(env.to_obj_arg(), opts.to_obj_arg(), to_array(ir_decls));
    object * log = cnstr_get(r, 0);
    if (array_size(log) > 0) {
        inc(log);
        object * str = lean_ir_log_to_string(log);
        tout() << string_cstr(str);
        dec_ref(str);
    }
    object * v  = cnstr_get(r, 1);
    if (cnstr_tag(v) == 0) {
        string_ref error(cnstr_get(v, 0), true);
        dec_ref(r);
        throw exception(error.data());
    } else {
        elab_environment new_env(cnstr_get(v, 0), true);
        dec_ref(r);
        return new_env;
    }
}

/*
@[export lean_ir_add_boxed_version]
def addBoxedVersion (env : Environment) (decl : Decl) : Except String Environment :=
*/
extern "C" object * lean_ir_add_boxed_version(object * env, object * decl);
elab_environment add_boxed_version(elab_environment const & env, decl const & d) {
    object * v = lean_ir_add_boxed_version(env.to_obj_arg(), d.to_obj_arg());
    if (cnstr_tag(v) == 0) {
        string_ref error(cnstr_get(v, 0), true);
        dec_ref(v);
        throw exception(error.data());
    } else {
        elab_environment new_env(cnstr_get(v, 0), true);
        dec_ref(v);
        return new_env;
    }
}

elab_environment add_extern(elab_environment const & env, name const & fn) {
    decl d = to_ir_fn(env)(fn);
    elab_environment new_env = ir::add_decl(env, d);
    return add_boxed_version(new_env, d);
}

extern "C" LEAN_EXPORT object* lean_add_extern(object * env, object * fn) {
    try {
        elab_environment new_env = add_extern(elab_environment(env), name(fn));
        return mk_except_ok(new_env);
    } catch (exception & ex) {
        // throw; // We use to uncomment this line when debugging weird bugs in the Lean/C++ interface.
        return mk_except_error_string(ex.what());
    }
}

extern "C" object * lean_ir_emit_c(object * env, object * mod_name);

string_ref emit_c(elab_environment const & env, name const & mod_name) {
    object * r = lean_ir_emit_c(env.to_obj_arg(), mod_name.to_obj_arg());
    string_ref s(cnstr_get(r, 0), true);
    if (cnstr_tag(r) == 0) {
        dec_ref(r);
        throw exception(s.to_std_string());
    } else {
        dec_ref(r);
        return s;
    }
}

/*
inductive CtorFieldInfo
| irrelevant
| object (i : Nat)
| usize  (i : Nat)
| scalar (sz : Nat) (offset : Nat) (type : IRType)

structure CtorLayout :=
(cidx       : Nat)
(fieldInfo  : List CtorFieldInfo)
(numObjs    : Nat)
(numUSize   : Nat)
(scalarSize : Nat)
*/
object_ref to_object_ref(cnstr_info const & info) {
    buffer<object_ref> fields;
    for (field_info const & finfo : info.m_field_info) {
        switch (finfo.m_kind) {
        case field_info::Irrelevant:
            fields.push_back(object_ref(box(0)));
            break;
        case field_info::Object:
            fields.push_back(mk_cnstr(1, nat(finfo.m_idx)));
            break;
        case field_info::USize:
            fields.push_back(mk_cnstr(2, nat(finfo.m_idx)));
            break;
        case field_info::Scalar:
            fields.push_back(mk_cnstr(3, nat(finfo.m_size), nat(finfo.m_offset), object_ref(ir::box_type(to_ir_type(finfo.m_type)))));
            break;
        }
    }
    return mk_cnstr(0, nat(info.m_cidx), list_ref<object_ref>(fields), nat(info.m_num_objs), nat(info.m_num_usizes), nat(info.m_scalar_sz));
}

extern "C" LEAN_EXPORT object * lean_ir_get_ctor_layout(object * env0, object * ctor_name0) {
    elab_environment const & env = TO_REF(elab_environment, env0);
    name const & ctor_name  = TO_REF(name, ctor_name0);
    type_checker::state st(env);
    try {
        cnstr_info info = get_cnstr_info(st, ctor_name);
        return mk_except_ok(to_object_ref(info));
    } catch (exception & ex) {
        return mk_except_error_string(ex.what());
    }
}
}

void initialize_ir() {
    ir::irrelevant_arg = box(1);
}

void finalize_ir() {
}
}
