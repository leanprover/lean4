/*
Copyright (c) 2013-14 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/interrupt.h"
#include "util/lbool.h"
#include "util/flet.h"
#include "util/sstream.h"
#include "util/scoped_map.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/metavar.h"
#include "kernel/error_msgs.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"

namespace lean {
static name g_x_name("x");

no_constraints_allowed_exception::no_constraints_allowed_exception():exception("constraints are not allowed in this type checker") {}
exception * no_constraints_allowed_exception::clone() const { return new no_constraints_allowed_exception(); }
void no_constraints_allowed_exception::rethrow() const { throw *this; }

add_cnstr_fn mk_no_contranint_fn() {
    return add_cnstr_fn([](constraint const &) { throw no_constraints_allowed_exception(); });
}

type_checker::scope::scope(type_checker & tc):
    m_tc(tc), m_old_cs_size(m_tc.m_cs.size()), m_old_cache_cs(m_tc.m_cache_cs), m_keep(false) {
    m_tc.m_infer_type_cache[0].push();
    m_tc.m_infer_type_cache[1].push();
    m_tc.m_cache_cs = true;
}
type_checker::scope::~scope() {
    if (m_keep) {
        // keep results
        m_tc.m_infer_type_cache[0].keep();
        m_tc.m_infer_type_cache[1].keep();
    } else {
        // restore caches
        m_tc.m_infer_type_cache[0].pop();
        m_tc.m_infer_type_cache[1].pop();
        m_tc.m_cs.shrink(m_old_cs_size);
    }
    m_tc.m_cache_cs = m_old_cache_cs;
}

void type_checker::scope::keep() {
    m_keep = true;
    if (!m_old_cache_cs) {
        lean_assert(m_old_cs_size == 0);
        // send results to m_add_cnstr_fn
        try {
            for (auto const & c : m_tc.m_cs)
                m_tc.m_add_cnstr_fn(c);
        } catch (...) {
            m_tc.m_cs.clear();
            throw;
        }
        m_tc.m_cs.clear();
    }
}

optional<expr> type_checker::expand_macro(expr const & m) {
    lean_assert(is_macro(m));
    return macro_def(m).expand(m, m_tc_ctx);
}

/**
   \brief Return the body of the given binder, where the free variable #0 is replaced with a fresh local constant.
   It also returns the fresh local constant.
*/
std::pair<expr, expr> type_checker::open_binding_body(expr const & e) {
    expr local     = mk_local(m_gen.next(), binding_name(e), binding_domain(e));
    return mk_pair(instantiate(binding_body(e), local), local);
}

/** \brief Add given constraint using m_add_cnstr_fn. */
void type_checker::add_cnstr(constraint const & c) {
    if (m_cache_cs)
        m_cs.push_back(c);
    else
        m_add_cnstr_fn(c);
}

/**
   \brief Given a metavariable application ((?m t_1) ... t_k)
   Create a telescope with the types of t_1 ... t_k.
   If t_i is a local constant, then we abstract the occurrences of t_i in the types of t_{i+1} ... t_k.
   Return false if the telescope still contains local constants after the abstraction step.
*/
bool type_checker::meta_to_telescope(expr const & e, buffer<expr> & telescope) {
    lean_assert(is_meta(e));
    lean_assert(closed(e));
    buffer<optional<expr>> locals;
    return meta_to_telescope_core(e, telescope, locals);
}

/** \brief Auxiliary method for meta_to_telescope */
bool type_checker::meta_to_telescope_core(expr const & e, buffer<expr> & telescope, buffer<optional<expr>> & locals) {
    lean_assert(is_meta(e));
    if (is_app(e)) {
        if (!meta_to_telescope_core(app_fn(e), telescope, locals))
            return false;
        // infer type and abstract local constants
        unsigned n = locals.size();
        expr t = replace(infer_type(app_arg(e)),
                         [&](expr const & e, unsigned offset) -> optional<expr> {
                             if (is_local(e)) {
                                 for (unsigned i = 0; i < n; i++) {
                                     if (locals[i] && is_eqp(*locals[i], e))
                                         return some_expr(mk_var(offset + n - i - 1));
                                 }
                             }
                             return none_expr();
                         });
        if (has_local(t))
            return false;
        telescope.push_back(t);
        if (is_local(e))
            locals.push_back(some_expr(e));
        else
            locals.push_back(none_expr());
    }
    return true;
}

/**
   \brief Make sure \c e "is" a sort, and return the corresponding sort.
   If \c e is not a sort, then the whnf procedure is invoked. Then, there are
   two options: the normalize \c e is a sort, or it is a meta. If it is a meta,
   a new constraint is created forcing it to be a sort.

   \remark \c s is used to extract position (line number information) when an
   error message is produced
*/
expr type_checker::ensure_sort_core(expr e, expr const & s) {
    if (is_sort(e))
        return e;
    e = whnf(e);
    if (is_sort(e)) {
        return e;
    } else if (is_meta(e)) {
        expr r = mk_sort(mk_meta_univ(m_gen.next()));
        justification j = mk_justification(s,
                                           [=](formatter const & fmt, options const & o, substitution const & subst) {
                                               return pp_type_expected(fmt, m_env, o, subst.instantiate_metavars_wo_jst(s));
                                           });
        add_cnstr(mk_eq_cnstr(e, r, j));
        return r;
    } else {
        // We don't want m_env (i.e., this->m_env) inside the following closure,
        // because the type checker may be gone, when the closure is executed.
        environment env = m_env;
        throw_kernel_exception(env, s,
                               [=](formatter const & fmt, options const & o) { return pp_type_expected(fmt, env, o, s); });
    }
}

/** \brief Similar to \c ensure_sort, but makes sure \c e "is" a Pi. */
expr type_checker::ensure_pi_core(expr e, expr const & s) {
    if (is_pi(e))
        return e;
    e = whnf(e);
    if (is_pi(e)) {
        return e;
    } else if (is_meta(e)) {
        buffer<expr> telescope;
        if (!meta_to_telescope(e, telescope)) {
            environment env = m_env;
            throw_kernel_exception(env, s,
                                   [=](formatter const & fmt, options const & o) { return pp_function_expected(fmt, env, o, s); });
        }
        expr ta    = mk_sort(mk_meta_univ(m_gen.next()));
        expr A     = mk_metavar(m_gen.next(), mk_pi(telescope, ta));
        expr A_xs  = mk_app_vars(A, telescope.size());
        telescope.push_back(A_xs);
        expr tb    = mk_sort(mk_meta_univ(m_gen.next()));
        expr B     = mk_metavar(m_gen.next(), mk_pi(telescope, tb));
        buffer<expr> args;
        get_app_args(e, args);
        expr A_args = mk_app(A, args.size(), args.data());
        args.push_back(Var(0));
        expr B_args = mk_app(B, args.size(), args.data());
        expr r      = mk_pi(g_x_name, A_args, B_args);
        justification j = mk_justification(s,
                                           [=](formatter const & fmt, options const & o, substitution const & subst) {
                                               return pp_function_expected(fmt, m_env, o, subst.instantiate_metavars_wo_jst(s));
                                           });
        add_cnstr(mk_eq_cnstr(e, r, j));
        return r;
    } else {
        environment env = m_env;
        throw_kernel_exception(env, s,
                               [=](formatter const & fmt, options const & o) { return pp_function_expected(fmt, env, o, s); });
    }
}

static constexpr char const * g_macro_error_msg = "failed to type check macro expansion";

justification type_checker::mk_macro_jst(expr const & e) {
    return mk_justification(e,
                            [=](formatter const &, options const &, substitution const &) {
                                return format(g_macro_error_msg);
                            });
}

void type_checker::check_level(level const & l, expr const & s) {
    if (auto n1 = get_undef_global(l, m_env))
        throw_kernel_exception(m_env, sstream() << "invalid reference to undefined global universe level '" << *n1 << "'", s);
    if (auto n2 = get_undef_param(l, m_params))
        throw_kernel_exception(m_env, sstream() << "invalid reference to undefined universe level parameter '" << *n2 << "'", s);
}

app_delayed_justification::app_delayed_justification(environment const & env, expr const & e, expr const & f_type, expr const & a_type):
    m_env(env), m_e(e), m_fn_type(f_type), m_arg_type(a_type) {}

justification app_delayed_justification::get() {
    if (!m_jst) {
        // We should not have a reference to this object inside the closure.
        // So, we create the following locals that will be captured by the closure instead of 'this'.
        environment env = m_env;
        expr e          = m_e;
        expr fn_type    = m_fn_type;
        expr arg_type   = m_arg_type;
        m_jst = mk_justification(app_arg(e),
                                 [=](formatter const & fmt, options const & o, substitution const & subst) {
                                     return pp_app_type_mismatch(fmt, env, o,
                                                                 subst.instantiate_metavars_wo_jst(e),
                                                                 subst.instantiate_metavars_wo_jst(binding_domain(fn_type)),
                                                                 subst.instantiate_metavars_wo_jst(arg_type));
                                 });
    }
    return *m_jst;
}

/**
   \brief Return type of expression \c e, if \c infer_only is false, then it also check whether \c e is type correct or not.

   \pre closed(e)
*/
expr type_checker::infer_type_core(expr const & e, bool infer_only) {
    if (is_var(e))
        throw_kernel_exception(m_env, "type checker does not support free variables, replace them with local constants before invoking it", e);

    lean_assert(closed(e));
    check_system("type checker");

    if (m_memoize) {
        auto it = m_infer_type_cache[infer_only].find(e);
        if (it != m_infer_type_cache[infer_only].end())
            return it->second;
    }

    expr r;
    switch (e.kind()) {
    case expr_kind::Local: case expr_kind::Meta:
        r = mlocal_type(e);
        break;
    case expr_kind::Var:
        lean_unreachable();  // LCOV_EXCL_LINE
    case expr_kind::Sort:
        if (!infer_only)
            check_level(sort_level(e), e);
        r = mk_sort(mk_succ(sort_level(e)));
        break;
    case expr_kind::Constant: {
        declaration d    = m_env.get(const_name(e));
        auto const & ps = d.get_univ_params();
        auto const & ls = const_levels(e);
        if (length(ps) != length(ls))
            throw_kernel_exception(m_env, sstream() << "incorrect number of universe levels parameters for '" << const_name(e) << "', #"
                                   << length(ps)  << " expected, #" << length(ls) << " provided");
        if (!infer_only) {
            for (level const & l : ls)
                check_level(l, e);
        }
        r = instantiate_params(d.get_type(), ps, ls);
        break;
    }
    case expr_kind::Macro: {
        buffer<expr> arg_types;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            arg_types.push_back(infer_type_core(macro_arg(e, i), infer_only));
        r = macro_def(e).get_type(e, arg_types.data(), m_tc_ctx);
        if (!infer_only && macro_def(e).trust_level() >= m_env.trust_lvl()) {
            optional<expr> m = expand_macro(e);
            if (!m)
                throw_kernel_exception(m_env, "failed to expand macro", e);
            expr t = infer_type_core(*m, infer_only);
            simple_delayed_justification jst([=]() { return mk_macro_jst(e); });
            if (!is_def_eq(r, t, jst))
                throw_kernel_exception(m_env, g_macro_error_msg, e);
        }
        break;
    }
    case expr_kind::Lambda: {
        if (!infer_only) {
            expr t = infer_type_core(binding_domain(e), infer_only);
            ensure_sort_core(t, binding_domain(e));
        }
        auto b = open_binding_body(e);
        r = mk_pi(binding_name(e), binding_domain(e), abstract_local(infer_type_core(b.first, infer_only), b.second), binding_info(e));
        break;
    }
    case expr_kind::Pi: {
        expr t1 = ensure_sort_core(infer_type_core(binding_domain(e), infer_only), binding_domain(e));
        auto b  = open_binding_body(e);
        expr t2 = ensure_sort_core(infer_type_core(b.first, infer_only), binding_body(e));
        if (m_env.impredicative())
            r = mk_sort(mk_imax(sort_level(t1), sort_level(t2)));
        else
            r = mk_sort(mk_max(sort_level(t1), sort_level(t2)));
        break;
    }
    case expr_kind::App: {
        expr f_type = ensure_pi_core(infer_type_core(app_fn(e), infer_only), app_fn(e));
        if (!infer_only) {
            expr a_type = infer_type_core(app_arg(e), infer_only);
            app_delayed_justification jst(m_env, e, f_type, a_type);
            if (!is_def_eq(a_type, binding_domain(f_type), jst)) {
                environment env = m_env;
                throw_kernel_exception(m_env, app_arg(e),
                                       [=](formatter const & fmt, options const & o) {
                                           return pp_app_type_mismatch(fmt, env, o, e, binding_domain(f_type), a_type);
                                       });
            }
        }
        r = instantiate(binding_body(f_type), app_arg(e));
        break;
    }}

    if (m_memoize)
        m_infer_type_cache[infer_only].insert(mk_pair(e, r));

    return r;
}

expr type_checker::infer_type(expr const & e) {
    scope mk_scope(*this);
    expr r = infer_type_core(e, true);
    mk_scope.keep();
    return r;
}

expr type_checker::check(expr const & e, level_param_names const & ps) {
    scope mk_scope(*this);
    flet<level_param_names> updt(m_params, ps);
    expr r = infer_type_core(e, false);
    mk_scope.keep();
    return r;
}

expr type_checker::ensure_sort(expr const & e, expr const & s) {
    scope mk_scope(*this);
    expr r = ensure_sort_core(e, s);
    mk_scope.keep();
    return r;
}

expr type_checker::ensure_pi(expr const & e, expr const & s) {
    scope mk_scope(*this);
    expr r = ensure_pi_core(e, s);
    mk_scope.keep();
    return r;
}

/** \brief Return true iff \c t and \c s are definitionally equal */
bool type_checker::is_def_eq(expr const & t, expr const & s, delayed_justification & jst) {
    scope mk_scope(*this);
    bool r = m_conv->is_def_eq(t, s, *this, jst);
    if (r) mk_scope.keep();
    return r;
}

bool type_checker::is_def_eq(expr const & t, expr const & s) {
    scope mk_scope(*this);
    bool r = m_conv->is_def_eq(t, s, *this);
    if (r) mk_scope.keep();
    return r;
}

bool type_checker::is_def_eq(expr const & t, expr const & s, justification const & j) {
    as_delayed_justification djst(j);
    return is_def_eq(t, s, djst);
}

/** \brief Return true iff \c e is a proposition */
bool type_checker::is_prop(expr const & e) {
    scope mk_scope(*this);
    bool r = whnf(infer_type(e)) == Bool;
    if (r) mk_scope.keep();
    return r;
}

expr type_checker::whnf(expr const & t) {
    return m_conv->whnf(t, *this);
}

void type_checker::push() {
    lean_assert(!m_cache_cs);
    m_infer_type_cache[0].push();
    m_infer_type_cache[1].push();
}

void type_checker::pop() {
    lean_assert(!m_cache_cs);
    m_infer_type_cache[0].pop();
    m_infer_type_cache[1].pop();
}

unsigned type_checker::num_scopes() const {
    lean_assert(m_infer_type_cache[0].num_scopes() == m_infer_type_cache[1].num_scopes());
    return m_infer_type_cache[0].num_scopes();
}

static add_cnstr_fn g_no_constraint_fn = mk_no_contranint_fn();

type_checker::type_checker(environment const & env, name_generator const & g, add_cnstr_fn const & h,
                           std::unique_ptr<converter> && conv, bool memoize):
    m_env(env), m_gen(g), m_add_cnstr_fn(h), m_conv(std::move(conv)), m_tc_ctx(*this),
    m_memoize(memoize), m_cache_cs(false) {
}

type_checker::type_checker(environment const & env, name_generator const & g, std::unique_ptr<converter> && conv, bool memoize):
    type_checker(env, g, g_no_constraint_fn, std::move(conv), memoize) {}

static name g_tmp_prefix = name::mk_internal_unique_name();

type_checker::type_checker(environment const & env):
    type_checker(env, name_generator(g_tmp_prefix), g_no_constraint_fn, mk_default_converter(env), true) {}

type_checker::~type_checker() {}

static void check_no_metavar(environment const & env, name const & n, expr const & e, bool is_type) {
    if (has_metavar(e))
        throw_kernel_exception(env, e,
                               [=](formatter const & fmt, options const & o) {
                                   return pp_decl_has_metavars(fmt, env, o, n, e, is_type);
                               });
}

static void check_no_local(environment const & env, expr const & e) {
    if (has_local(e))
        throw_kernel_exception(env, "failed to add declaration to environment, it contains local constants", e);
}

static void check_no_mlocal(environment const & env, name const & n, expr const & e, bool is_type) {
    check_no_metavar(env, n, e, is_type);
    check_no_local(env, e);
}

static void check_name(environment const & env, name const & n) {
    if (env.find(n))
        throw_already_declared(env, n);
}

static void check_duplicated_params(environment const & env, declaration const & d) {
    level_param_names ls = d.get_univ_params();
    while (!is_nil(ls)) {
        auto const & p = head(ls);
        ls = tail(ls);
        if (std::find(ls.begin(), ls.end(), p) != ls.end()) {
            throw_kernel_exception(env, sstream() << "failed to add declaration to environment, duplicate universe level parameter: '"
                                   << p << "'", d.get_type());
        }
    }
}

certified_declaration check(environment const & env, declaration const & d, name_generator const & g, name_set const & extra_opaque, bool memoize) {
    if (d.is_definition())
        check_no_mlocal(env, d.get_name(), d.get_value(), false);
    check_no_mlocal(env, d.get_name(), d.get_type(), true);
    check_name(env, d.get_name());
    check_duplicated_params(env, d);
    type_checker checker1(env, g, mk_default_converter(env, optional<module_idx>(), memoize, extra_opaque));
    checker1.check(d.get_type(), d.get_univ_params());
    if (d.is_definition()) {
        optional<module_idx> midx;
        if (d.is_opaque())
            midx = optional<module_idx>(d.get_module_idx());
        type_checker checker2(env, g, mk_default_converter(env, midx, memoize, extra_opaque));
        expr val_type = checker2.check(d.get_value(), d.get_univ_params());
        if (!checker2.is_def_eq(val_type, d.get_type())) {
            throw_kernel_exception(env, d.get_value(),
                                   [=](formatter const & fmt, options const & o) {
                                       return pp_def_type_mismatch(fmt, env, o, d.get_name(), d.get_type(), val_type);
                                   });
        }
    }
    return certified_declaration(env.get_id(), d);
}

certified_declaration check(environment const & env, declaration const & d, name_set const & extra_opaque, bool memoize) {
    return check(env, d, name_generator(g_tmp_prefix), extra_opaque, memoize);
}
}
