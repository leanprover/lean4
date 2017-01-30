/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/flet.h"
#include "util/thread.h"
#include "kernel/find_fn.h"
#include "kernel/error_msgs.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/user_recursors.h"
#include "library/aux_recursors.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/scope_pos_info_provider.h"
#include "library/choice.h"
#include "library/string.h"
#include "library/sorry.h"
#include "library/quote.h"
#include "library/util.h"
#include "library/typed_expr.h"
#include "library/annotation.h"
#include "library/pp_options.h"
#include "library/replace_visitor.h"
#include "library/locals.h"
#include "library/private.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"
#include "library/protected.h"
#include "library/message_builder.h"
#include "library/aliases.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/elaborate.h"
#include "library/equations_compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/tactic_evaluator.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/structure_instance.h"

namespace lean {
MK_THREAD_LOCAL_GET(type_context_cache_manager, get_tcm, true /* use binder information at infer_cache */);

static name * g_level_prefix = nullptr;
static name * g_elab_strategy = nullptr;

struct elaborator_strategy_attribute_data : public attr_data {
    elaborator_strategy m_status;
    elaborator_strategy_attribute_data() {}
    elaborator_strategy_attribute_data(elaborator_strategy status) : m_status(status) {}
    virtual unsigned hash() const override { return static_cast<unsigned>(m_status); }
    void write(serializer & s) const { s << static_cast<char>(m_status); }
    void read(deserializer & d) {
        char c; d >> c;
        m_status = static_cast<elaborator_strategy>(c);
    }
};

bool operator==(elaborator_strategy_attribute_data const & d1, elaborator_strategy_attribute_data const & d2) {
    return d1.m_status == d2.m_status;
}

template class typed_attribute<elaborator_strategy_attribute_data>;
typedef typed_attribute<elaborator_strategy_attribute_data> elaborator_strategy_attribute;

static elaborator_strategy_attribute const & get_elaborator_strategy_attribute() {
    return static_cast<elaborator_strategy_attribute const &>(get_system_attribute(*g_elab_strategy));
}

class elaborator_strategy_proxy_attribute : public proxy_attribute<elaborator_strategy_attribute_data> {
    typedef proxy_attribute<elaborator_strategy_attribute_data> parent;
public:
    elaborator_strategy_proxy_attribute(char const * id, char const * descr, elaborator_strategy status):
        parent(id, descr, status) {}

    virtual typed_attribute<elaborator_strategy_attribute_data> const & get_attribute() const {
        return get_elaborator_strategy_attribute();
    }
};

elaborator_strategy get_elaborator_strategy(environment const & env, name const & n) {
    if (auto data = get_elaborator_strategy_attribute().get(env, n))
        return data->m_status;

    if (inductive::is_elim_rule(env, n) ||
        is_aux_recursor(env, n) ||
        is_user_defined_recursor(env, n)) {
        return elaborator_strategy::AsEliminator;
    }

    return elaborator_strategy::WithExpectedType;
}

#define trace_elab(CODE) lean_trace("elaborator", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_detail(CODE) lean_trace("elaborator_detail", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_debug(CODE) lean_trace("elaborator_debug", scope_trace_env _scope(m_env, m_ctx); CODE)

elaborator::elaborator(environment const & env, options const & opts, name const & decl_name,
                       metavar_context const & mctx, local_context const & lctx):
    m_env(env), m_opts(opts), m_decl_name(decl_name),
    m_ctx(env, opts, mctx, lctx, get_tcm(), transparency_mode::Semireducible),
    m_uses_infom(get_global_info_manager() != nullptr) {
}

elaborator::~elaborator() {
    try {
        if (m_uses_infom && get_global_info_manager() && !in_thread_finalization()) {
            m_info.instantiate_mvars(m_ctx.mctx());
            get_global_info_manager()->merge(m_info);
        }
    } catch (...) {}
}

auto elaborator::mk_pp_ctx() -> pp_fn {
    return ::lean::mk_pp_ctx(m_ctx.env(), m_opts, m_ctx.mctx(), m_ctx.lctx());
}

format elaborator::pp_indent(pp_fn const & pp_fn, expr const & e) {
    unsigned i = get_pp_indent(m_opts);
    return nest(i, line() + pp_fn(e));
}

format elaborator::pp_indent(expr const & e) {
    return pp_indent(mk_pp_ctx(), e);
}

format elaborator::pp(expr const & e) {
    auto fn = mk_pp_ctx();
    return fn(e);
}

auto elaborator::pp_until_different(expr const & e1, expr const & e2) -> std::tuple<pp_fn, format, format> {
    flet<options> save_opts(m_opts, m_opts);
    expr n_e1    = erase_binder_info(e1);
    expr n_e2    = erase_binder_info(e2);
    pp_fn fn     = mk_pp_ctx();
    list<options> extra = get_distinguishing_pp_options();
    while (true) {
        format r1 = pp_indent(fn, n_e1);
        format r2 = pp_indent(fn, n_e2);
        if (!format_pp_eq(r1, r2, m_opts) || !extra)
            return std::make_tuple(fn, pp_indent(fn, e1), pp_indent(fn, e2));
        m_opts    = join(head(extra), m_opts);
        fn        = mk_pp_ctx();
        extra     = tail(extra);
    }
}

format elaborator::pp_overload(pp_fn const & pp_fn, expr const & fn) {
    return is_constant(fn) ? format(const_name(fn)) : pp_fn(fn);
}

format elaborator::pp_overloads(pp_fn const & pp_fn, buffer<expr> const & fns) {
    format r("overloads:");
    r += space();
    bool first = true;
    for (expr const & fn : fns) {
        if (first) first = false; else r += format(", ");
        r += pp_overload(pp_fn, fn);
    }
    return paren(r);
}

level elaborator::mk_univ_metavar() {
    return m_ctx.mk_univ_metavar_decl();
}

expr elaborator::mk_metavar(expr const & A, expr const & ref) {
    return copy_tag(ref, m_ctx.mk_metavar_decl(m_ctx.lctx(), A));
}

expr elaborator::mk_metavar(optional<expr> const & A, expr const & ref) {
    if (A)
        return mk_metavar(*A, ref);
    else
        return mk_metavar(mk_type_metavar(ref), ref);
}

expr elaborator::mk_type_metavar(expr const & ref) {
    level l = mk_univ_metavar();
    return mk_metavar(mk_sort(l), ref);
}

expr elaborator::mk_instance_core(local_context const & lctx, expr const & C, expr const & ref) {
    scope_traces_as_messages traces_as_messages(get_pos_info_provider(), ref);

    optional<expr> inst = m_ctx.mk_class_instance_at(lctx, C);
    if (!inst) {
        metavar_context mctx   = m_ctx.mctx();
        local_context new_lctx = lctx.instantiate_mvars(mctx);
        new_lctx = erase_inaccessible_annotations(new_lctx);
        tactic_state s = ::lean::mk_tactic_state_for(m_env, m_opts, m_decl_name, mctx, new_lctx, C);
        throw elaborator_exception(ref, format("failed to synthesize type class instance for") + line() + s.pp());
    }
    return *inst;
}

expr elaborator::mk_instance_core(expr const & C, expr const & ref) {
    return mk_instance_core(m_ctx.lctx(), C, ref);
}

expr elaborator::mk_instance(expr const & C, expr const & ref) {
    if (has_expr_metavar(C)) {
        expr inst = mk_metavar(C, ref);
        m_instances = cons(inst, m_instances);
        return inst;
    } else {
        return mk_instance_core(C, ref);
    }
}

expr elaborator::instantiate_mvars(expr const & e) {
    expr r = m_ctx.instantiate_mvars(e);
    if (r.get_tag() == nulltag)
        r.set_tag(e.get_tag());
    return r;
}

level elaborator::get_level(expr const & A, expr const & ref) {
    expr A_type = whnf(infer_type(A));
    if (is_sort(A_type)) {
        return sort_level(A_type);
    }

    if (is_meta(A_type)) {
        level l = mk_univ_metavar();
        if (try_is_def_eq(A_type, mk_sort(l))) {
            return l;
        }
    }

    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref, format("type expected at") + pp_indent(pp_fn, A));
}

level elaborator::replace_univ_placeholder(level const & l) {
    auto fn = [&](level const & l) {
        if (is_one_placeholder(l))
            return some_level(mk_level_one());
        else if (is_placeholder(l))
            return some_level(mk_univ_metavar());
        else
            return none_level();
    };
    return replace(l, fn);
}

static bool contains_placeholder(level const & l) {
    bool contains = false;
    auto fn = [&](level const & l) {
        if (contains) return false;
        if (is_placeholder(l) || is_one_placeholder(l))
            contains = true;
        return true;
    };
    for_each(l, fn);
    return contains;
}

/* Here, we say a term is first-order IF all applications are of the form (f ...) where f is a constant. */
static bool is_first_order(expr const & e) {
    return !find(e, [&](expr const & e, unsigned) {
            return is_app(e) && !is_constant(get_app_fn(e));
        });
}

bool elaborator::is_elim_elab_candidate(name const & fn) {
    return get_elaborator_strategy(m_env, fn) == elaborator_strategy::AsEliminator;
}

/** See comment at elim_info */
auto elaborator::get_elim_info_for_builtin(name const & fn) -> elim_info {
    lean_assert(is_aux_recursor(m_env, fn) || inductive::is_elim_rule(m_env, fn));
    /* Remark: this is not just an optimization. The code at use_elim_elab_core
       only works for dependent elimination. */
    lean_assert(!fn.is_atomic());
    name const & I_name    = fn.get_prefix();
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(m_env, I_name);
    lean_assert(decl);
    unsigned nparams  = decl->m_num_params;
    unsigned nindices = *inductive::get_num_indices(m_env, I_name);
    unsigned nminors  = length(decl->m_intro_rules);
    elim_info r;
    if (strcmp(fn.get_string(), "brec_on") == 0 || strcmp(fn.get_string(), "binduction_on") == 0) {
        r.m_arity      = nparams + 1 /* motive */ + nindices + 1 /* major */ + 1;
    } else {
        r.m_arity      = nparams + 1 /* motive */ + nindices + 1 /* major */ + nminors;
    }
    r.m_nexplicit  = 1 /* major premise */ + nminors;
    if (nminors == 0) {
        /* The motive is marked as explicit in builtin recursors that do not have
           minor premises */
        r.m_nexplicit++;
    }
    r.m_motive_idx = nparams;
    unsigned major_idx;
    if (inductive::is_elim_rule(m_env, fn)) {
        major_idx = nparams + 1 + nindices + nminors;
    } else {
        major_idx = nparams + 1 + nindices;
    }
    r.m_idxs = to_list(major_idx);
    return r;
}

/** See comment at elim_info */
auto elaborator::use_elim_elab_core(name const & fn) -> optional<elim_info> {
    if (!is_elim_elab_candidate(fn))
        return optional<elim_info>();
    if (is_aux_recursor(m_env, fn) || inductive::is_elim_rule(m_env, fn)) {
        return optional<elim_info>(get_elim_info_for_builtin(fn));
    }
    type_context::tmp_locals locals(m_ctx);
    declaration d     = m_env.get(fn);
    expr type         = d.get_type();
    while (is_pi(type)) {
        type = instantiate(binding_body(type), locals.push_local_from_binding(type));
    }

    buffer<expr> C_args;
    expr const & C = get_app_args(type, C_args);
    if (!is_local(C) || C_args.empty() || !std::all_of(C_args.begin(), C_args.end(), is_local)) {
        format msg = format("'eliminator' elaboration is not used for '") + format(fn) +
            format("' because resulting type is not of the expected form\n");
        m_elim_failure_info.insert(fn, msg);
        return optional<elim_info>();
    }

    buffer<expr> const & params = locals.as_buffer();
    optional<unsigned> _midx = params.index_of(C);
    if (!_midx)
        return optional<elim_info>();

    unsigned midx = *_midx;
    buffer<unsigned> idxs;
    buffer<bool>     found;
    found.resize(C_args.size(), false);
    unsigned i    = params.size();
    unsigned nexplicit = 0;
    while (i > 0) {
        --i;
        expr const & param = params[i];

        if (!is_explicit(local_info(param))) {
            continue;
        }
        nexplicit++;

        if (optional<unsigned> pos = C_args.index_of(param)) {
            // Parameter is an argument of the resulting type (C ...)
            if (!found[*pos]) {
                // We store it if we could not infer it using the type of other arguments.
                found[*pos] = true;
                idxs.push_back(i);
            }
        }

        expr param_type = m_ctx.infer(param);
        if (!is_first_order(param_type))
            continue;

        bool collected = false;
        for_each(param_type, [&](expr const & e, unsigned) {
                if (is_local(e)) {
                    if (optional<unsigned> pos = C_args.index_of(e)) {
                        if (!found[*pos]) {
                            collected   = true;
                            found[*pos] = true;
                        }
                    }
                }
                return true;
            });
        if (collected)
            idxs.push_back(i);
    }

    for (unsigned i = 0; i < found.size(); i++) {
        if (!found[i]) {
            format msg = format("'eliminator' elaboration is not used for '") + format(fn) +
                format("' because a (reliable) way to synthesize '") + pp(C_args[i]) +
                format("', which occurs in the resulting type, was not found\n");
            m_elim_failure_info.insert(fn, msg);
            return optional<elim_info>();
        }
    }

    std::reverse(idxs.begin(), idxs.end());
    trace_elab_detail(tout() << "'eliminator' elaboration is going to be used for '" << fn << "' applications, "
                      << "the motive is computed using the argument(s):";
                      for (unsigned idx : idxs) tout() << " #" << (idx+1);
                      tout() << "\n";);
    return optional<elim_info>(params.size(), nexplicit, midx, to_list(idxs));
}

/** See comment at elim_info */
auto elaborator::use_elim_elab(name const & fn) -> optional<elim_info> {
    if (auto it = m_elim_cache.find(fn))
        return *it;
    optional<elim_info> r = use_elim_elab_core(fn);
    m_elim_cache.insert(fn, r);
    return r;
}

void elaborator::trace_coercion_failure(expr const & e_type, expr const & type, expr const & ref, char const * error_msg) {
    trace_elab({
            auto pp_fn = mk_pp_ctx();
            format msg("coercion at ");
            msg += format(pos_string_for(ref));
            msg += space() + format("from");
            msg += pp_indent(pp_fn, e_type);
            msg += line() + format("to");
            msg += pp_indent(pp_fn, type);
            msg += line() + format(error_msg);
            tout() << msg << "\n";
        });
}

optional<expr> elaborator::mk_coercion_core(expr const & e, expr const & e_type, expr const & type, expr const & ref) {
    if (!has_expr_metavar(e_type) && !has_expr_metavar(type)) {
        expr has_coe_t;
        try {
            has_coe_t = mk_app(m_ctx, get_has_coe_t_name(), e_type, type);
        } catch (app_builder_exception & ex) {
            trace_coercion_failure(e_type, type, ref,
                                   "failed create type class expression 'has_coe_t' "
                                   "('set_option trace.app_builder true' for more information)");
            return none_expr();
        }
        optional<expr> inst;
        try {
            inst = m_ctx.mk_class_instance_at(m_ctx.lctx(), has_coe_t);
        } catch (class_exception &) {
            trace_coercion_failure(e_type, type, ref,
                                   "failed to synthesize class instance for 'has_coe_t' "
                                   "('set_option trace.class_instances true' for more information)");
            return none_expr();
        }
        if (!inst) {
            trace_coercion_failure(e_type, type, ref,
                                   "failed to synthesize 'has_coe_t' type class instance "
                                   "('set_option trace.class_instances true' for more information)");
            return none_expr();
        }
        level u_1 = get_level(e_type, ref);
        level u_2 = get_level(type, ref);
        expr coe_to_lift = mk_app(mk_constant(get_coe_to_lift_name(), {u_1, u_2}), e_type, type, *inst);
        expr coe         = mk_app(mk_constant(get_coe_name(), {u_1, u_2}), e_type, type, coe_to_lift, e);
        return some_expr(coe);
    } else {
        return none_expr();
    }
}

bool elaborator::is_monad(expr const & e) {
    try {
        expr m = mk_app(m_ctx, get_monad_name(), e);
        return static_cast<bool>(m_ctx.mk_class_instance(m));
    } catch (app_builder_exception &) {
        return false;
    } catch (class_exception &) {
        return false;
    }
}

/*
   When lifting monads in do-notation and/or bind, it is very common to have coercion problems such as

          tactic name  ===>  solver ?a

   Coercion resolution cannot be used because (solver ?a) contains meta-variables. Recall that
   coercion resolution is based on type class resolution, and we can only synthesize type class instances
   if the type does not contain meta-variables.

   The coercion problem above is generated in scenarios such as

       do v ← t1,
          ...

   which is notation for

       @bind ?m ?inst ?a ?b t1 (fun v : ?a, ...)

   Now, assume (t1 : tactic name) and the expected type is (solver unit).
   Then, the following meta-variables can be resolved.

        ?m    := solver
        ?b    := unit
        ?inst := solver.monad

   and we get

       @bind solver solver.monad ?a unit t1 (fun v : ?a, ...)

   At this point, we get a type mismatch at t1 because th expected type is (solver ?a) and the given type
   is (tactic name).

   In this method, we consider the following compromise: we assign ?a := name, and then, try to perform
   coercion resolution again.

   Remark: this method also handle the case where the metavariable is at e_type. Example:

          tactic ?a    ===> smt_tactic unit

   TODO(leo): can/should we generalize this approach? */
optional<expr> elaborator::try_monad_coercion(expr const & e, expr const & e_type, expr type, expr const & ref) {
    if ((has_expr_metavar(e_type) && has_expr_metavar(type))
        || (!has_expr_metavar(e_type) && !has_expr_metavar(type))
        || !is_app(e_type)
        || !is_app(type)
        || has_expr_metavar(app_fn(type))
        || has_expr_metavar(app_fn(e_type))
        || (!is_metavar(app_arg(e_type)) && !is_metavar(app_arg(type)))
        || !is_monad(app_fn(e_type))
        || !is_monad(app_fn(type))) {
        /* Not applicable */
        return none_expr();
    }
    if (!m_ctx.is_def_eq(app_arg(e_type), app_arg(type)))
        return none_expr();
    type   = instantiate_mvars(type);
    return mk_coercion_core(e, e_type, type, ref);
}

optional<expr> elaborator::mk_coercion(expr const & e, expr e_type, expr type, expr const & ref) {
    e_type = instantiate_mvars(e_type);
    type   = instantiate_mvars(type);
    if (!has_expr_metavar(e_type) && !has_expr_metavar(type)) {
        return mk_coercion_core(e, e_type, type, ref);
    } else if (auto r = try_monad_coercion(e, e_type, type, ref)) {
        return r;
    } else {
        trace_coercion_failure(e_type, type, ref,
                               "was not considered because types contain metavariables");
        return none_expr();
    }
}

bool elaborator::is_def_eq(expr const & e1, expr const & e2) {
    type_context::approximate_scope scope(m_ctx);
    try {
        return m_ctx.is_def_eq(e1, e2);
    } catch (exception &) {
        return false;
    }
}

bool elaborator::try_is_def_eq(expr const & e1, expr const & e2) {
    snapshot S(*this);
    try {
        return is_def_eq(e1, e2);
    } catch (exception &) {
        S.restore(*this);
        throw;
    }
    S.restore(*this);
    return false;
}

optional<expr> elaborator::ensure_has_type(expr const & e, expr const & e_type, expr const & type, expr const & ref) {
    if (is_def_eq(e_type, type))
        return some_expr(e);
    return mk_coercion(e, e_type, type, ref);
}

expr elaborator::enforce_type(expr const & e, expr const & expected_type, char const * header, expr const & ref) {
    expr e_type = infer_type(e);
    if (auto r = ensure_has_type(e, e_type, expected_type, ref)) {
        return *r;
    } else {
        auto pp_data = pp_until_different(e_type, expected_type);
        auto pp_fn   = std::get<0>(pp_data);
        format msg = format(header);
        msg += format(", expression") + pp_indent(pp_fn, e);
        msg += line() + format("has type") + std::get<1>(pp_data);
        msg += line() + format("but is expected to have type") + std::get<2>(pp_data);
        throw elaborator_exception(ref, msg);
    }
}

void elaborator::trace_coercion_fn_sort_failure(bool is_fn, expr const & e_type, expr const & ref, char const * error_msg) {
    trace_elab({
            format msg("coercion at ");
            auto pp_fn = mk_pp_ctx();
            msg += format(pos_string_for(ref));
            msg += space() + format("from");
            msg += pp_indent(pp_fn, e_type);
            if (is_fn)
                msg += line() + format("to function space");
            else
                msg += line() + format("to sort");
            msg += line() + format(error_msg);
            tout() << msg << "\n";
        });
}

optional<expr> elaborator::mk_coercion_to_fn_sort(bool is_fn, expr const & e, expr const & _e_type, expr const & ref) {
    expr e_type = instantiate_mvars(_e_type);
    if (!has_expr_metavar(e_type)) {
        try {
            bool mask[3] = { true, false, true };
            expr args[2] = { e_type, e };
            expr new_e = mk_app(m_ctx, is_fn ? get_coe_fn_name() : get_coe_sort_name(), 3, mask, args);
            expr new_e_type = whnf(infer_type(new_e));
            if ((is_fn && is_pi(new_e_type)) || (!is_fn && is_sort(new_e_type))) {
                return some_expr(new_e);
            }
            trace_coercion_fn_sort_failure(is_fn, e_type, ref,
                                           "coercion was successfully generated, but resulting type is not the expected one");
            return none_expr();
        } catch (app_builder_exception & ex) {
            trace_coercion_fn_sort_failure(is_fn, e_type, ref,
                                           "failed create coercion application using type class resolution "
                                           "('set_option trace.app_builder true' and 'set_option trace.class_instances true' for more information)");
            return none_expr();
        }
    } else {
        trace_coercion_fn_sort_failure(is_fn, e_type, ref,
                                       "was not considered because type contain metavariables");
        return none_expr();
    }
}

expr elaborator::ensure_function(expr const & e, expr const & ref) {
    expr e_type = whnf(infer_type(e));
    if (is_pi(e_type)) {
        return e;
    }
    if (auto r = mk_coercion_to_fn(e, e_type, ref)) {
        return *r;
    }
    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref, format("function expected at") + pp_indent(pp_fn, e));
}

expr elaborator::ensure_type(expr const & e, expr const & ref) {
    expr e_type = whnf(infer_type(e));
    if (is_sort(e_type)) {
        return e;
    }

    if (is_meta(e_type) && is_def_eq(e_type, mk_sort(mk_univ_metavar()))) {
        return e;
    }

    if (auto r = mk_coercion_to_sort(e, e_type, ref)) {
        return *r;
    }

    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref, format("type expected at") + pp_indent(pp_fn, e));
}

static expr get_ref_for_child(expr const & arg, expr const & ref) {
    if (get_pos_info_provider() && get_pos_info_provider()->get_pos_info(arg)) {
        return arg;
    } else {
        /* using ref because position info for argument is not available */
        return ref;
    }
}

expr elaborator::visit_typed_expr(expr const & e) {
    expr ref          = e;
    expr val          = get_typed_expr_expr(e);
    expr type         = get_typed_expr_type(e);
    expr new_type;
    expr ref_type     = get_ref_for_child(type, e);
    new_type = ensure_type(visit(type, none_expr()), ref_type);
    synthesize_type_class_instances();
    expr new_val      = visit(val, some_expr(new_type));
    expr new_val_type = infer_type(new_val);
    if (auto r = ensure_has_type(new_val, new_val_type, new_type, ref))
        return *r;

    auto pp_data = pp_until_different(new_val_type, new_type);
    auto pp_fn   = std::get<0>(pp_data);
    throw elaborator_exception(ref,
                               format("invalid type ascription, expression has type") + std::get<1>(pp_data) +
                               line() + format("but is expected to have type") + std::get<2>(pp_data));
}

level elaborator::dec_level(level const & l, expr const & ref) {
    if (auto d = ::lean::dec_level(l))
        return *d;
    level r = m_ctx.mk_univ_metavar_decl();
    if (!m_ctx.is_def_eq(mk_succ(r), l))
        throw elaborator_exception(ref, "invalid pre-numeral, universe level must be > 0");
    return r;
}

expr elaborator::visit_prenum(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_prenum(e));
    expr ref = e;
    mpz const & v  = prenum_value(e);
    tag e_tag      = e.get_tag();
    expr A;
    if (expected_type) {
        A = *expected_type;
        if (is_metavar(*expected_type))
            m_numeral_types = cons(A, m_numeral_types);
    } else {
        A = mk_type_metavar(ref);
        m_numeral_types = cons(A, m_numeral_types);
    }
    level A_lvl = get_level(A, ref);
    levels ls(dec_level(A_lvl, ref));
    if (v.is_neg())
        throw elaborator_exception(ref, "invalid pre-numeral, it must be a non-negative value");
    if (v.is_zero()) {
        expr has_zero_A = mk_app(mk_constant(get_has_zero_name(), ls), A, e_tag);
        expr S          = mk_instance(has_zero_A, ref);
        return mk_app(mk_app(mk_constant(get_zero_name(), ls), A, e_tag), S, e_tag);
    } else {
        expr has_one_A = mk_app(mk_constant(get_has_one_name(), ls), A, e_tag);
        expr S_one     = mk_instance(has_one_A, ref);
        expr one       = mk_app(mk_app(mk_constant(get_one_name(), ls), A, e_tag), S_one, e_tag);
        if (v == 1) {
            return one;
        } else {
            expr has_add_A = mk_app(mk_constant(get_has_add_name(), ls), A, e_tag);
            expr S_add     = mk_instance(has_add_A, ref);
            std::function<expr(mpz const & v)> convert = [&](mpz const & v) {
                lean_assert(v > 0);
                if (v == 1)
                    return one;
                else if (v % mpz(2) == 0) {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_constant(get_bit0_name(), ls), A, e_tag), S_add, e_tag), r, e_tag);
                } else {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_app(mk_constant(get_bit1_name(), ls), A, e_tag), S_one, e_tag),
                                         S_add, e_tag), r, e_tag);
                }
            };
            return convert(v);
        }
    }
}

expr elaborator::visit_sort(expr const & e) {
    level new_l = replace_univ_placeholder(sort_level(e));
    expr r = update_sort(e, new_l);
    if (contains_placeholder(sort_level(e)))
        m_to_check_sorts.emplace_back(e, r);
    return r;
}

expr elaborator::visit_const_core(expr const & e) {
    declaration d = m_env.get(const_name(e));
    buffer<level> ls;
    for (level const & l : const_levels(e)) {
        level new_l = replace_univ_placeholder(l);
        ls.push_back(new_l);
    }
    unsigned num_univ_params = d.get_num_univ_params();
    if (num_univ_params < ls.size()) {
        format msg("incorrect number of universe levels parameters for '");
        msg += format(const_name(e)) + format("', #") + format(num_univ_params);
        msg += format(" expected, #") + format(ls.size()) + format("provided");
        throw elaborator_exception(e, msg);
    }
    // "fill" with meta universe parameters
    for (unsigned i = ls.size(); i < num_univ_params; i++)
        ls.push_back(mk_univ_metavar());
    lean_assert(num_univ_params == ls.size());
    return update_constant(e, to_list(ls.begin(), ls.end()));
}

/** \brief Auxiliary function for saving information about which overloaded identifier was used by the elaborator. */
void elaborator::save_identifier_info(expr const & f, optional<pos_info> pos) {
    if (!m_no_info && m_uses_infom && get_pos_info_provider() && (is_constant(f) || is_local(f))) {
        if (!pos)
            pos = get_pos_info_provider()->get_pos_info(f);
        if (pos) {
            m_info.add_identifier_info(pos->first, pos->second, is_constant(f) ? const_name(f) : local_pp_name(f));
            m_info.add_type_info(pos->first, pos->second, infer_type(f));
        }
    }
}

expr elaborator::visit_function(expr const & fn, bool has_args, expr const & ref) {
    if (is_placeholder(fn)) {
        throw elaborator_exception(ref, "placeholders '_' cannot be used where a function is expected");
    }
    expr r;
    switch (fn.kind()) {
    case expr_kind::Var:
    case expr_kind::Pi:
    case expr_kind::Meta:
    case expr_kind::Sort:
        throw elaborator_exception(ref, "invalid application, function expected");
    // The expr_kind::App case can only happen when nary notation is used
    case expr_kind::App:       r = visit(fn, none_expr()); break;
    case expr_kind::Local:     r = fn; break;
    case expr_kind::Constant:  r = visit_const_core(fn); break;
    case expr_kind::Macro:     r = visit_macro(fn, none_expr(), true); break;
    case expr_kind::Lambda:    r = visit_lambda(fn, none_expr()); break;
    case expr_kind::Let:       r = visit_let(fn, none_expr()); break;
    }
    save_identifier_info(r);
    if (has_args)
        r = ensure_function(r, ref);
    return r;
}

void elaborator::validate_overloads(buffer<expr> const & fns, expr const & ref) {
    for (expr const & fn_i : fns) {
        if (is_constant(fn_i) && use_elim_elab(const_name(fn_i))) {
            auto pp_fn = mk_pp_ctx();
            format msg("invalid overloaded application, "
                       "elaborator has special support for '");
            msg += pp_fn(fn_i);
            msg += format("' (it is handled as an \"eliminator\"), "
                          "but this kind of constant cannot be overloaded "
                          "(solution: use fully qualified names) ");
            msg += pp_overloads(pp_fn, fns);
            return throw elaborator_exception(ref, msg);
        }
    }
}

format elaborator::mk_app_type_mismatch_error(expr const & t, expr const & arg, expr const & arg_type,
                                              expr const & expected_type) {
    auto pp_data = pp_until_different(arg_type, expected_type);
    auto pp_fn   = std::get<0>(pp_data);
    format msg   = format("type mismatch at application");
    msg += pp_indent(pp_fn, t);
    msg += line() + format("term");
    msg += pp_indent(pp_fn, arg);
    msg += line() + format("has type");
    msg += std::get<1>(pp_data);
    msg += line() + format("but is expected to have type");
    msg += std::get<2>(pp_data);
    return msg;
}

format elaborator::mk_app_arg_mismatch_error(expr const & t, expr const & arg, expr const & expected_arg) {
    auto pp_data = pp_until_different(arg, expected_arg);
    auto pp_fn   = std::get<0>(pp_data);
    format msg = format("unexpected argument at application");
    msg += pp_indent(pp_fn, t);
    msg += line() + format("given argument");
    msg += std::get<1>(pp_data);
    msg += line() + format("expected argument");
    msg += std::get<2>(pp_data);
    return msg;
}

format elaborator::mk_too_many_args_error(expr const & fn_type) {
    auto pp_fn = mk_pp_ctx();
    return
        format("invalid function application, too many arguments, function type:") +
        pp_indent(pp_fn, fn_type);
}

void elaborator::throw_app_type_mismatch(expr const & t, expr const & arg, expr const & arg_type, expr const & expected_type,
                                         expr const & ref) {
    throw elaborator_exception(ref, mk_app_type_mismatch_error(t, arg, arg_type, expected_type));
}

expr elaborator::visit_elim_app(expr const & fn, elim_info const & info, buffer<expr> const & args,
                                optional<expr> const & _expected_type, expr const & ref) {
    trace_elab_detail(tout() << "recursor/eliminator application at " << pos_string_for(ref) << "\n";);
    lean_assert(info.m_nexplicit <= args.size());
    if (!_expected_type) {
        throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) + format ("' application, ") +
                                   format("elaborator has special support for this kind of application ") +
                                   format("(it is handled as an \"eliminator\"), ") +
                                   format("but the expected type must be known"));
    }
    synthesize_type_class_instances();
    expr expected_type = instantiate_mvars(*_expected_type);
    if (has_expr_metavar(expected_type)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) + format ("' application, ") +
                                   format("elaborator has special support for this kind of application ") +
                                   format("(it is handled as an \"eliminator\"), ") +
                                   format("but expected type must not contain metavariables") +
                                   pp_indent(pp_fn, expected_type));
    }

    trace_elab_debug(
        tout() << "eliminator elaboration for '" << fn << "'\n"
        << "  arity:     " << info.m_arity << "\n"
        << "  nexplicit: " << info.m_nexplicit << "\n"
        << "  motive:    #" << (info.m_motive_idx+1) << "\n"
        << "  \"major\":  ";
        for (unsigned idx : info.m_idxs)
            tout() << " #" << (idx+1);
        tout() << "\n";);

    expr fn_type = try_to_pi(infer_type(fn));
    buffer<expr> new_args;

    /* In the first pass we only process the arguments at info.m_idxs */
    expr type = fn_type;
    unsigned i = 0;
    unsigned j = 0;
    list<unsigned> main_idxs  = info.m_idxs;
    buffer<optional<expr>> postponed_args; // mark arguments that must be elaborated in the second pass.
    {
        while (is_pi(type)) {
            expr const & d = binding_domain(type);
            binder_info const & bi = binding_info(type);
            expr new_arg;
            optional<expr> postponed;
            if (std::find(main_idxs.begin(), main_idxs.end(), i) != main_idxs.end()) {
                {
                    new_arg = visit(args[j], some_expr(d));
                    synthesize();
                    new_arg = instantiate_mvars(new_arg);
                }
                j++;
                if (has_expr_metavar(new_arg)) {
                    auto pp_fn = mk_pp_ctx();
                    throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) +
                                               format ("' application, ") +
                                               format("elaborator has special support for this kind of application ") +
                                               format("(it is handled as an \"eliminator\"), ") +
                                               format("but term") + pp_indent(pp_fn, new_arg) +
                                               line() + format("must not contain metavariables because") +
                                               format(" it is used to compute the motive"));
                }
                expr new_arg_type = infer_type(new_arg);
                if (!is_def_eq(new_arg_type, d)) {
                    new_args.push_back(new_arg);
                    throw elaborator_exception(ref, mk_app_type_mismatch_error(mk_app(fn, new_args),
                                                                               new_arg, new_arg_type, d));
                }
            } else if (is_explicit(bi)) {
                expr arg_ref = args[j];
                new_arg      = mk_metavar(d, arg_ref);
                postponed    = args[j];
                j++;
            } else if (bi.is_inst_implicit()) {
                new_arg = mk_instance(d, ref);
            } else {
                new_arg = mk_metavar(d, ref);
            }
            new_args.push_back(new_arg);
            postponed_args.push_back(postponed);
            type = try_to_pi(instantiate(binding_body(type), new_arg));
            i++;
        }

        lean_assert(new_args.size() == info.m_arity);

        /* Process extra arguments */
        for (; j < args.size(); j++) {
            new_args.push_back(visit(args[j], none_expr()));
        }
        synthesize();
    }

    /* Compute expected_type for the recursor application without extra arguments */
    buffer<expr> extra_args;
    i = new_args.size();
    while (i > info.m_arity) {
        --i;
        expr new_arg      = instantiate_mvars(new_args[i]);
        expr new_arg_type = instantiate_mvars(infer_type(new_arg));
        expected_type     = ::lean::mk_pi("_a", new_arg_type, kabstract(m_ctx, expected_type, new_arg));
        extra_args.push_back(new_arg);
    }
    new_args.shrink(i);
    std::reverse(extra_args.begin(), extra_args.end());

    // Compute motive */
    trace_elab_debug(tout() << "compute motive by using keyed-abstraction:\n  " <<
                     instantiate_mvars(type) << "\nwith\n  " <<
                     expected_type << "\n";);
    expr motive = expected_type;
    buffer<expr> keys;
    get_app_args(type, keys);
    i = keys.size();
    while (i > 0) {
        --i;
        expr k = instantiate_mvars(keys[i]);
        expr k_type    = infer_type(k);
        motive = ::lean::mk_lambda("_x", k_type, kabstract(m_ctx, motive, k));
    }
    trace_elab_debug(tout() << "motive:\n  " << instantiate_mvars(motive) << "\n";);

    expr motive_arg = new_args[info.m_motive_idx];
    if (!is_def_eq(motive_arg, motive)) {
        throw elaborator_exception(ref, "\"eliminator\" elaborator failed to compute the motive");
    }

    try {
        /* Elaborate postponed arguments */
        for (unsigned i = 0; i < new_args.size(); i++) {
            if (optional<expr> arg = postponed_args[i]) {
                lean_assert(is_metavar(new_args[i]));
                expr new_arg_type = instantiate_mvars(infer_type(new_args[i]));
                expr new_arg      = visit(*arg, some_expr(new_arg_type));
                if (!is_def_eq(new_args[i], new_arg)) {
                    auto pp_data = pp_until_different(infer_type(new_arg), new_arg_type);
                    auto pp_fn   = std::get<0>(pp_data);
                    throw elaborator_exception(ref, format("\"eliminator\" elaborator type mismatch, term") +
                                               pp_indent(pp_fn, new_arg) +
                                               line() + format("has type") +
                                               std::get<1>(pp_data) +
                                               line() + format("but is expected to have type") +
                                               std::get<2>(pp_data));
                } else {
                    new_args[i] = new_arg;
                }
            }
        }

        expr r = instantiate_mvars(mk_app(mk_app(fn, new_args), extra_args));
        trace_elab_debug(tout() << "elaborated recursor:\n  " << r << "\n";);
        return r;
    } catch (elaborator_exception & ex) {
        throw nested_elaborator_exception(ref, ex, format("the inferred motive for the eliminator-like application is") +
                                          pp_indent(motive));
    }
}

struct elaborator::first_pass_info {
    buffer<expr> args_mvars;
    buffer<expr> args_expected_types;
    buffer<expr> new_args;
    /* new_args_size[i] contains size of new_args after args_mvars[i] was pushed.
       We need this information for producing error messages. */
    buffer<unsigned> new_args_size;
    buffer<expr>     new_instances;
    /* new_instances_size[i] contains the size of new_instances before (and after) args_mvars[i]
       was pushed. */
    buffer<unsigned> new_instances_size;
};

static optional<expr> is_optional_param(expr const & e) {
    if (is_app_of(e, get_opt_param_name(), 2)) {
        return some_expr(app_arg(e));
    } else {
        return none_expr();
    }
}

/* Check if fn args resulting type matches the expected type, and fill
   first_pass_info & info with information collected in this first pass.
   Return true iff the types match.

   Remark: the arguments \c args are *not* visited in this first pass.
   They are only used in this method to provide location information. */
void elaborator::first_pass(expr const & fn, buffer<expr> const & args,
                            expr const & expected_type, expr const & ref,
                            first_pass_info & info) {
    expr fn_type          = infer_type(fn);
    expr type_before_whnf = fn_type;
    expr type             = whnf(fn_type);
    unsigned i   = 0;
    /* First pass: compute type for an fn-application, and unify it with expected_type.
       We don't visit expelicit arguments at this point. */
    while (is_pi(type)) {
        binder_info const & bi = binding_info(type);
        expr const & d = binding_domain(type);
        if (bi.is_strict_implicit() && i == args.size() && !is_optional_param(d))
            break;
        expr new_arg;
        if (!is_explicit(bi)) {
            // implicit argument
            new_arg = mk_metavar(d, ref);
            if (bi.is_inst_implicit())
                info.new_instances.push_back(new_arg);
            // implicit arguments are tagged as inaccessible in patterns
            if (m_in_pattern)
                new_arg = copy_tag(ref, mk_inaccessible(new_arg));
        } else if (i < args.size()) {
            // explicit argument
            expr const & arg_ref = args[i];
            i++;
            info.args_expected_types.push_back(d);
            new_arg      = mk_metavar(d, arg_ref);
            info.args_mvars.push_back(new_arg);
            info.new_args_size.push_back(info.new_args.size());
            info.new_instances_size.push_back(info.new_instances.size());
        } else if (auto def_value = is_optional_param(d)) {
            new_arg = *def_value;
        } else {
            break;
        }
        info.new_args.push_back(new_arg);
        /* See comment above at visit_base_app_core */
        type_before_whnf = instantiate(binding_body(type), new_arg);
        type             = whnf(type_before_whnf);
    }
    type = type_before_whnf;
    if (i != args.size()) {
        /* failed to consume all explicit arguments, use base elaboration for applications */
        throw elaborator_exception(ref, "too many arguments");
    }
    lean_assert(args.size() == info.args_expected_types.size());
    lean_assert(args.size() == info.args_mvars.size());
    lean_assert(args.size() == info.new_args_size.size());
    lean_assert(args.size() == info.new_instances_size.size());
    if (!is_def_eq(expected_type, type)) {
        auto pp_data = pp_until_different(type, expected_type);
        auto pp_fn   = std::get<0>(pp_data);
        expr e = mk_app(fn, info.new_args);
        throw elaborator_exception(ref, format("type mismatch") + pp_indent(pp_fn, e) +
                                   line() + format("has type") + std::get<1>(pp_data) +
                                   line() + format("but is expected to have type") +
                                   std::get<2>(pp_data));
    }
}

/* Using the information colllected in the first-pass, visit the arguments args.
   And then, create resulting application */
expr elaborator::second_pass(expr const & fn, buffer<expr> const & args,
                             expr const & ref, first_pass_info & info) {
    unsigned j = 0; /* for traversing new_instances */
    /* Second pass: visit explicit arguments using the information
       we gained about their expected types */
    for (unsigned i = 0; i < args.size(); i++) {
        /* Process type class instances upto args[i] */
        for (; j < info.new_instances_size[i]; j++) {
            expr const & mvar = info.new_instances[j];
            if (!try_synthesize_type_class_instance(mvar))
                m_instances = cons(mvar, m_instances);
        }
        expr ref_arg      = get_ref_for_child(args[i], ref);
        expr new_arg      = visit(args[i], some_expr(info.args_expected_types[i]));
        expr new_arg_type = infer_type(new_arg);
        optional<expr> new_new_arg = ensure_has_type(new_arg, new_arg_type, info.args_expected_types[i], ref_arg);
        if (!new_new_arg) {
            info.new_args.shrink(info.new_args_size[i]);
            info.new_args.push_back(new_arg);
            format msg = mk_app_type_mismatch_error(mk_app(fn, info.new_args.size(), info.new_args.data()),
                                                    new_arg, new_arg_type, info.args_expected_types[i]);
            throw elaborator_exception(ref, msg);
        }
        if (!is_def_eq(info.args_mvars[i], *new_new_arg)) {
            info.new_args.shrink(info.new_args_size[i]);
            info.new_args.push_back(new_arg);
            format msg = mk_app_arg_mismatch_error(mk_app(fn, info.new_args.size(), info.new_args.data()),
                                                   new_arg, info.args_mvars[i]);
            throw elaborator_exception(ref, msg);
        }
        info.new_args[info.new_args_size[i]] = *new_new_arg;
    }
    for (; j < info.new_instances.size(); j++) {
        expr const & mvar = info.new_instances[j];
        if (!try_synthesize_type_class_instance(mvar))
            m_instances = cons(mvar, m_instances);
    }
    return mk_app(fn, info.new_args.size(), info.new_args.data());
}

bool elaborator::is_with_expected_candidate(expr const & fn) {
    if (!is_constant(fn)) return false;
    return get_elaborator_strategy(m_env, const_name(fn)) == elaborator_strategy::WithExpectedType;
}

expr elaborator::visit_base_app_simple(expr const & _fn, arg_mask amask, buffer<expr> const & args,
                                       bool args_already_visited, optional<expr> const & expected_type, expr const & ref) {
    expr fn      = _fn;
    expr fn_type = infer_type(fn);
    unsigned i = 0;
    buffer<expr> new_args;

    /* We manually track the type before whnf. We do that because after the loop
       we check whether the application type is definitionally equal to expected_type.
       Suppose, the result type is (tactic expr) and the expected type is (?M1 ?M2).
       The unification problem can be solved using first-order unification, but if we
       unfold (tactic expr), we get (tactic_state -> base_tactic_result ...) which cannot.

       The statement
         expr type = try_to_pi(fn_type);
       also does not work because (tactic expr) unfolds into a type. */
    expr type_before_whnf = fn_type;
    expr type             = whnf(fn_type);
    while (true) {
        if (is_pi(type)) {
            binder_info const & bi = binding_info(type);
            expr const & d = binding_domain(type);
            expr new_arg;
            if (amask == arg_mask::Default && bi.is_strict_implicit() && i == args.size() && !is_optional_param(d))
                break;
            if ((amask == arg_mask::Default && !is_explicit(bi)) ||
                (amask == arg_mask::InstHoExplicit && !is_explicit(bi) && !bi.is_inst_implicit() && !is_pi(d))) {
                // implicit argument
                if (bi.is_inst_implicit())
                    new_arg = mk_instance(d, ref);
                else
                    new_arg = mk_metavar(d, ref);
                // implicit arguments are tagged as inaccessible in patterns
                if (m_in_pattern)
                    new_arg = copy_tag(ref, mk_inaccessible(new_arg));
            } else if (i < args.size()) {
                // explicit argument
                expr ref_arg = get_ref_for_child(args[i], ref);
                if (args_already_visited) {
                    new_arg = args[i];
                } else if (bi.is_inst_implicit() && is_placeholder(args[i])) {
                    lean_assert(amask != arg_mask::Default);
                    /* If '@' or '@@' have been used, and the argument is '_', then
                       we use type class resolution. */
                    new_arg = mk_instance(d, ref);
                } else {
                    new_arg = visit(args[i], some_expr(d));
                }
                expr new_arg_type = infer_type(new_arg);
                if (optional<expr> new_new_arg = ensure_has_type(new_arg, new_arg_type, d, ref_arg)) {
                    new_arg = *new_new_arg;
                } else {
                    new_args.push_back(new_arg);
                    format msg = mk_app_type_mismatch_error(mk_app(fn, new_args.size(), new_args.data()),
                                                            new_arg, new_arg_type, d);
                    throw elaborator_exception(ref, msg);
                }
                i++;
            } else if (auto def_value = is_optional_param(d)) {
                new_arg = *def_value;
            } else {
                break;
            }
            new_args.push_back(new_arg);
            /* See comment above at first type_before_whnf assignment */
            type_before_whnf = instantiate(binding_body(type), new_arg);
            type             = whnf(type_before_whnf);
        } else if (i < args.size()) {
            expr new_fn = mk_app(fn, new_args.size(), new_args.data());
            new_args.clear();
            fn = ensure_function(new_fn, ref);
            type_before_whnf = infer_type(fn);
            type = whnf(type_before_whnf);
        } else {
            lean_assert(i == args.size());
            break;
        }
    }

    type = type_before_whnf;

    expr r = mk_app(fn, new_args.size(), new_args.data());
    if (expected_type) {
        if (auto new_r = ensure_has_type(r, instantiate_mvars(type), *expected_type, ref)) {
            return *new_r;
        } else {
            /* We do not generate the error here because we can produce a better one from
               the caller (i.e., place the set the expected_type) */
        }
    }
    return r;
}

expr elaborator::visit_base_app_core(expr const & fn, arg_mask amask, buffer<expr> const & args,
                                     bool args_already_visited, optional<expr> const & expected_type, expr const & ref) {
    /** Check if this application is a candidate for propagating the expected type to arguments */
    if (args_already_visited || /* if the arguments have already been visited, then there is no point. */
        amask != arg_mask::Default || /* we do not propagate expected type info when @ and @@ are used */
        !is_with_expected_candidate(fn) ||
        !expected_type) {
        return visit_base_app_simple(fn, amask, args, args_already_visited, expected_type, ref);
    }

    snapshot C(*this);
    first_pass_info info;
    try {
        /* In the first pass, we skip universe contraints such as

               (max 1 ?m) =?= ?m
               (max ?m1 1) =?= (max 1 ?m2)

           The first one cannot be solved by type_context, and an approximate
           solution is used for the second one. In the second pass, we will have
           additional information propagated from the expected_type, and these
           constraints may become trivial.

           The following definition illustrates the issue:

              meta def foo (ex_lst : list name) (e : expr) : list name :=
              expr.fold e [] (λ _ _ l, l)

           expr.fold has type

              meta constant expr.fold {α : Type} : expr → α → (expr → nat → α → α) → α

           So, when processing [], we have to unify ?α with (list ?m), where

                     ?α      : Type 1
                     list ?m : Type (max 1 ?u)

           Thus, we also have to solve

                   1 =?= (max 1 ?u)

           which, as described above, cannot be solved by type_context.
           However, this constraint becomes trivial after we propagate the expected type
           (list name), and we have to solve (list name) =?= (list ?m)
        */
        type_context::full_postponed_scope scope(m_ctx, false);
        first_pass(fn, args, *expected_type, ref, info);
    } catch (elaborator_exception & ex1) {
        C.restore(*this);
        try {
            return visit_base_app_simple(fn, amask, args, args_already_visited, expected_type, ref);
        } catch (elaborator_exception & ex2) {
            throw nested_elaborator_exception(ref, ex2,
                                              format("switched to simple application elaboration procedure because "
                                                     "failed to use expected type to elaborate it, "
                                                     "error message") + nest(get_pp_indent(m_opts), line() + ex1.pp()));
        }
    }
    return second_pass(fn, args, ref, info);
}

expr elaborator::visit_base_app(expr const & fn, arg_mask amask, buffer<expr> const & args,
                                optional<expr> const & expected_type, expr const & ref) {
    return visit_base_app_core(fn, amask, args, false, expected_type, ref);
}

expr elaborator::visit_overload_candidate(expr const & fn, buffer<expr> const & args,
                                          optional<expr> const & expected_type, expr const & ref) {
    return visit_base_app_core(fn, arg_mask::Default, args, true, expected_type, ref);
}

format elaborator::mk_no_overload_applicable_msg(buffer<expr> const & fns, buffer<elaborator_exception> const & error_msgs) {
    format r("none of the overloads are applicable");
    lean_assert(error_msgs.size() == fns.size());
    for (unsigned i = 0; i < fns.size(); i++) {
        if (i > 0) r += line();
        auto pp_fn = mk_pp_ctx();
        r += line() + format("error for") + space() + pp_overload(pp_fn, fns[i]);
        r += line() + error_msgs[i].pp();
    }
    return r;
}

void elaborator::throw_no_overload_applicable(buffer<expr> const & fns, buffer<elaborator_exception> const & error_msgs,
                                              expr const & ref) {
    throw elaborator_exception(ref, mk_no_overload_applicable_msg(fns, error_msgs));
}

expr elaborator::visit_overloaded_app_core(buffer<expr> const & fns, buffer<expr> const & args,
                                           optional<expr> const & expected_type, expr const & ref) {
    buffer<expr> new_args;
    for (expr const & arg : args) {
        new_args.push_back(copy_tag(arg, visit(arg, none_expr())));
    }

    snapshot S(*this);

    buffer<pair<expr, snapshot>> candidates;
    buffer<elaborator_exception> error_msgs;
    for (expr const & fn : fns) {
        try {
            // Restore state
            S.restore(*this);
            bool has_args = !args.empty();
            expr new_fn   = visit_function(fn, has_args, ref);
            expr c        = visit_overload_candidate(new_fn, new_args, expected_type, ref);
            synthesize_type_class_instances();

            if (expected_type) {
                expr c_type = infer_type(c);
                if (ensure_has_type(c, c_type, *expected_type, ref)) {
                    candidates.emplace_back(c, snapshot(*this));
                } else {
                    auto pp_data = pp_until_different(c_type, *expected_type);
                    auto pp_fn   = std::get<0>(pp_data);
                    throw elaborator_exception(ref, format("invalid overload, expression") + pp_indent(pp_fn, c) +
                                               line() + format("has type") + std::get<1>(pp_data) +
                                               line() + format("but is expected to have type") +
                                               std::get<2>(pp_data));
                }
            } else {
                candidates.emplace_back(c, snapshot(*this));
            }
        } catch (elaborator_exception & ex) {
            error_msgs.push_back(ex);
        } catch (exception & ex) {
            error_msgs.push_back(elaborator_exception(ref, format(ex.what())));
        }
    }
    lean_assert(candidates.size() + error_msgs.size() == fns.size());

    if (candidates.empty()) {
        S.restore(*this);

        throw_no_overload_applicable(fns, error_msgs, ref);
    } else if (candidates.size() > 1) {
        S.restore(*this);

        options new_opts = m_opts.update_if_undef(get_pp_full_names_name(), true);
        flet<options> set_opts(m_opts, new_opts);
        auto pp_fn = mk_pp_ctx();
        format r("ambiguous overload, possible interpretations");
        for (auto const & c : candidates) {
            r += pp_indent(pp_fn, c.first);
        }
        throw elaborator_exception(ref, r);
    } else {
        // Restore successful state
        candidates[0].second.restore(*this);
        return candidates[0].first;
    }
}

expr elaborator::visit_overloaded_app_with_expected(buffer<expr> const & fns, buffer<expr> const & args,
                                                    expr const & expected_type, expr const & ref) {
    snapshot S(*this);
    buffer<std::tuple<expr, snapshot, first_pass_info>> candidates;
    buffer<elaborator_exception> error_msgs;
    for (expr const & fn : fns) {
        try {
            // Restore state
            S.restore(*this);
            bool has_args = !args.empty();
            expr new_fn   = visit_function(fn, has_args, ref);
            first_pass_info info;
            first_pass(new_fn, args, expected_type, ref, info);
            candidates.emplace_back(new_fn, snapshot(*this), info);
        } catch (elaborator_exception & ex) {
            error_msgs.push_back(ex);
        } catch (exception & ex) {
            error_msgs.push_back(elaborator_exception(ref, format(ex.what())));
        }
    }

    if (candidates.empty()) {
        try {
            /* Failed to disambiguate using expected type, switch to basic */
            S.restore(*this);
            return visit_overloaded_app_core(fns, args, some_expr(expected_type), ref);
        } catch (elaborator_exception & ex) {
            auto pp_fn = mk_pp_ctx();
            format msg = format("switched to basic overload resolution where arguments are elaborated without "
                                "any information about the expected type, because failed to elaborate all candidates "
                                "using the expected type");
            msg += pp_indent(pp_fn, expected_type);
            msg += line() + format("this can happen because, for example, coercions were not considered in the process");
            msg += line() + mk_no_overload_applicable_msg(fns, error_msgs);
            throw nested_elaborator_exception(ref, ex, msg);
        }
    }

    if (candidates.size() == 1) {
        // Restore successful state
        auto & c = candidates[0];
        expr fn = std::get<0>(c);
        std::get<1>(c).restore(*this);
        first_pass_info & info = std::get<2>(c);
        try {
            return second_pass(fn, args, ref, info);
        } catch (elaborator_exception & ex) {
            auto pp_fn = mk_pp_ctx();
            format msg = format("overload was disambiguated using expected type");
            msg += line() + pp_overloads(pp_fn, fns);
            msg += line() + format("the only applicable one seemed to be: ") + pp_overload(pp_fn, fn);
            msg += line();

            for (auto const & error_msg : error_msgs) {
                msg += line() + error_msg.pp();
            }

            throw nested_elaborator_exception(ref, ex, msg);
        }
    }

    try {
        /* Failed to disambiguate using expected type, switch to basic */
        S.restore(*this);
        return visit_overloaded_app_core(fns, args, some_expr(expected_type), ref);
    } catch (elaborator_exception & ex) {
        auto pp_fn = mk_pp_ctx();
        format msg = format("switched to basic overload resolution where arguments are elaborated without "
                            "any information about the expected type because it failed to disambiguate "
                            "overload using the expected type");
        msg += pp_indent(pp_fn, expected_type);
        msg += line() + format("the following overloaded terms were applicable");
        for (auto const & c : candidates)
            msg += pp_indent(pp_fn, std::get<0>(c));
        throw nested_elaborator_exception(ref, ex, msg);
    }
}

expr elaborator::visit_overloaded_app(buffer<expr> const & fns, buffer<expr> const & args,
                                      optional<expr> const & expected_type, expr const & ref) {
    trace_elab_detail(tout() << "overloaded application at " << pos_string_for(ref);
                      auto pp_fn = mk_pp_ctx();
                      tout() << pp_overloads(pp_fn, fns) << "\n";);
    if (expected_type) {
        return visit_overloaded_app_with_expected(fns, args, *expected_type, ref);
    } else {
        try {
            return visit_overloaded_app_core(fns, args, expected_type, ref);
        } catch (elaborator_exception & ex) {
            format msg = format("switched to basic overload resolution where arguments are elaborated without "
                                "any information about the expected type because expected type was not available");
            throw nested_elaborator_exception(ref, ex, msg);
        }
    }
}

expr elaborator::visit_no_confusion_app(expr const & fn, buffer<expr> const & args, optional<expr> const & expected_type,
                                        expr const & ref) {
    name fn_name = const_name(fn);
    if (!expected_type) {
        throw elaborator_exception(ref, format("invalid '") + format(fn_name) + format ("' application, ") +
                                   format("elaborator has special support for no_confusion ") +
                                   format("but the expected type must be known"));
    }
    if (args.empty()) {
        throw elaborator_exception(ref,
                                   format("invalid occurrence of function '") + format(fn_name) +
                                   format ("', it must be applied to at least one argument (possible solution: use '@')"));
    }
    /* I.no_confusion functions have a type of the form

       Pi (params) (indices) (C : Type) (lhs rhs : I params indices) (H : lhs = rhs),
          I.no_confusion_type params indices C lhs rhs

       The type (I.no_confusion_type params indices C lhs rhs) is C if lhs and rhs are distinct constructors,
       and (Pi Hs, C) if they are the same constructor where Hs is a sequence of equalities.

       (C : Type) is the expected type.

       To make the elaborator more effective, we first elaborate the first explicit argument (i.e., args[0]) and obtain Heq,
       and create the fake pre-term

       (I.no_confusion _ ... _ (as-is expected_type) _ _ (as-is Heq) args[1] ... args[n-1])

       Then, we elaborate this new fake pre-term.
    */
    expr Heq      = strict_visit(args[0], none_expr());
    name I_name   = fn_name.get_prefix();
    unsigned nparams  = *inductive::get_num_params(m_env, I_name);
    unsigned nindices = *inductive::get_num_indices(m_env, I_name);
    buffer<expr> new_args;
    for (unsigned i = 0; i < nparams + nindices; i++) {
        new_args.push_back(copy_tag(ref, mk_expr_placeholder()));
    }
    new_args.push_back(copy_tag(ref, mk_as_is(*expected_type)));
    new_args.push_back(copy_tag(ref, mk_expr_placeholder())); // lhs
    new_args.push_back(copy_tag(ref, mk_expr_placeholder())); // rhs
    new_args.push_back(copy_tag(args[0], mk_as_is(Heq)));
    for (unsigned i = 1; i < args.size(); i++)
        new_args.push_back(args[i]);
    return visit_base_app_core(fn, arg_mask::AllExplicit, new_args, false, expected_type, ref);
}

expr elaborator::visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type,
                                expr const & ref) {
    arg_mask amask = arg_mask::Default;
    if (is_explicit(fn)) {
        fn   = get_explicit_arg(fn);
        amask = arg_mask::AllExplicit;
    } else if (is_partial_explicit(fn)) {
        fn   = get_partial_explicit_arg(fn);
        amask = arg_mask::InstHoExplicit;
    }

    bool has_args = !args.empty();

    while (is_annotation(fn))
        fn = get_annotation_arg(fn);

    if (is_choice(fn)) {
        buffer<expr> fns;
        if (amask != arg_mask::Default)
            throw elaborator_exception(ref, "invalid explicit annotation, symbol is overloaded "
                                       "(solution: use fully qualified names)");
        for (unsigned i = 0; i < get_num_choices(fn); i++) {
            expr const & fn_i = get_choice(fn, i);
            fns.push_back(fn_i);
        }
        validate_overloads(fns, ref);
        return visit_overloaded_app(fns, args, expected_type, ref);
    } else {
        expr new_fn = visit_function(fn, has_args, ref);
        /* Check if we should use a custom elaboration procedure for this application. */
        if (is_constant(new_fn) && amask == arg_mask::Default) {
            if (auto info = use_elim_elab(const_name(new_fn))) {
                if (args.size() >= info->m_nexplicit) {
                    return visit_elim_app(new_fn, *info, args, expected_type, ref);
                } else {
                    try {
                        return visit_base_app(new_fn, amask, args, expected_type, ref);
                    } catch (elaborator_exception & ex) {
                        throw nested_elaborator_exception(ref, ex,
                                                          format("'eliminator' elaboration was not used for '") +
                                                          pp(fn) + format("' because it is not fully applied, #") +
                                                          format(info->m_nexplicit) + format(" explicit arguments expected"));
                    }
                }
            } else if (is_no_confusion(m_env, const_name(new_fn))) {
                return visit_no_confusion_app(new_fn, args, expected_type, ref);
            } else {
                try {
                    return visit_base_app(new_fn, amask, args, expected_type, ref);
                } catch (elaborator_exception & ex) {
                    if (auto error_msg = m_elim_failure_info.find(const_name(new_fn))) {
                        throw nested_elaborator_exception(ref, ex, *error_msg);
                    } else {
                        throw;
                    }
                }
            }
        }
        return visit_base_app(new_fn, amask, args, expected_type, ref);
    }
}

expr elaborator::visit_local(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type, e);
}

expr elaborator::visit_constant(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type, e);
}

expr elaborator::visit_scope_trace(expr const & e, optional<expr> const & expected_type) {
    buffer<expr> new_args;
    auto pip = get_pos_info_provider();
    unsigned line = 0, col = 0;
    if (pip) {
        pos_info pos = pip->get_pos_info_or_some(e);
        line         = pos.first;
        col          = pos.second;
    }
    new_args.push_back(copy_tag(e, mk_expr_placeholder()));
    new_args.push_back(copy_tag(e, mk_prenum(mpz(line))));
    new_args.push_back(copy_tag(e, mk_prenum(mpz(col))));
    new_args.push_back(app_arg(e));
    return visit(mk_app(copy_tag(e, mk_explicit(app_fn(e))), new_args.size(), new_args.data()), expected_type);
}

expr elaborator::visit_app(expr const & e, optional<expr> const & expected_type) {
    if (is_app_of(e, get_scope_trace_name(), 1))
        return visit_scope_trace(e, expected_type);
    expr const & ref = e;
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_equations(fn)) {
        return visit_convoy(e, expected_type);
    } else if (is_constant(fn, get_tactic_eval_expr_name()) && args.size() == 2) {
        buffer<expr> new_args;
        expr ref_arg = get_ref_for_child(args[0], ref);
        expr A = ensure_type(visit(args[0], none_expr()), ref_arg);
        if (has_local(A))
            throw elaborator_exception(e, "invalid eval_expr, type must be a closed expression");
        new_args.push_back(mk_as_is(A));
        /* Remark: the code generator will replace the following argument */
        new_args.push_back(copy_tag(e, mk_quote(mk_Prop())));
        new_args.push_back(args[1]);
        return visit(copy_tag(e, mk_app(mk_explicit(fn), new_args)), expected_type);
    } else {
        return visit_app_core(fn, args, expected_type, e);
    }
}

expr elaborator::visit_by(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_by(e));
    expr tac = strict_visit(get_by_arg(e), none_expr());
    expr const & ref = e;
    expr mvar        = mk_metavar(expected_type, ref);
    m_tactics = cons(mk_pair(mvar, tac), m_tactics);
    trace_elab(tout() << "tactic for ?m_" << get_metavar_decl_ref_suffix(mvar) << " at " <<
               pos_string_for(mvar) << "\n" << tac << "\n";);
    return mvar;
}

expr elaborator::visit_anonymous_constructor(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_anonymous_constructor(e));
    buffer<expr> args;
    expr const & c = get_app_args(get_anonymous_constructor_arg(e), args);
    if (!expected_type)
        throw elaborator_exception(e, "invalid constructor ⟨...⟩, expected type must be known");
    expr I = get_app_fn(m_ctx.relaxed_whnf(instantiate_mvars(*expected_type)));
    if (!is_constant(I))
        throw elaborator_exception(e, format("invalid constructor ⟨...⟩, expected type is not an inductive type") +
                                   pp_indent(*expected_type));
    name I_name = const_name(I);
    if (is_private(m_env, I_name))
        throw elaborator_exception(e, "invalid constructor ⟨...⟩, type is a private inductive datatype");
    if (!inductive::is_inductive_decl(m_env, I_name))
        throw elaborator_exception(e, sstream() << "invalid constructor ⟨...⟩, '" << I_name << "' is not an inductive type");
    buffer<name> c_names;
    get_intro_rule_names(m_env, I_name, c_names);
    if (c_names.size() != 1)
        throw elaborator_exception(e, sstream() << "invalid constructor ⟨...⟩, '" << I_name << "' must have only one constructor");
    expr type = m_env.get(c_names[0]).get_type();
    unsigned num_explicit = 0;
    while (is_pi(type)) {
        if (is_explicit(binding_info(type)))
            num_explicit++;
        type = binding_body(type);
    }
    if (num_explicit > 1 && args.size() > num_explicit) {
        unsigned num_extra = args.size() - num_explicit;
        expr rest = copy_tag(e, mk_app(c, num_extra + 1, args.data() + num_explicit - 1));
        rest = copy_tag(e, mk_anonymous_constructor(rest));
        args.shrink(num_explicit);
        args.back() = rest;
    }
    expr new_e = copy_tag(e, mk_app(mk_constant(c_names[0]), args));
    return visit(new_e, expected_type);
}

static expr get_equations_fn_type(expr const & eqns) {
    buffer<expr> eqs;
    to_equations(eqns, eqs);
    lean_assert(!eqs.empty());
    lean_assert(is_lambda(eqs[0]));
    return binding_domain(eqs[0]);
}

/** \brief Similar to instantiate_rev, but assumes that subst contains only local constants.
    When replacing a variable with a local, we copy the local constant and inherit the tag
    associated with the variable. This is a trick for preserving position information. */
static expr instantiate_rev_locals(expr const & a, unsigned n, expr const * subst) {
    if (closed(a))
        return a;
    auto fn = [=](expr const & m, unsigned offset) -> optional<expr> {
        if (offset >= get_free_var_range(m))
            return some_expr(m); // expression m does not contain free variables with idx >= offset
        if (is_var(m)) {
            unsigned vidx = var_idx(m);
            if (vidx >= offset) {
                unsigned h = offset + n;
                if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                    expr local = subst[n - (vidx - offset) - 1];
                    lean_assert(is_local(local));
                    return some_expr(copy_tag(m, copy(local)));
                } else {
                    return some_expr(copy_tag(m, mk_var(vidx - n)));
                }
            }
        }
        return none_expr();
    };
    return replace(a, fn);
}

static expr instantiate_rev_locals(expr const & e, type_context::tmp_locals const & locals) {
    return instantiate_rev_locals(e, locals.as_buffer().size(), locals.as_buffer().data());
}

static expr update_equations_fn_type(expr const & eqns, expr const & new_fn_type) {
    expr fn_type = mk_as_is(new_fn_type);
    buffer<expr> eqs;
    to_equations(eqns, eqs);
    for (expr & eq : eqs) {
        lean_assert(is_lambda(eq));
        eq = update_binding(eq, fn_type, binding_body(eq));
    }
    return update_equations(eqns, eqs);
}

expr elaborator::visit_convoy(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_app(e));
    lean_assert(is_equations(get_app_fn(e)));
    expr const & ref = e;
    buffer<expr> args, new_args;
    expr const & eqns = get_app_args(e, args);
    lean_assert(equations_num_fns(eqns) == 1);
    lean_assert(equations_size(eqns) > 0);
    expr fn_type = get_equations_fn_type(eqns);
    expr new_fn_type;
    if (is_placeholder(fn_type)) {
        /* User did not provide the type for the match,
           we try to infer one using expected_type and the type of the arguments */
        if (!expected_type)
            throw elaborator_exception(ref, "invalid match/convoy expression, expected type is not known");
        for (unsigned i = 0; i < args.size(); i++)
            new_args.push_back(visit(args[i], none_expr()));
        synthesize();
        new_fn_type = instantiate_mvars(*expected_type);
        unsigned i = args.size();
        while (i > 0) {
            --i;
            expr new_arg      = instantiate_mvars(new_args[i]);
            expr new_arg_type = instantiate_mvars(infer_type(new_arg));
            new_fn_type       = ::lean::mk_pi("_a", new_arg_type, kabstract(m_ctx, new_fn_type, new_arg));
        }
    } else {
        // User provided some typing information for the match
        type_context::tmp_locals locals(m_ctx);
        expr it = fn_type;
        for (unsigned i = 0; i < args.size(); i++) {
            if (!is_pi(it))
                throw elaborator_exception(it, "type expected in match-expression");
            expr d        = instantiate_rev_locals(binding_domain(it), locals);
            expr new_d    = visit(d, none_expr());
            expr ref_d    = get_ref_for_child(binding_domain(it), it);
            new_d         = ensure_type(new_d, ref_d);
            expr expected = replace_locals(new_d, locals.as_buffer(), new_args);
            expr new_arg  = visit(args[i], some_expr(expected));
            new_arg       = enforce_type(new_arg, expected, "type mismatch in match expression", args[i]);
            locals.push_local(binding_name(it), new_d, binding_info(it));
            it            = binding_body(it);
            new_args.push_back(new_arg);
        }
        if (is_placeholder(it)) {
            synthesize();
            if (!expected_type)
                throw elaborator_exception(ref, "invalid match/convoy expression, expected type is not known");
            new_fn_type = instantiate_mvars(*expected_type);
            unsigned i = args.size();
            while (i > 0) {
                --i;
                new_args[i]  = instantiate_mvars(new_args[i]);
                new_fn_type  = instantiate(kabstract(m_ctx, new_fn_type, new_args[i]), locals.as_buffer()[i]);
            }
            new_fn_type = locals.mk_pi(new_fn_type);
        } else {
            expr b      = instantiate_rev_locals(it, locals);
            expr new_b  = visit(b, none_expr());
            synthesize();
            new_fn_type = locals.mk_pi(instantiate_mvars(new_b));
        }
    }
    new_fn_type = instantiate_mvars(new_fn_type);
    if (has_expr_metavar(new_fn_type)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(ref, format("invalid match/convoy expression, type contains meta-variables") +
                                   pp_indent(pp_fn, new_fn_type));
    }
    trace_elab(tout() << "match/convoy function type: " << new_fn_type << "\n";);
    expr new_eqns = visit_equations(update_equations_fn_type(eqns, new_fn_type));
    expr fn       = get_equations_result(new_eqns, 0);
    return mk_app(fn, new_args);
}

/** \brief Given two binding expressions \c source and \c target
    s.t. they have at least \c num binders, replace the first \c num binders of \c target with \c source.
    The binder types are wrapped with \c mk_as_is to make sure the elaborator will not process
    them again. */
static expr copy_domain(unsigned num, expr const & source, expr const & target) {
    if (num == 0) {
        return target;
    } else {
        lean_assert(is_binding(source) && is_binding(target));
        return update_binding(source, mk_as_is(binding_domain(source)),
                              copy_domain(num-1, binding_body(source), binding_body(target)));
    }
}

static void check_equations_arity(buffer<expr> const & eqns) {
    buffer<optional<unsigned>> fidx2arity;
    for (expr eqn : eqns) {
        unsigned nbinders = 0;
        expr curr = eqn;
        while (is_lambda(eqn)) {
            nbinders++;
            eqn = binding_body(eqn);
        }
        if (is_equation(eqn)) {
            expr const & lhs = equation_lhs(eqn);
            expr const & fn  = get_app_fn(lhs);
            unsigned arity   = get_app_num_args(lhs);
            if (!is_var(fn) || var_idx(fn) >= nbinders)
                throw elaborator_exception(eqn, "ill-formed match/equations expression");
            unsigned fidx    = nbinders - var_idx(fn) - 1;
            if (fidx >= fidx2arity.size())
                fidx2arity.resize(fidx+1, optional<unsigned>());
            if (auto r = fidx2arity[fidx]) {
                if (*r != arity) {
                    throw elaborator_exception(eqn, "invalid match/equations expression, "
                                               "each case must have the same number of patterns");
                }
            } else {
                fidx2arity[fidx] = arity;
            }
        } else if (is_no_equation(eqn)) {
            /* do nothing */
        } else {
            throw elaborator_exception(curr, "ill-formed match/equations expression");
        }
    }
}

expr elaborator::visit_equations(expr const & e) {
    expr const & ref = e;
    buffer<expr> eqs;
    buffer<expr> new_eqs;
    optional<expr> new_R;
    optional<expr> new_Rwf;
    flet<list<expr_pair>> save_stack(m_inaccessible_stack, m_inaccessible_stack);
    list<expr_pair> saved_inaccessible_stack = m_inaccessible_stack;
    equations_header const & header = get_equations_header(e);
    unsigned num_fns = header.m_num_fns;
    to_equations(e, eqs);
    lean_assert(!eqs.empty());

    if (is_wf_equations(e)) {
        new_R   = visit(equations_wf_rel(e), none_expr());
        new_Rwf = visit(equations_wf_proof(e), none_expr());
        expr wf = mk_app(m_ctx, get_well_founded_name(), *new_R);
        new_Rwf = enforce_type(*new_Rwf, wf, "invalid well-founded relation proof", ref);
    }

    optional<expr> first_eq;
    for (expr const & eq : eqs) {
        expr new_eq;
        buffer<expr> fns_locals;
        fun_to_telescope(eq, fns_locals, optional<binder_info>());
        list<expr> locals = to_list(fns_locals.begin() + num_fns, fns_locals.end());
        if (first_eq) {
            // Replace first num_fns domains of eq with the ones in first_eq.
            // This is a trick/hack to ensure the fns in each equation have
            // the same elaborated type.
            new_eq   = copy_tag(eq, visit(copy_domain(num_fns, *first_eq, eq), none_expr()));
        } else {
            new_eq   = copy_tag(eq, visit(eq, none_expr()));
            first_eq = new_eq;
        }
        new_eqs.push_back(new_eq);
    }
    check_equations_arity(new_eqs);
    synthesize();
    check_inaccessible(saved_inaccessible_stack);
    expr new_e;
    if (new_R) {
        new_e = copy_tag(e, mk_equations(header, new_eqs.size(), new_eqs.data(), *new_R, *new_Rwf));
    } else {
        new_e = copy_tag(e, mk_equations(header, new_eqs.size(), new_eqs.data()));
    }
    new_e = instantiate_mvars(new_e);
    ensure_no_unassigned_metavars(new_e);
    metavar_context mctx = m_ctx.mctx();
    expr r = compile_equations(m_env, m_opts, mctx, m_ctx.lctx(), new_e);
    m_ctx.set_env(m_env);
    m_ctx.set_mctx(mctx);
    return r;
}

void elaborator::check_pattern_inaccessible_annotations(expr const & p) {
    if (is_app(p)) {
        buffer<expr> args;
        expr const & c = get_app_args(p, args);
        if (is_constant(c)) {
            if (optional<name> I_name = inductive::is_intro_rule(m_env, const_name(c))) {
                /* Make sure the inductive datatype parameters are marked as inaccessible */
                unsigned nparams = *inductive::get_num_params(m_env, *I_name);
                for (unsigned i = 0; i < nparams && i < args.size(); i++) {
                    if (!is_inaccessible(args[i])) {
                        throw elaborator_exception(c, "invalid pattern, in a constructor application, "
                                                   "the parameters of the inductive datatype must be marked as inaccessible");
                    }
                }
            }
            // TODO(Leo): we should add a similar check for derived constructors.
            // What about constants marked as pattern? Example: @add
            // Option: check again at elim_match. The error message will not be nice,
            // but it is better than nothing.
        }
        for (expr const & a : args) {
            check_pattern_inaccessible_annotations(a);
        }
    }
}

void elaborator::check_inaccessible_annotations(expr const & lhs) {
    buffer<expr> patterns;
    get_app_args(lhs, patterns);
    for (expr const & p : patterns) {
        check_pattern_inaccessible_annotations(p);
    }
}

expr elaborator::visit_equation(expr const & eq) {
    expr const & lhs = equation_lhs(eq);
    expr const & rhs = equation_rhs(eq);
    expr lhs_fn = get_app_fn(lhs);
    if (is_explicit_or_partial_explicit(lhs_fn))
        lhs_fn = get_explicit_or_partial_explicit_arg(lhs_fn);
    if (!is_local(lhs_fn))
        throw exception("ill-formed equation");
    expr new_lhs;
    {
        flet<bool> set(m_in_pattern, true);
        new_lhs = visit(lhs, none_expr());
        check_inaccessible_annotations(new_lhs);
        synthesize_no_tactics();
    }
    expr new_lhs_type = instantiate_mvars(infer_type(new_lhs));
    expr new_rhs      = visit(rhs, some_expr(new_lhs_type));
    new_rhs = enforce_type(new_rhs, new_lhs_type, "equation type mismatch", eq);
    return copy_tag(eq, mk_equation(new_lhs, new_rhs));
}

expr elaborator::visit_inaccessible(expr const & e, optional<expr> const & expected_type) {
    if (!m_in_pattern)
        throw elaborator_exception(e, "invalid occurrence of 'inaccessible' annotation, "
                                   "it must only occur in patterns");
    expr const & ref = e;
    expr m = mk_metavar(expected_type, ref);
    expr a = get_annotation_arg(e);
    expr new_a;
    {
        flet<bool> set(m_in_pattern, false);
        new_a = visit(a, expected_type);
    }
    m_inaccessible_stack = cons(mk_pair(m, new_a), m_inaccessible_stack);
    return copy_tag(e, mk_inaccessible(m));
}

name elaborator::field_to_decl(expr const & e, expr const & s, expr const & s_type) {
    expr I      = get_app_fn(s_type);
    if (!is_constant(I)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(e, format("invalid '~>' notation, type is not of the form (C ...) where C is a constant") +
                                   pp_indent(pp_fn, s) +
                                   line() + format("has type") +
                                   pp_indent(pp_fn, s_type));
    }
    if (is_anonymous_field_notation(e)) {
        if (!is_structure(m_env, const_name(I))) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(e, format("invalid projection, structure expected") +
                                       pp_indent(pp_fn, s) +
                                       line() + format("has type") +
                                       pp_indent(pp_fn, s_type));
        }
        buffer<name> fnames;
        get_structure_fields(m_env, const_name(I), fnames);
        unsigned fidx = get_field_notation_field_idx(e);
        lean_assert(fidx > 0);
        if (fidx > fnames.size()) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(e, format("invalid projection, structure has only ") +
                                       format(fnames.size()) + format(" field(s)") +
                                       pp_indent(pp_fn, s) +
                                       line() + format("which has type") +
                                       pp_indent(pp_fn, s_type));
        }
        return fnames[fidx-1];
    } else {
        name fname  = get_field_notation_field_name(e);
        name full_fname = const_name(I) + fname;
        if (!m_env.find(full_fname)) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(e, format("invalid '~>' notation, '") + format(fname) + format("'") +
                                       format(" is not a valid \"field\" because environment does not contain ") +
                                       format("'") + format(full_fname) + format("'") +
                                       pp_indent(pp_fn, s) +
                                       line() + format("which has type") +
                                       pp_indent(pp_fn, s_type));
        }
        return full_fname;
    }
}

expr elaborator::visit_field(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_field_notation(e));
    expr s      = visit(macro_arg(e, 0), none_expr());
    expr s_type = head_beta_reduce(instantiate_mvars(infer_type(s)));
    name full_fname;
    try {
        full_fname = field_to_decl(e, s, s_type);
    } catch (elaborator_exception & ex1) {
        /* Try again using whnf */
        expr new_s_type = whnf(s_type);
        if (new_s_type == s_type)
            throw;
        try {
            full_fname = field_to_decl(e, s, new_s_type);
        } catch (elaborator_exception & ex2) {
            throw nested_elaborator_exception(ex2.get_main_expr(), ex1, ex2.pp());
        }
    }
    expr proj  = copy_tag(e, mk_constant(full_fname));
    expr new_e = copy_tag(e, mk_app(proj, copy_tag(e, mk_as_is(s))));
    expr r = visit(new_e, expected_type);
    if (auto pos = get_field_notation_field_pos(e))
        save_identifier_info(app_fn(r), pos);
    return r;
}

expr elaborator::visit_structure_instance(expr const & e, optional<expr> const & _expected_type) {
    name S_name;
    optional<expr> src;
    buffer<name> fnames;
    buffer<expr> fvalues;
    optional<expr> expected_type;
    if (_expected_type) {
        synthesize_type_class_instances();
        expected_type = instantiate_mvars(*_expected_type);
        if (is_metavar(*expected_type))
            expected_type = none_expr();
    }
    get_structure_instance_info(e, S_name, src, fnames, fvalues);
    if (!S_name.is_anonymous() && !is_structure(env(), S_name))
        throw elaborator_exception(e, sstream() << "invalid structure instance, '" <<
                                   S_name << "' is not the name of a structure type");
    lean_assert(fnames.size() == fvalues.size());
    name src_S_name;
    unsigned src_S_nparams = 0;
    if (src) {
        src = visit(*src, none_expr());
        synthesize_type_class_instances();
        expr type  = instantiate_mvars(whnf(infer_type(*src)));
        expr src_S = get_app_fn(type);
        if (!is_constant(src_S) || !is_structure(m_env, const_name(src_S))) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(e,
                                       format("invalid structure update { src with ...}, source is not a structure") +
                                       pp_indent(pp_fn, *src) +
                                       line() + format("which has type") +
                                       pp_indent(pp_fn, type));
        }
        src_S_name    = const_name(src_S);
        src_S_nparams = *inductive::get_num_params(m_env, src_S_name);
    }
    if (S_name.is_anonymous()) {
        if (expected_type) {
            expr type = whnf(*expected_type);
            expr S    = get_app_fn(type);
            if (!is_constant(S) || !is_structure(m_env, const_name(S))) {
                auto pp_fn = mk_pp_ctx();
                throw elaborator_exception(e,
                                           format("invalid structure value {...}, expected type is known, "
                                                  "but it is not a structure") + pp_indent(pp_fn, *expected_type));
            }
            S_name = const_name(S);
        } else if (src) {
            S_name = src_S_name;
        } else {
            throw elaborator_exception(e, "invalid structure value {...}, expected type is not known"
                                       "(solution: use qualified structure instance { struct_id . ... }");
        }
    }
    unsigned nparams = *inductive::get_num_params(m_env, S_name);
    buffer<bool> used;
    used.resize(fnames.size(), false);
    if (src) src = copy_tag(*src, mk_as_is(*src));

    buffer<name> c_names;
    get_intro_rule_names(m_env, S_name, c_names);
    lean_assert(c_names.size() == 1);
    expr c = copy_tag(e, mk_constant(c_names[0]));
    expr c_type = m_env.get(c_names[0]).get_type();
    unsigned i = 0;
    name_map<expr> field2value;
    while (is_pi(c_type)) {
        if (i < nparams) {
            if (is_explicit(binding_info(c_type))) {
                throw elaborator_exception(e, sstream() << "invalid structure value {...}, structure parameter '" <<
                                           binding_name(c_type) << "' is explicit in the structure constructor '" <<
                                           c_names[0] << "'");
            }
        } else {
            name S_fname = binding_name(c_type);
            if (is_explicit(binding_info(c_type))) {
                unsigned j = 0;
                for (; j < fnames.size(); j++) {
                    if (S_fname == fnames[j]) {
                        used[j] = true;
                        field2value.insert(S_fname, fvalues[j]);
                        c = copy_tag(e, mk_app(c, fvalues[j]));
                        break;
                    }
                }
                if (j == fnames.size()) {
                    if (src) {
                        name new_fname = src_S_name + S_fname;
                        expr f = copy_tag(e, mk_constant(new_fname));
                        f = copy_tag(e, mk_explicit(f));
                        for (unsigned i = 0; i < src_S_nparams; i++)
                            f = copy_tag(e, mk_app(f, copy_tag(e, mk_expr_placeholder())));
                        f = copy_tag(e, mk_app(f, *src));
                        try {
                            f = visit(f, none_expr());
                        } catch (exception & ex) {
                            throw nested_exception(some_expr(e),
                                                   sstream() << "invalid structure update { src with ... }, field '"
                                                   << S_fname << "'"
                                                   << " was not provided, nor it was found in the source", ex);
                        }
                        f = copy_tag(e, mk_as_is(f));
                        field2value.insert(S_fname, f);
                        c = copy_tag(e, mk_app(c, f));
                    } else {
                        name full_S_fname = S_name + S_fname;
                        if (optional<name> default_value_fn = has_default_value(m_env, full_S_fname)) {
                            expr value = mk_field_default_value(m_env, full_S_fname, [&](name const & fname) {
                                    if (auto v = field2value.find(fname))
                                        return some_expr(*v);
                                    else
                                        return none_expr();
                                });
                            field2value.insert(S_fname, value);
                            c = copy_tag(e, mk_app(c, value));
                        } else {
                            throw elaborator_exception(e, sstream() << "invalid structure value { ... }, field '" <<
                                                       S_fname << "' was not provided");
                        }
                    }
                }
            } else {
                /* Implicit field */
                if (std::find(fnames.begin(), fnames.end(), S_fname) != fnames.end()) {
                    throw elaborator_exception(e, sstream() << "invalid structure value {...}, field '"
                                               << S_fname << "' is implicit and must not be provided");
                }
            }
        }
        c_type = binding_body(c_type);
        i++;
    }
    for (unsigned i = 0; i < fnames.size(); i++) {
        if (!used[i]) {
            throw elaborator_exception(e, sstream() << "invalid structure value { ... }, '" << fnames[i] << "'" <<
                                       " is not a field of structure '" << S_name << "'");
        }
    }
    return visit(c, expected_type);
}

expr elaborator::visit_macro(expr const & e, optional<expr> const & expected_type, bool is_app_fn) {
    if (is_as_is(e)) {
        return get_as_is_arg(e);
    } else if (is_anonymous_constructor(e)) {
        if (is_app_fn)
            throw elaborator_exception(e, "invalid constructor ⟨...⟩, function expected");
        return visit_anonymous_constructor(e, expected_type);
    } else if (is_prenum(e)) {
        return visit_prenum(e, expected_type);
    } else if (is_typed_expr(e)) {
        return visit_typed_expr(e);
    } else if (is_choice(e) || is_explicit(e) || is_partial_explicit(e)) {
        return visit_app_core(e, buffer<expr>(), expected_type, e);
    } else if (is_by(e)) {
        return visit_by(e, expected_type);
    } else if (is_equations(e)) {
        lean_assert(!is_app_fn); // visit_convoy is used in this case
        return visit_equations(e);
    } else if (is_equation(e)) {
        lean_assert(!is_app_fn);
        return visit_equation(e);
    } else if (is_field_notation(e)) {
        return visit_field(e, expected_type);
    } else if (is_inaccessible(e)) {
        if (is_app_fn)
            throw elaborator_exception(e, "invalid inaccessible term, function expected");
        return visit_inaccessible(e, expected_type);
    } else if (is_as_atomic(e)) {
        /* ignore annotation */
        expr new_e = visit(get_as_atomic_arg(e), none_expr());
        if (is_app_fn)
            return new_e;
        /* If the as_atomic macro is not the the function in a function application, then we need to consume
           implicit arguments. */
        return visit_base_app_core(new_e, arg_mask::Default, buffer<expr>(), true, expected_type, e);
    } else if (is_structure_instance(e)) {
        return visit_structure_instance(e, expected_type);
    } else if (is_annotation(e)) {
        expr r = visit(get_annotation_arg(e), expected_type);
        return update_macro(e, 1, &r);
    } else {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(visit(macro_arg(e, i), none_expr()));
        return update_macro(e, args.size(), args.data());
    }
}

/* If the instance fingerprint has been set, then make sure `type` is not a local instance.
   Then, add a new local declaration to locals. */
expr elaborator::push_local(type_context::tmp_locals & locals,
                            name const & n, expr const & type, binder_info const & binfo, expr const & /* ref */) {
#if 0 // TODO(Leo): the following check is too restrictive
    if (m_ctx.lctx().get_instance_fingerprint() &&
        m_ctx.is_class(type)) {
        throw elaborator_exception(ref, "invalid occurrence of local instance, it must be a declaration parameter");
    }
#endif
    return locals.push_local(n, type, binfo);
}

/* See method above */
expr elaborator::push_let(type_context::tmp_locals & locals,
                          name const & n, expr const & type, expr const & value, expr const & /* ref */) {
#if 0 // TODO(Leo): the following check is too restrictive
    if (m_ctx.lctx().get_instance_fingerprint() &&
        m_ctx.is_class(type)) {
        throw elaborator_exception(ref, "invalid occurrence of local instance, it must be a declaration parameter");
    }
#endif
    return locals.push_let(n, type, value);
}

expr elaborator::visit_lambda(expr const & e, optional<expr> const & expected_type) {
    type_context::tmp_locals locals(m_ctx);
    expr it  = e;
    expr ex;
    bool has_expected;
    if (expected_type) {
        ex = instantiate_mvars(*expected_type);
        has_expected = true;
    } else {
        has_expected = false;
    }
    while (is_lambda(it)) {
        if (has_expected) {
            ex = try_to_pi(ex);
            if (!is_pi(ex))
                has_expected = false;
        }
        expr d     = instantiate_rev_locals(binding_domain(it), locals);
        expr new_d = visit(d, none_expr());
        if (has_expected) {
            expr ex_d = binding_domain(ex);
            try_is_def_eq(new_d, ex_d);
        }
        expr ref_d = get_ref_for_child(binding_domain(it), it);
        new_d      = ensure_type(new_d, ref_d);
        expr l     = copy_tag(binding_domain(it), push_local(locals, binding_name(it), new_d, binding_info(it), ref_d));
        save_identifier_info(l);
        it = binding_body(it);
        if (has_expected) {
            lean_assert(is_pi(ex));
            ex = instantiate(binding_body(ex), l);
        }
    }
    expr b = instantiate_rev_locals(it, locals);
    expr new_b;
    if (has_expected) {
        new_b = visit(b, some_expr(ex));
    } else {
        new_b = visit(b, none_expr());
    }
    synthesize();
    expr r = locals.mk_lambda(new_b);
    return r;
}

expr elaborator::visit_pi(expr const & e) {
    type_context::tmp_locals locals(m_ctx);
    expr it  = e;
    expr parent_it = e;
    while (is_pi(it)) {
        expr d     = instantiate_rev_locals(binding_domain(it), locals);
        expr new_d = visit(d, none_expr());
        expr ref_d = get_ref_for_child(binding_domain(it), it);
        new_d      = ensure_type(new_d, ref_d);
        expr ref   = binding_domain(it);
        expr l     = copy_tag(binding_domain(it), push_local(locals, binding_name(it), new_d, binding_info(it), ref));
        save_identifier_info(l);
        parent_it  = it;
        it         = binding_body(it);
    }
    expr b     = instantiate_rev_locals(it, locals);
    expr new_b = visit(b, none_expr());
    expr ref_b = get_ref_for_child(it, parent_it);
    new_b      = ensure_type(new_b, ref_b);
    synthesize();
    expr r = locals.mk_pi(new_b);
    return r;
}

expr elaborator::visit_let(expr const & e, optional<expr> const & expected_type) {
    expr ref = e;
    expr new_type  = visit(let_type(e), none_expr());
    synthesize_no_tactics();
    expr new_value = visit(let_value(e), some_expr(new_type));
    expr ref_value = get_ref_for_child(let_value(e), ref);
    new_value      = enforce_type(new_value, new_type, "invalid let-expression", ref_value);
    synthesize();
    new_type       = instantiate_mvars(new_type);
    new_value      = instantiate_mvars(new_value);
    ensure_no_unassigned_metavars(new_value);
    type_context::tmp_locals locals(m_ctx);
    expr l = copy_tag(let_type(e), push_let(locals, let_name(e), new_type, new_value, ref));
    save_identifier_info(l);
    expr body      = instantiate_rev_locals(let_body(e), locals);
    expr new_body  = visit(body, expected_type);
    expr new_e     = locals.mk_lambda(new_body);
    return new_e;
}

expr elaborator::visit_placeholder(expr const & e, optional<expr> const & expected_type) {
    expr const & ref = e;
    return mk_metavar(expected_type, ref);
}

static bool is_have_expr(expr const & e) {
    return is_app(e) && is_have_annotation(app_fn(e)) && is_lambda(get_annotation_arg(app_fn(e)));
}

expr elaborator::strict_visit(expr const & e, optional<expr> const & expected_type) {
    expr r = visit(e, expected_type);
    synthesize();
    r = instantiate_mvars(r);
    ensure_no_unassigned_metavars(r);
    return r;
}

expr elaborator::visit_have_expr(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_have_expr(e));
    expr lambda     = get_annotation_arg(app_fn(e));
    expr type       = binding_domain(lambda);
    expr proof      = app_arg(e);
    expr new_type   = visit(type, none_expr());
    synthesize_no_tactics();
    new_type        = ensure_type(new_type, type);
    expr new_proof  = visit(proof, some_expr(new_type));
    new_proof       = enforce_type(new_proof, new_type, "invalid have-expression", proof);
    synthesize();
    ensure_no_unassigned_metavars(new_proof);
    type_context::tmp_locals locals(m_ctx);
    expr ref        = binding_domain(lambda);
    push_local(locals, binding_name(lambda), new_type, binding_info(lambda), ref);
    expr body       = instantiate_rev_locals(binding_body(lambda), locals);
    expr new_body   = visit(body, expected_type);
    expr new_lambda = locals.mk_lambda(new_body);
    return mk_app(mk_have_annotation(new_lambda), new_proof);
}

expr elaborator::visit_suffices_expr(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_suffices_annotation(e));
    expr body = get_annotation_arg(e);
    if (!is_app(body)) throw elaborator_exception(e, "ill-formed suffices expression");
    expr fn   = app_fn(body);
    expr rest = app_arg(body);
    if (!is_lambda(fn)) throw elaborator_exception(e, "ill-formed suffices expression");
    expr new_fn;
    expr type     = binding_domain(fn);
    expr new_type = visit(type, none_expr());
    synthesize_no_tactics();
    {
        type_context::tmp_locals locals(m_ctx);
        expr ref        = binding_domain(fn);
        push_local(locals, binding_name(fn), new_type, binding_info(fn), ref);
        expr body       = instantiate_rev_locals(binding_body(fn), locals);
        expr new_body   = visit(body, expected_type);
        synthesize();
        new_fn          = locals.mk_lambda(new_body);
    }
    expr new_rest = visit(rest, some_expr(new_type));
    new_rest      = enforce_type(new_rest, new_type, "invalid suffices-expression", rest);
    return mk_suffices_annotation(mk_app(new_fn, new_rest));
}

expr elaborator::visit_emptyc_or_emptys(expr const & e, optional<expr> const & expected_type) {
    if (!expected_type) {
        return visit(copy_tag(e, mk_constant(get_emptyc_name())), expected_type);
    } else {
        synthesize_type_class_instances();
        expr new_expected_type = instantiate_mvars(*expected_type);
        expr S = get_app_fn(new_expected_type);
        if (is_constant(S) && is_structure(m_env, const_name(S))) {
            expr empty_struct = copy_tag(e, mk_structure_instance(name(), buffer<name>(), buffer<expr>()));
            return visit(empty_struct, expected_type);
        } else {
            return visit(copy_tag(e, mk_constant(get_emptyc_name())), expected_type);
        }
    }
}

expr elaborator::visit(expr const & e, optional<expr> const & expected_type) {
    flet<unsigned> inc_depth(m_depth, m_depth+1);
    trace_elab_detail(tout() << "[" << m_depth << "] visiting\n" << e << "\n";
                      if (expected_type) tout() << "expected type:\n" << instantiate_mvars(*expected_type) << "\n";);
    if (is_placeholder(e)) {
        return visit_placeholder(e, expected_type);
    } else if (is_have_expr(e)) {
        return copy_tag(e, visit_have_expr(e, expected_type));
    } else if (is_suffices_annotation(e)) {
        return copy_tag(e, visit_suffices_expr(e, expected_type));
    } else if (is_no_info(e)) {
        flet<bool> set(m_no_info, true);
        return visit(get_annotation_arg(e), expected_type);
    } else if (is_emptyc_or_emptys(e)) {
        return visit_emptyc_or_emptys(e, expected_type);
    } else if (is_sort_wo_universe(e)) {
        return visit(get_annotation_arg(e), expected_type);
    } else {
        switch (e.kind()) {
        case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Meta:       return e;
        case expr_kind::Sort:       return copy_tag(e, visit_sort(e));
        case expr_kind::Local:      return copy_tag(e, visit_local(e, expected_type));
        case expr_kind::Constant:   return copy_tag(e, visit_constant(e, expected_type));
        case expr_kind::Macro:      return copy_tag(e, visit_macro(e, expected_type, false));
        case expr_kind::Lambda:     return copy_tag(e, visit_lambda(e, expected_type));
        case expr_kind::Pi:         return copy_tag(e, visit_pi(e));
        case expr_kind::App:        return copy_tag(e, visit_app(e, expected_type));
        case expr_kind::Let:        return copy_tag(e, visit_let(e, expected_type));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

expr elaborator::get_default_numeral_type() {
    // TODO(Leo): allow user to modify default?
    return mk_constant(get_nat_name());
}

void elaborator::synthesize_numeral_types() {
    for (expr const & A : m_numeral_types) {
        if (is_metavar(instantiate_mvars(A))) {
            if (!assign_mvar(A, get_default_numeral_type()))
                throw elaborator_exception(A, "invalid numeral, failed to force numeral to be a nat");
        }
    }
    m_numeral_types = list<expr>();
}

bool elaborator::synthesize_type_class_instance_core(expr const & mvar, expr const & inferred_inst, expr const & inst_type) {
    if (has_expr_metavar(inst_type))
        return false;
    metavar_decl mdecl = *m_ctx.mctx().get_metavar_decl(mvar);
    expr ref = mvar;
    expr synthesized_inst = mk_instance_core(mdecl.get_context(), inst_type, ref);
    if (!is_def_eq(inferred_inst, synthesized_inst)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(mvar,
                                   format("synthesized type class instance is not definitionally equal to expression "
                                          "inferred by typing rules, synthesized")
                                   + pp_indent(pp_fn, synthesized_inst)
                                   + line() + format("inferred")
                                   + pp_indent(pp_fn, inferred_inst));
    }
    return true;
}

bool elaborator::try_synthesize_type_class_instance(expr const & mvar) {
    expr inst = instantiate_mvars(mvar);
    expr inst_type = instantiate_mvars(infer_type(inst));
    return synthesize_type_class_instance_core(mvar, inst, inst_type);
}

void elaborator::synthesize_type_class_instances_step() {
    buffer<expr> to_keep;
    buffer<std::tuple<expr, expr, expr>> to_process;
    for (expr const & mvar : m_instances) {
        expr inst      = instantiate_mvars(mvar);
        expr inst_type = instantiate_mvars(infer_type(inst));
        if (has_expr_metavar(inst_type)) {
            to_keep.push_back(mvar);
        } else {
            to_process.emplace_back(mvar, inst, inst_type);
        }
    }
    if (to_process.empty())
        return;
    expr mvar, inst, inst_type;
    for (std::tuple<expr, expr, expr> const & curr : to_process) {
        std::tie(mvar, inst, inst_type) = curr;
        synthesize_type_class_instance_core(mvar, inst, inst_type);
    }
    m_instances = to_list(to_keep);
}

void elaborator::synthesize_type_class_instances() {
    while (true) {
        auto old_instances = m_instances;
        synthesize_type_class_instances_step();
        if (is_eqp(old_instances, m_instances))
            return;
    }
}

tactic_state elaborator::mk_tactic_state_for(expr const & mvar) {
    metavar_context mctx = m_ctx.mctx();
    metavar_decl mdecl   = *mctx.get_metavar_decl(mvar);
    local_context lctx   = mdecl.get_context().instantiate_mvars(mctx);
    lctx                 = erase_inaccessible_annotations(lctx);
    expr type            = mctx.instantiate_mvars(mdecl.get_type());
    type                 = erase_inaccessible_annotations(type);
    m_ctx.set_mctx(mctx);
    return ::lean::mk_tactic_state_for(m_env, m_opts, m_decl_name, mctx, lctx, type);
}

void elaborator::invoke_tactic(expr const & mvar, expr const & tactic) {
    expr const & ref     = mvar;
    tactic_state s       = mk_tactic_state_for(mvar);
    tactic_state new_s   = tactic_evaluator(m_ctx, m_info, m_opts)(s, tactic, ref);

    metavar_context mctx = new_s.mctx();
    expr val             = mctx.instantiate_mvars(new_s.main());
    if (has_expr_metavar(val)) {
        throw_unsolved_tactic_state(new_s, "tactic failed, result contains meta-variables", ref);
    }
    mctx.assign(mvar, val);
    m_env = new_s.env();
    m_ctx.set_env(m_env);
    m_ctx.set_mctx(mctx);
}

void elaborator::synthesize_using_tactics() {
    buffer<expr_pair> to_process;
    to_buffer(m_tactics, to_process);
    m_tactics = list<expr_pair>();
    for (expr_pair const & p : to_process) {
        lean_assert(is_metavar(p.first));
        invoke_tactic(p.first, p.second);
    }
}

void elaborator::synthesize_no_tactics() {
    synthesize_numeral_types();
    synthesize_type_class_instances();
}

void elaborator::synthesize() {
    synthesize_numeral_types();
    synthesize_type_class_instances();
    synthesize_using_tactics();
}

void elaborator::check_inaccessible(list<expr_pair> const & old_stack) {
    buffer<expr_pair> to_process;
    while (!is_eqp(m_inaccessible_stack, old_stack)) {
        to_process.push_back(head(m_inaccessible_stack));
        m_inaccessible_stack = tail(m_inaccessible_stack);
    }
    if (to_process.empty()) return;

    unsigned i = to_process.size();
    while (i > 0) {
        --i;
        expr_pair const & p = to_process[i];
        expr const & m = p.first;
        lean_assert(is_metavar(m));
        if (!m_ctx.is_assigned(m)) {
            throw elaborator_exception(m, "invalid use of inaccessible term, it is not fixed by other arguments");
        }
        expr v = instantiate_mvars(m);
        if (has_expr_metavar(v)) {
            throw elaborator_exception(m, format("invalid use of inaccessible term, "
                                                 "it is not completely fixed by other arguments") +
                                       pp_indent(v));
        }
        if (!is_def_eq(v, p.second)) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(m, format("invalid use of inaccessible term, the provided term is") +
                                       pp_indent(pp_fn, p.second) +
                                       line() + format("but is expected to be") +
                                       pp_indent(pp_fn, v));
        }
    }
}

void elaborator::unassigned_uvars_to_params(level const & l) {
    if (!has_meta(l)) return;
    for_each(l, [&](level const & l) {
            if (!has_meta(l)) return false;
            if (is_meta(l) && !m_ctx.is_assigned(l)) {
                name r = mk_tagged_fresh_name(*g_level_prefix);
                m_ctx.assign(l, mk_param_univ(r));
            }
            return true;
        });
}

void elaborator::unassigned_uvars_to_params(expr const & e) {
    if (!has_univ_metavar(e)) return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_univ_metavar(e)) return false;
            if (is_constant(e)) {
                for (level const & l : const_levels(e))
                    unassigned_uvars_to_params(l);
            } else if (is_sort(e)) {
                unassigned_uvars_to_params(sort_level(e));
            }
            return true;
        });
}

void elaborator::report_error(tactic_state const & s, char const * state_header,
                              char const * msg, expr const & ref) {
    auto tc = std::make_shared<type_context>(m_env, m_opts, m_ctx.mctx(), m_ctx.lctx());
    auto pip = get_pos_info_provider();
    if (!pip) return;
    message_builder out(pip, tc, m_env, get_global_ios(), pip->get_file_name(),
                        pip->get_pos_info_or_some(ref), ERROR);
    out << msg << "\n" << state_header << "\n" << mk_pair(s.pp(), m_opts);
    out.report();
}

void elaborator::ensure_no_unassigned_metavars(expr const & e) {
    if (!has_expr_metavar(e)) return;
    metavar_context mctx = m_ctx.mctx();
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e)) return false;
            if (is_metavar_decl_ref(e) && !mctx.is_assigned(e)) {
                tactic_state s = mk_tactic_state_for(e);
                report_error(s, "context:", "don't know how to synthesize placeholder", e);
                throw elaborator_exception(e, "elaborator failed");
            }
            return true;
        });
}

elaborator::snapshot::snapshot(elaborator const & e) {
    m_saved_mctx               = e.m_ctx.mctx();
    m_saved_info               = e.m_info;
    m_saved_instances          = e.m_instances;
    m_saved_numeral_types      = e.m_numeral_types;
    m_saved_tactics            = e.m_tactics;
    m_saved_inaccessible_stack = e.m_inaccessible_stack;
}

void elaborator::snapshot::restore(elaborator & e) {
    e.m_ctx.set_mctx(m_saved_mctx);
    e.m_info               = m_saved_info;
    e.m_instances          = m_saved_instances;
    e.m_numeral_types      = m_saved_numeral_types;
    e.m_tactics            = m_saved_tactics;
    e.m_inaccessible_stack = m_saved_inaccessible_stack;
}

/**
    \brief Auxiliary class for creating nice names for universe
    parameters introduced by the elaborator.

    This class also transforms remaining universe metavariables
    into parameters */
struct sanitize_param_names_fn : public replace_visitor {
    type_context &  m_ctx;
    name            m_p{"u"};
    name_set        m_L; /* All parameter names in the input expression. */
    name_map<level> m_R; /* map from tagged g_level_prefix to "clean" name not in L. */
    name_map<level> m_U; /* map from universe metavariable name to "clean" name not in L. */
    unsigned        m_idx{1};
    buffer<name> &  m_new_param_names;
    /* If m_fixed == true, then m_R, m_L and m_U are read only. We set m_fixed when elaborating
       theorem proofs.
       Remark: we should be able to infer the set of universe variables using just the
       theorem type. */
    bool            m_fixed;

    sanitize_param_names_fn(type_context & ctx, buffer<name> & new_lp_names):
        m_ctx(ctx), m_new_param_names(new_lp_names), m_fixed(false) {}

    sanitize_param_names_fn(type_context & ctx, elaborator::theorem_finalization_info const & info,
                            buffer<name> & new_lp_names):
        m_ctx(ctx), m_L(info.m_L), m_R(info.m_R), m_U(info.m_U),
        m_new_param_names(new_lp_names), m_fixed(true) {}

    level mk_param() {
        while (true) {
            name new_n = m_p.append_after(m_idx);
            m_idx++;
            if (!m_L.contains(new_n)) {
                if (m_fixed) {
                    throw exception(sstream() << "theorem/lemma proof uses universe '" << new_n << "' which does not occur in its type");
                }
                m_new_param_names.push_back(new_n);
                return mk_param_univ(new_n);
            }
        }
    }

    level sanitize(level const & l) {
        name p("u");
        return replace(l, [&](level const & l) -> optional<level> {
                if (is_param(l)) {
                    name const & n = param_id(l);
                    if (is_tagged_by(n, *g_level_prefix)) {
                        if (auto new_l = m_R.find(n)) {
                            return some_level(*new_l);
                        } else {
                            if (m_fixed) {
                                throw exception(sstream() << "theorem/lemma proof uses universe '" << n << "'"
                                                << " which does not occur in its type (possible solution: use def instead of theorem)");
                            }
                            level r = mk_param();
                            m_R.insert(n, r);
                            return some_level(r);
                        }
                    }
                } else if (is_meta(l)) {
                    if (is_metavar_decl_ref(l) && m_ctx.is_assigned(l)) {
                        return some_level(sanitize(*m_ctx.get_assignment(l)));
                    } else {
                        name const & n = meta_id(l);
                        if (auto new_l = m_U.find(n)) {
                            return some_level(*new_l);
                        } else {
                            if (m_fixed) {
                                throw exception(sstream() << "theorem/lemma proof contains an unassigned universe metavariable '" << n << "'"
                                                << " (possible solution: use def instead of theorem)");
                            }
                            level r = mk_param();
                            m_U.insert(n, r);
                            return some_level(r);
                        }
                    }
                }
                return none_level();
            });
    }

    virtual expr visit_constant(expr const & e) override {
        return update_constant(e, map(const_levels(e), [&](level const & l) { return sanitize(l); }));
    }

    virtual expr visit_sort(expr const & e) override {
        return update_sort(e, sanitize(sort_level(e)));
    }

    void collect_params(expr const & e) {
        m_L = collect_univ_params(e, m_L);
    }

    void collect_local_context_params() {
        m_ctx.lctx().for_each([&](local_decl const & l) {
                collect_params(m_ctx.instantiate_mvars(l.get_type()));
                if (auto v = l.get_value())
                    collect_params(m_ctx.instantiate_mvars(*v));
            });
    }

    expr sanitize(expr const & e) {
        expr r = operator()(e);
        return r;
    }

    elaborator::theorem_finalization_info mk_info() {
        return elaborator::theorem_finalization_info(m_L, m_R, m_U);
    }
};

/** When the output of the elaborator may contain meta-variables, we convert the type_context level meta-variables
    into regular kernel meta-variables. */
static expr replace_with_simple_metavars(metavar_context mctx, name_map<expr> & cache, expr const & e) {
    if (!has_expr_metavar(e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!is_metavar(e)) return none_expr();
            if (auto r = cache.find(mlocal_name(e))) {
                return some_expr(*r);
            } else if (auto decl = mctx.get_metavar_decl(e)) {
                expr new_type = replace_with_simple_metavars(mctx, cache, mctx.instantiate_mvars(decl->get_type()));
                expr new_mvar = mk_metavar(mlocal_name(e), new_type);
                cache.insert(mlocal_name(e), new_mvar);
                return some_expr(new_mvar);
            } else if (is_metavar_decl_ref(e)) {
                throw exception("unexpected occurrence of internal elaboration metavariable");
            }
            return none_expr();
        });
}

expr elaborator::elaborate(expr const & e) {
    scoped_info_manager scope_infom(&m_info);
    expr r = visit(e,  none_expr());
    trace_elab_detail(tout() << "result before final checkpoint\n" << r << "\n";);
    synthesize();
    return r;
}

expr elaborator::elaborate_type(expr const & e) {
    scoped_info_manager scope_infom(&m_info);
    expr const & ref = e;
    expr new_e = ensure_type(visit(e, none_expr()), ref);
    synthesize();
    return new_e;
}

expr_pair elaborator::elaborate_with_type(expr const & e, expr const & e_type) {
    scoped_info_manager scope_infom(&m_info);
    expr const & ref = e;
    expr new_e, new_e_type;
    {
        expr Type  = visit(copy_tag(e_type, mk_sort(mk_level_placeholder())), none_expr());
        new_e_type = visit(e_type, some_expr(Type));
        ensure_type(new_e_type, e_type);
        new_e      = visit(e,      some_expr(new_e_type));
        synthesize();
    }
    expr inferred_type = infer_type(new_e);
    if (auto r = ensure_has_type(new_e, inferred_type, new_e_type, ref)) {
        new_e = *r;
    } else {
        auto pp_data = pp_until_different(inferred_type, new_e_type);
        auto pp_fn   = std::get<0>(pp_data);
        throw elaborator_exception(ref,
                                   format("type mismatch, expression") + pp_indent(pp_fn, new_e) +
                                   line() + format("has type") + std::get<1>(pp_data) +
                                   line() + format("but is expected to have type") + std::get<2>(pp_data));
    }
    return mk_pair(new_e, new_e_type);
}

void elaborator::finalize_core(sanitize_param_names_fn & S, buffer<expr> & es,
                               bool check_unassigned, bool to_simple_metavar, bool collect_local_ctx) {
    name_map<expr> to_simple_mvar_cache;
    for (expr & e : es) {
        e = instantiate_mvars(e);
        if (check_unassigned)
            ensure_no_unassigned_metavars(e);
        if (!check_unassigned && to_simple_metavar) {
            e = replace_with_simple_metavars(m_ctx.mctx(), to_simple_mvar_cache, e);
        }
        unassigned_uvars_to_params(e);
        e = instantiate_mvars(e);
        S.collect_params(e);
    }
    if (collect_local_ctx)
        S.collect_local_context_params();
    for (expr & e : es) {
        e = S.sanitize(e);
    }
}

void elaborator::finalize(buffer<expr> & es, buffer<name> & new_lp_names, bool check_unassigned, bool to_simple_metavar) {
    sanitize_param_names_fn S(m_ctx, new_lp_names);
    finalize_core(S, es, check_unassigned, to_simple_metavar, true);
}

pair<expr, level_param_names> elaborator::finalize(expr const & e, bool check_unassigned, bool to_simple_metavar) {
    buffer<expr> es; es.push_back(e);
    buffer<name> new_lp_names;
    finalize(es, new_lp_names, check_unassigned, to_simple_metavar);
    return mk_pair(es[0], to_list(new_lp_names));
}

auto elaborator::finalize_theorem_type(expr const & type, buffer<name> & new_lp_names)
    -> pair<expr, theorem_finalization_info> {
    sanitize_param_names_fn S(m_ctx, new_lp_names);
    buffer<expr> es; es.push_back(type);
    bool check_unassigned  = true;
    bool to_simple_metavar = false;
    bool collect_local_ctx = true;
    finalize_core(S, es, check_unassigned, to_simple_metavar, collect_local_ctx);
    return mk_pair(es[0], S.mk_info());
}

expr elaborator::finalize_theorem_proof(expr const & val, theorem_finalization_info const & info) {
    buffer<name> dummy;
    sanitize_param_names_fn S(m_ctx, info, dummy);
    buffer<expr> es; es.push_back(val);
    bool check_unassigned  = true;
    bool to_simple_metavar = false;
    bool collect_local_ctx = false;
    finalize_core(S, es, check_unassigned, to_simple_metavar, collect_local_ctx);
    return es[0];
}

pair<expr, level_param_names>
elaborate(environment & env, options const & opts, name const & decl_name,
          metavar_context & mctx, local_context const & lctx, expr const & e,
          bool check_unassigned) {
    elaborator elab(env, opts, decl_name, mctx, lctx);
    expr r = elab.elaborate(e);
    auto p = elab.finalize(r, check_unassigned, true);
    mctx = elab.mctx();
    env  = elab.env();
    return p;
}

// Auxiliary procedure for #translate
static expr resolve_local_name(environment const & env, local_context const & lctx, name const & id,
                               expr const & src) {
    /* check local context */
    if (auto decl = lctx.get_local_decl_from_user_name(id)) {
        return copy_tag(src, decl->mk_ref());
    }

    /* check local_refs */
    if (auto ref = get_local_ref(env, id)) {
        /* ref may contain local references that have new names at lctx. */
        return copy_tag(src, replace(*ref, [&](expr const & e, unsigned) {
                    if (is_local(e)) {
                        if (auto decl = lctx.get_local_decl_from_user_name(local_pp_name(e))) {
                            return some_expr(decl->mk_ref());
                        }
                    }
                    return none_expr();
                }));
    }

    /* check in current namespaces */
    for (name const & ns : get_namespaces(env)) {
        auto new_id = ns + id;
        if (!ns.is_anonymous() && env.find(new_id) &&
            (!id.is_atomic() || !is_protected(env, new_id))) {
            return copy_tag(src, mk_constant(new_id));
        }
    }

    /* check if exact name was provided */
    if (!id.is_atomic()) {
        name new_id = id;
        new_id = remove_root_prefix(new_id);
        if (env.find(new_id)) {
            return copy_tag(src, mk_constant(new_id));
        }
    }

    if (id == "sorry")
        return copy_tag(src, mk_constant(id));

    optional<expr> r;
    // globals
    if (env.find(id))
        r = copy_tag(src, mk_constant(id));
    // aliases
    list<name> as = get_expr_aliases(env, id);
    if (!is_nil(as)) {
        buffer<expr> new_as;
        if (r)
            new_as.push_back(*r);
        for (auto const & a : as) {
            new_as.push_back(copy_tag(src, mk_constant(a)));
        }
        r = copy_tag(src, mk_choice(new_as.size(), new_as.data()));
    }

    if (!r)
        throw elaborator_exception(src, format("unknown identifier '") + format(id) + format("'"));

    return *r;
}

vm_obj tactic_resolve_local_name(vm_obj const & vm_id, vm_obj const & vm_s) {
    name const & id        = to_name(vm_id);
    tactic_state const & s = to_tactic_state(vm_s);
    try {
        optional<metavar_decl> g = s.get_main_goal_decl();
        if (!g) return mk_no_goals_exception(s);
        expr src; // dummy
        return mk_tactic_success(to_obj(resolve_local_name(s.env(), g->get_context(), id, src)), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

expr resolve_names(environment const & env, local_context const & lctx, expr const & e) {
    auto fn = [&](expr const & e) {
        if (is_placeholder(e) || is_by(e) || is_as_is(e)) {
            return some_expr(e); // ignore placeholders, nested tactics and as_is terms
        } else if (is_constant(e)) {
            if (!is_nil(const_levels(e))) {
                /* universe level were provided, so the constant was already resolved at parsing time */
                return some_expr(e);
            } else {
                expr new_e = copy_tag(e, resolve_local_name(env, lctx, const_name(e), e));
                return some_expr(new_e);
            }
        } else if (is_local(e)) {
            expr new_e = copy_tag(e, resolve_local_name(env, lctx, local_pp_name(e), e));
            return some_expr(new_e);
        } else {
            return none_expr();
        }
    };
    return replace(e, fn);
}

static vm_obj tactic_save_type_info(vm_obj const & _e, vm_obj const & ref, vm_obj const & _s) {
    expr const & e = to_expr(_e);
    tactic_state const & s = to_tactic_state(_s);
    if (!get_global_info_manager() || !get_pos_info_provider()) return mk_tactic_success(s);
    auto pos = get_pos_info_provider()->get_pos_info(to_expr(ref));
    if (!pos) return mk_tactic_success(s);
    type_context ctx = mk_type_context_for(s);
    try {
        expr type = ctx.infer(e);
        get_global_info_manager()->add_type_info(pos->first, pos->second, type);
        if (is_constant(e))
            get_global_info_manager()->add_identifier_info(pos->first, pos->second, const_name(e));
        else if (is_local(e))
            get_global_info_manager()->add_identifier_info(pos->first, pos->second, local_pp_name(e));
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
    return mk_tactic_success(s);
}

void initialize_elaborator() {
    g_elab_strategy = new name("elab_strategy");
    g_level_prefix = new name("_elab_u");
    register_trace_class("elaborator");
    register_trace_class("elaborator_detail");
    register_trace_class("elaborator_debug");

    register_system_attribute(
        elaborator_strategy_attribute(
            *g_elab_strategy,
            "internal attribute for the elaborator strategy for a given constant"));

    register_system_attribute(
        elaborator_strategy_proxy_attribute(
            "elab_with_expected_type",
            "instructs elaborator that the arguments of the function application (f ...) "
            "should be elaborated using information about the expected type",
            elaborator_strategy::WithExpectedType));

    register_system_attribute(
        elaborator_strategy_proxy_attribute(
            "elab_as_eliminator",
            "instructs elaborator that the arguments of the function application (f ...) "
            "should be elaborated as f were an eliminator",
            elaborator_strategy::AsEliminator));

    register_system_attribute(
        elaborator_strategy_proxy_attribute(
            "elab_simple",
            "instructs elaborator that the arguments of the function application (f ...) "
            "should be elaborated from left to right, and without propagating information from the expected type "
            "to its arguments",
            elaborator_strategy::Simple));

    register_incompatible("elab_simple", "elab_with_expected_type");
    register_incompatible("elab_simple", "elab_as_eliminator");
    register_incompatible("elab_with_expected_type", "elab_as_eliminator");

    DECLARE_VM_BUILTIN(name({"tactic", "save_type_info"}), tactic_save_type_info);
    DECLARE_VM_BUILTIN(name({"tactic", "resolve_name"}),   tactic_resolve_local_name);
}

void finalize_elaborator() {
    delete g_level_prefix;
    delete g_elab_strategy;
}
}
