/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <utility>
#include "runtime/thread.h"
#include "runtime/flet.h"
#include "util/option_declarations.h"
#include "kernel/find_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "library/scope_pos_info_provider.h"
#include "library/error_msgs.h"
#include "library/trace.h"
#include "library/user_recursors.h"
#include "library/aux_recursors.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/suffixes.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/string.h"
#include "library/class.h"
#include "library/sorry.h"
#include "library/util.h"
#include "library/annotation.h"
#include "library/pp_options.h"
#include "library/replace_visitor.h"
#include "library/locals.h"
#include "library/private.h"
#include "library/attribute_manager.h"
#include "library/protected.h"
#include "library/message_builder.h"
#include "library/aliases.h"
#include "library/aux_definition.h"
#include "library/check.h"
#include "library/compiler/compiler.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/tactic_evaluator.h"
#include "library/equations_compiler/compiler.h"
#include "library/equations_compiler/util.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/structure_instance.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/typed_expr.h"
#include "frontends/lean/choice.h"

#ifndef LEAN_DEFAULT_ELABORATOR_COERCIONS
#define LEAN_DEFAULT_ELABORATOR_COERCIONS true
#endif

namespace lean {
static name * g_elab_strategy = nullptr;
static name * g_elaborator_coercions = nullptr;

bool get_elaborator_coercions(options const & opts) {
    return opts.get_bool(*g_elaborator_coercions, LEAN_DEFAULT_ELABORATOR_COERCIONS);
}

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

    if (is_recursor(env, n) ||
        is_aux_recursor(env, n)  ||
        is_user_defined_recursor(env, n)) {
        return elaborator_strategy::AsEliminator;
    }

    return elaborator_strategy::WithExpectedType;
}

#define trace_elab(CODE) lean_trace("elaborator", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_detail(CODE) lean_trace("elaborator_detail", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_debug(CODE) lean_trace("elaborator_debug", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_numeral(CODE) lean_trace(name({"elaborator", "numeral"}), scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_instances(CODE) lean_trace(name({"elaborator", "instances"}), scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_equation(CODE) lean_trace(name({"elaborator", "equation"}), scope_trace_env _scope(m_env, m_ctx); CODE)

elaborator::elaborator(environment const & env, options const & opts, name const & decl_name,
                       metavar_context const & mctx, local_context const & lctx, bool recover_from_errors,
                       bool in_pattern):
    m_env(env), m_opts(opts), m_cache(opts), m_decl_name(decl_name),
    m_ctx(env, mctx, lctx, m_cache, transparency_mode::Semireducible),
    m_recover_from_errors(recover_from_errors),
    m_uses_infom(false /* get_global_info_manager() != nullptr */),
    m_in_pattern(in_pattern) {
    m_coercions = get_elaborator_coercions(opts);
}

elaborator::~elaborator() {
}

auto elaborator::mk_pp_ctx() -> pp_fn {
    return ::lean::mk_pp_ctx(m_ctx.env(), m_opts, m_ctx.mctx(), m_ctx.lctx());
}

formatter elaborator::mk_fmt_ctx() {
    return formatter(m_opts, [=](expr const & e, options const & o) {
        return ::lean::mk_pp_ctx(m_ctx.env(), o, m_ctx.mctx(), m_ctx.lctx())(e);
    });
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

format elaborator::pp_type_mismatch(expr const & e, expr const & e_type, expr const & expected_type) {
    try {
        expr e_type_type = instantiate_mvars(whnf(infer_type(e_type)));
        expr expected_type_type = instantiate_mvars(whnf(infer_type(expected_type)));
        return ::lean::pp_type_mismatch(mk_fmt_ctx(), e, e_type, expected_type, some_expr(e_type_type), some_expr(expected_type_type));
    } catch (exception &) {
        return ::lean::pp_type_mismatch(mk_fmt_ctx(), e, e_type, expected_type);
    }
}

format elaborator::pp_type_mismatch(expr const & e_type, expr const & expected_type) {
    try {
        expr e_type_type = instantiate_mvars(whnf(infer_type(e_type)));
        expr expected_type_type = instantiate_mvars(whnf(infer_type(expected_type)));
        return ::lean::pp_type_mismatch(mk_fmt_ctx(), e_type, expected_type, some_expr(e_type_type), some_expr(expected_type_type));
    } catch (exception &) {
        return ::lean::pp_type_mismatch(mk_fmt_ctx(), e_type, expected_type);
    }
}

bool elaborator::try_report(std::exception const & ex) {
    return try_report(ex, none_expr());
}

bool elaborator::try_report(std::exception const & ex, optional<expr> const & ref) {
    if (auto elab_ex = dynamic_cast<elaborator_exception const *>(&ex)) {
        if (elab_ex->is_ignored()) return true;
    }
    if (!m_recover_from_errors) return false;

    auto pip = get_pos_info_provider();
    if (!pip) return false;
    auto pos = pip->get_some_pos();
    if (m_last_pos)
        pos = *m_last_pos;
    if (ref)
        if (auto p = get_pos(*ref))
            pos = *p;

    auto tc = std::make_shared<type_context_old>(m_env, m_opts, m_ctx.mctx(), m_ctx.lctx());
    message_builder out(tc, m_env, get_global_ios(), pip->get_file_name(), pos, ERROR);
    out.set_exception(ex);
    out.report();
    m_has_errors = true;
    return true;
}

void elaborator::report_or_throw(elaborator_exception const & ex) {
    if (!try_report(ex))
        throw elaborator_exception(ex);
}

bool elaborator::has_synth_sorry(std::initializer_list<expr> && es) {
    for (auto & e : es) {
        if (has_synthetic_sorry(instantiate_mvars(e))) {
            return true;
        }
    }
    return false;
}

expr elaborator::mk_sorry(optional<expr> const & expected_type, expr const & ref, bool synthetic) {
    auto sorry_type = expected_type ? *expected_type : mk_type_metavar(ref);
    return mk_sorry(sorry_type, synthetic);
}

expr elaborator::recoverable_error(optional<expr> const & expected_type, expr const & ref, elaborator_exception const & ex) {
    report_or_throw(ex);
    return mk_sorry(expected_type, ref);
}


level elaborator::mk_univ_metavar() {
    return m_ctx.mk_univ_metavar_decl();
}

expr elaborator::mk_metavar(expr const & A, expr const & ref) {
    return mk_metavar(name(), A, ref);
}

expr elaborator::mk_metavar(name const & pp_n, expr const & A, expr const &) {
    auto m = m_ctx.mk_metavar_decl(pp_n.is_anonymous() ? pp_n : pp_n.append_before("?"), m_ctx.lctx(), A);
    m_user_mvars.insert(mk_pair(m, user_mvar_info(m_last_pos ? *m_last_pos : pos_info(1, 0))));
    return m;
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

    // TODO(gabriel): cache failures so that we do not report errors twice
    optional<expr> inst = m_ctx.mk_class_instance_at(lctx, C);
    if (!inst) {
        metavar_context mctx   = m_ctx.mctx();
        local_context new_lctx = lctx.instantiate_mvars(mctx);
        new_lctx = erase_inaccessible_annotations(new_lctx);
        tactic_state s = ::lean::mk_tactic_state_for(m_env, m_opts, m_decl_name, mctx, new_lctx, C);
        return recoverable_error(some_expr(C), ref, elaborator_exception(
                ref, format("failed to synthesize type class instance for") + line() + s.pp())
            .ignore_if(has_synth_sorry({C})));
    }
    return *inst;
}

expr elaborator::mk_instance_core(expr const & C, expr const & ref) {
    return mk_instance_core(m_ctx.lctx(), C, ref);
}

/* We say a type class (Pi X, (C a_1 ... a_n)), where X may be empty, is
   ready to synthesize if it does not contain metavariables,
   or if the a_i's that contain metavariables are marked as output params. */
bool elaborator::ready_to_synthesize(expr inst_type) {
    if (!has_expr_metavar(inst_type))
        return true;
    while (is_pi(inst_type))
        inst_type = binding_body(inst_type);
    buffer<expr> C_args;
    expr const & C = get_app_args(inst_type, C_args);
    if (!is_constant(C))
        return false;
    expr it = m_ctx.infer(C);
    for (expr const & C_arg : C_args) {
        if (!is_pi(it))
            return false; /* failed */
        expr const & d = binding_domain(it);
        if (has_expr_metavar(C_arg) && !is_class_out_param(d))
            return false;
        it = binding_body(it);
    }
    return true;
}

expr elaborator::mk_instance(expr const & C, expr const & ref) {
    if (!ready_to_synthesize(C)) {
        expr inst = mk_metavar(C, ref);
        m_instances = cons(inst, m_instances);
        return inst;
    } else {
        return mk_instance_core(C, ref);
    }
}

expr elaborator::instantiate_mvars(expr const & e) {
    expr r = m_ctx.instantiate_mvars(e);
    return r;
}

level elaborator::get_level(expr const & A, expr const & ref) {
    expr A_type = whnf(infer_type(A));
    if (is_sort(A_type)) {
        return sort_level(A_type);
    }

    if (is_metavar_app(A_type)) {
        level l = mk_univ_metavar();
        if (try_is_def_eq(A_type, mk_sort(l))) {
            return l;
        }
    }

    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref, pp_type_expected(mk_fmt_ctx(), A, &A_type));
}

level elaborator::replace_univ_placeholder(level const & l) {
    auto fn = [&](level const & l) {
        if (is_placeholder(l))
            return some_level(mk_univ_metavar());
        else
            return none_level();
    };
    return replace(l, fn);
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

/* Temporary hack for get_elim_info_for_builtin.
   It doesn't work for drec recursors for inductive predicates.
   TODO(Leo): fix it. */
static bool is_basic_aux_recursor(environment const & env, name const & n) {
    if (!is_aux_recursor(env, n))
        return false;
    return n.get_string() != "drec";
}

/** See comment at elim_info */
auto elaborator::get_elim_info_for_builtin(name const & fn) -> elim_info {
    lean_assert(is_basic_aux_recursor(m_env, fn) || is_recursor(m_env, fn));
    /* Remark: this is not just an optimization. The code at use_elim_elab_core
       only works for dependent elimination. */
    lean_assert(!fn.is_atomic());
    name const & I_name    = fn.get_prefix();

    unsigned nparams;
    unsigned nindices;
    unsigned nminors;

    constant_info I_info = m_env.get(I_name);
    lean_assert(I_info.is_inductive());
    inductive_val I_val  = I_info.to_inductive_val();
    nparams              = I_val.get_nparams();
    nindices             = I_val.get_nindices();
    nminors              = length(I_val.get_cnstrs());

    elim_info r;
    if (fn.get_string() == g_brec_on || fn.get_string() == g_binduction_on) {
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
    constant_info fn_info = m_env.get(fn);
    if (fn_info.is_recursor()) {
        major_idx = fn_info.to_recursor_val().get_major_idx();
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
    if (is_basic_aux_recursor(m_env, fn) || is_recursor(m_env, fn)) {
        return optional<elim_info>(get_elim_info_for_builtin(fn));
    }
    type_context_old::tmp_locals locals(m_ctx);
    constant_info d   = m_env.get(fn);
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

optional<expr> elaborator::mk_Prop_to_bool_coercion(expr const & e, expr const & ref) {
    expr dec    = mk_app(mk_constant(get_decidable_name()), e);
    expr inst   = mk_instance(dec, ref);
    expr r      = mk_app(mk_constant(get_decidable_decide_name()), e, inst);
    return some_expr(r);
}

static bool is_thunk(expr const & e) {
    return is_app_of(e, get_thunk_name(), 1);
}

optional<expr> elaborator::mk_coercion_core(expr const & e, expr const & e_type, expr const & type, expr const & ref) {
    if (e_type == mk_Prop() && m_ctx.is_def_eq(type, mk_bool())) {
        return mk_Prop_to_bool_coercion(e, ref);
    } else if (is_thunk(type) && m_ctx.is_def_eq(e_type, app_arg(type))) {
        return some_expr(::lean::mk_app(mk_constant(name{"Thunk", "mk"}, const_levels(app_fn(type))),
                                        app_arg(type),
                                        ::lean::mk_lambda("_", mk_constant(get_unit_name()), e)));
    } else if (!has_expr_metavar(e_type) && !has_expr_metavar(type)) {
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

bool elaborator::is_monad_fail(expr const & e) {
    try {
        expr m = mk_app(m_ctx, get_monad_fail_name(), e);
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
optional<expr> elaborator::try_monad_coercion(expr const & e, expr e_type, expr type, expr const & ref) {
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
    e_type = instantiate_mvars(e_type);
    type   = instantiate_mvars(type);
    return mk_coercion_core(e, e_type, type, ref);
}

optional<expr> elaborator::mk_coercion(expr const & e, expr e_type, expr type, expr const & ref) {
    if (!m_coercions) return none_expr();
    synthesize_type_class_instances();
    e_type = instantiate_mvars(e_type);
    type   = instantiate_mvars(type);
    if (auto r = try_monad_coercion(e, e_type, type, ref)) {
        return r;
    }
    if (!has_expr_metavar(e_type)) {
        auto whnf_type = whnf(type);
        if (is_pi(whnf_type)) {
            if (auto r = mk_coercion_to_fn(e, e_type, ref)) {
                return r;
            }
        }
        if (is_sort(whnf_type)) {
            if (auto r = mk_coercion_to_sort(e, e_type, ref)) {
                return r;
            }
        }
        if (!has_expr_metavar(type)) {
            return mk_coercion_core(e, e_type, type, ref);
        }
    }
    trace_coercion_failure(e_type, type, ref,
                            "was not considered because types contain metavariables");
    return none_expr();
}

bool elaborator::is_def_eq(expr const & e1, expr const & e2) {
    type_context_old::fo_unif_approx_scope  scope1(m_ctx);
    type_context_old::ctx_unif_approx_scope scope2(m_ctx);
    try {
        return m_ctx.is_def_eq(e1, e2);
    } catch (exception &) {
        return false;
    }
}

/* Check `e1 =?= e2` using all unifier approximation: first-order, context-compression and quasi-patterns. */
bool elaborator::is_def_eq_all_approx(expr const & e1, expr const & e2) {
    type_context_old::approximate_scope scope(m_ctx);
    try {
        return m_ctx.is_def_eq(e1, e2);
    } catch (exception &) {
        return false;
    }
}

bool elaborator::try_is_def_eq(expr const & e1, expr const & e2) {
    snapshot S(*this);
    flet<bool> dont_recover(m_recover_from_errors, false);
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
        auto exc = elaborator_exception(ref, format(header) + format(", term") +
                pp_type_mismatch(e, e_type, expected_type))
                .ignore_if(has_synth_sorry({e, e_type, expected_type}));
        return recoverable_error(some(expected_type), ref, exc);
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
    if (!m_coercions) return none_expr();
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
    throw elaborator_exception(ref, pp_function_expected(mk_fmt_ctx(), e, e_type))
            .ignore_if(has_synth_sorry({e, e_type}));
}

expr elaborator::ensure_type(expr const & e, expr const & ref) {
    expr e_type = whnf(infer_type(e));
    if (is_sort(e_type)) {
        return e;
    }

    if (is_metavar_app(e_type) && is_def_eq(e_type, mk_sort(mk_univ_metavar()))) {
        return e;
    }

    if (auto r = mk_coercion_to_sort(e, e_type, ref)) {
        return *r;
    }

    report_or_throw(elaborator_exception(ref, pp_type_expected(mk_fmt_ctx(), e, &e_type)));
    // only create the metavar if can actually recover from the error
    return mk_sorry(some_expr(mk_sort(mk_univ_metavar())), ref);
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
    expr val          = get_typed_expr_expr(e);
    expr ref          = val;
    expr type         = get_typed_expr_type(e);
    expr new_type;
    expr ref_type     = get_ref_for_child(type, e);
    new_type = ensure_type(visit(type, none_expr()), ref_type);
    synthesize_type_class_instances();
    expr new_val      = visit(val, some_expr(new_type));
    expr new_val_type = infer_type(new_val);
    if (auto r = ensure_has_type(new_val, new_val_type, new_type, ref))
        return *r;

    return recoverable_error(some_expr(new_type), ref, elaborator_exception(ref, format("invalid type ascription, term ") +
            pp_type_mismatch(new_val_type, new_type)));
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
        return recoverable_error(some_expr(A), ref, elaborator_exception(ref, "invalid pre-numeral, it must be a non-negative value"));
    if (v.is_zero()) {
        expr has_zero_A = copy_pos(ref, mk_app(mk_constant(get_has_zero_name(), ls), A));
        expr S          = mk_instance(has_zero_A, ref);
        return copy_pos(ref, mk_app(copy_pos(ref, mk_app(mk_constant(get_has_zero_zero_name(), ls), A)), S));
    } else {
        expr has_one_A = copy_pos(ref, mk_app(mk_constant(get_has_one_name(), ls), A));
        expr S_one     = mk_instance(has_one_A, ref);
        expr one       = copy_pos(ref, mk_app(copy_pos(ref, mk_app(mk_constant(get_has_one_one_name(), ls), A)), S_one));
        if (v == 1) {
            return one;
        } else {
            expr has_add_A = copy_pos(ref, mk_app(mk_constant(get_has_add_name(), ls), A));
            expr S_add     = mk_instance(has_add_A, ref);
            std::function<expr(mpz const & v)> convert = [&](mpz const & v) {
                lean_assert(v > 0);
                if (v == 1)
                    return one;
                else if (v % mpz(2) == 0) {
                    expr r = convert(v / 2);
                    return copy_pos(ref, mk_app(copy_pos(ref, mk_app(copy_pos(ref, mk_app(mk_constant(get_bit0_name(), ls), A)), S_add)), r));
                } else {
                    expr r = convert(v / 2);
                    return copy_pos(ref, mk_app(copy_pos(ref, mk_app(copy_pos(ref, mk_app(copy_pos(ref, mk_app(mk_constant(get_bit1_name(), ls), A)), S_one)), S_add)), r));
                }
            };
            return convert(v);
        }
    }
}

expr elaborator::visit_sort(expr const & e) {
    level new_l = replace_univ_placeholder(sort_level(e));
    expr r = update_sort(e, new_l);
    if (has_placeholder(sort_level(e)))
        m_to_check_sorts.emplace_back(e, r);
    return r;
}

expr elaborator::visit_const_core(expr const & e) {
    constant_info d = m_env.get(const_name(e));
    buffer<level> ls;
    for (level const & l : const_levels(e)) {
        level new_l = replace_univ_placeholder(l);
        ls.push_back(new_l);
    }
    unsigned num_lparams = d.get_num_lparams();
    if (num_lparams < ls.size()) {
        format msg("incorrect number of universe levels parameters for '");
        msg += format(const_name(e)) + format("', #") + format(num_lparams);
        msg += format(" expected, #") + format(ls.size()) + format("provided");
        return recoverable_error({}, e, elaborator_exception(e, msg));
    }
    // "fill" with meta universe parameters
    for (unsigned i = ls.size(); i < num_lparams; i++)
        ls.push_back(mk_univ_metavar());
    lean_assert(num_lparams == ls.size());
    return update_constant(e, levels(ls));
}

expr elaborator::visit_function(expr const & fn, bool has_args, optional<expr> const & expected_type, expr const & ref) {
    expr ufn = unwrap_pos(fn);
    if (is_placeholder(ufn)) {
        throw elaborator_exception(ref, "placeholders '_' cannot be used where a function is expected");
    }
    if (is_field_notation(ufn))
        throw elaborator_exception(ref, "invalid occurrence of field notation");
    expr r;
    switch (ufn.kind()) {
    case expr_kind::BVar:
    case expr_kind::Pi:
    case expr_kind::MVar:
    case expr_kind::Sort:
    case expr_kind::Lit:
        throw elaborator_exception(ref, "invalid application, function expected");
    // The expr_kind::App case can only happen when nary notation is used
    case expr_kind::App:       r = visit(ufn, expected_type); break;
    case expr_kind::FVar:      r = ufn; break;
    case expr_kind::Const:     r = visit_const_core(ufn); break;
    case expr_kind::MData:     r = visit_mdata(ufn, expected_type, true); break;
    case expr_kind::Lambda:    r = visit_lambda(ufn, expected_type); break;
    case expr_kind::Let:       r = visit_let(ufn, expected_type); break;
    case expr_kind::Proj:      throw elaborator_exception(ref, "unexpected occurrence of proj constructor");
    }
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
            throw elaborator_exception(ref, msg);
        }
    }
}

void elaborator::throw_app_type_mismatch_error(expr const & t, expr const & arg, expr const & arg_type,
                                               expr const & expected_type, expr const & ref) {
    format msg   = format("type mismatch at application");
    msg += pp_indent(mk_pp_ctx(), t);
    msg += line() + format("term") + pp_type_mismatch(arg, arg_type, expected_type);
    throw elaborator_exception(ref, msg).
            ignore_if(has_synth_sorry({arg, arg_type, expected_type}));
}

format elaborator::mk_app_arg_mismatch_error(expr const & t, expr const & arg, expr const & expected_arg) {
    auto pp_data = pp_until_different(mk_fmt_ctx(), arg, expected_arg);
    auto fmt     = std::get<0>(pp_data);
    format msg = format("unexpected argument at application");
    msg += pp_indent_expr(fmt, t);
    msg += line() + format("given argument");
    msg += std::get<1>(pp_data);
    msg += line() + format("expected argument");
    msg += std::get<2>(pp_data);
    return msg;
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
            binder_info bi = binding_info(type);
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
                    throw_app_type_mismatch_error(mk_app(fn, new_args), new_arg, new_arg_type, d, ref);
                }
            } else if (is_explicit(bi)) {
                expr arg_ref = args[j];
                new_arg      = mk_metavar(d, arg_ref);
                postponed    = args[j];
                j++;
            } else if (is_inst_implicit(bi)) {
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
    trace_elab_debug(tout() << "motive_arg:\n  " << motive_arg << "\n";);
    if (!is_def_eq_all_approx(motive_arg, motive)) {
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
                    throw elaborator_exception(ref, format("\"eliminator\" elaborator type mismatch, term") +
                                               pp_type_mismatch(new_arg, infer_type(new_arg), new_arg_type));
                } else {
                    new_args[i] = new_arg;
                }
            }
        }

        expr r = instantiate_mvars(mk_app(mk_app(fn, new_args), extra_args));
        trace_elab_debug(tout() << "elaborated recursor:\n  " << r << "\n";);
        return r;
    } catch (elaborator_exception & ex) {
        // TODO(gabriel): the additional information is not added in error-recovery mode
        throw nested_elaborator_exception(ref, std::current_exception(),
                                          format("the inferred motive for the eliminator-like application is") +
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
    /* Store arguments that need to be abstracted when we apply eta expansion for function applications
       containing optional and auto parameters. */
    buffer<expr>     eta_args;
};

expr elaborator::mk_auto_param(expr const &, expr const &, expr const &) {
    throw exception("auto_param has been disabled (we removed the tactic framework");
}


optional<expr> elaborator::process_optional_and_auto_params(expr type, expr const & ref, buffer<expr> & eta_args, buffer<expr> & new_args) {
    unsigned sz1 = eta_args.size();
    unsigned sz2 = new_args.size();
    optional<expr> result_type;
    while (true) {
        expr it = whnf(type);
        if (!is_pi(it))
            break;
        type = it;
        expr const & d = binding_domain(type);
        expr new_arg;
        bool found = false;
        if (auto def_value = is_optional_param(d)) {
            found   = true;
            new_arg = *def_value;
        } else if (auto p = is_auto_param(d)) {
            found   = true;
            new_arg = mk_auto_param(p->second, p->first, ref);
        } else {
            new_arg = mk_local(mk_fresh_name(), binding_name(type), d, binding_info(type));
            eta_args.push_back(new_arg);
        }
        new_args.push_back(new_arg);
        type = instantiate(binding_body(type), new_arg);
        if (found) {
            result_type = type;
            sz1 = eta_args.size();
            sz2 = new_args.size();
        }
    }
    eta_args.shrink(sz1);
    new_args.shrink(sz2);
    if (result_type)
        return some_expr(Pi(eta_args, *result_type));
    else
        return result_type;
}

expr elaborator::post_process_implicit_arg(expr const & arg, expr const & /* ref */) {
    return arg;
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

    /* Outer loop is used to make sure we consume implicit arguments occurring after auto/option params. */
    while (true) {
        while (is_pi(type)) {
            binder_info bi = binding_info(type);
            expr const & d = binding_domain(type);
            if (is_strict_implicit(bi) && i == args.size())
                break;
            expr new_arg;
            if (!is_explicit(bi)) {
                // implicit argument
                new_arg = mk_metavar(binding_name(type), d, ref);
                if (is_inst_implicit(bi))
                    info.new_instances.push_back(new_arg);
                new_arg = post_process_implicit_arg(new_arg, ref);
            } else if (i < args.size()) {
                // explicit argument
                expr const & arg_ref = args[i];
                info.args_expected_types.push_back(d);
                if (is_as_is(args[i])) {
                    /* We check the type of as-is arguments eagerly, and
                       we don't create a metavariable for them since they
                       have already been elaborated.

                       This is important when we are elaborating terms such as

                       l.map (λ ⟨a, b⟩, a + b)

                       where (l : list (nat × nat))

                       We elaborate l when we process l.map, and convert it into

                       list.map (λ ⟨a, b⟩, a + b) (as-is l)

                       By checking the type of l here, we make sure that the
                       domain of the function (λ ⟨a, b⟩, a + b) is known when
                       we elaborate it.

                       Note that if the user types

                       list.map (λ ⟨a, b⟩, a + b) l
                                 --^ fails here

                       It will fail because we elaborate from left to right, and
                       we don't have the type of l.

                       See discussion at #1403
                    */
                    new_arg = get_as_is_arg(args[i]);
                    expr arg_expected_type;
                    arg_expected_type = d;
                    expr new_arg_type = infer_type(new_arg);
                    optional<expr> new_new_arg = ensure_has_type(new_arg, new_arg_type, arg_expected_type, arg_ref);
                    if (!new_new_arg) {
                        buffer<expr> tmp_args;
                        tmp_args.append(info.new_args);
                        tmp_args.push_back(new_arg);
                        throw_app_type_mismatch_error(mk_app(fn, tmp_args), new_arg, new_arg_type, arg_expected_type, ref);
                    }
                    new_arg = *new_new_arg;
                } else {
                    new_arg = mk_metavar(d, arg_ref);
                }
                i++;
                lean_assert(!get_pos(new_arg));
                info.args_mvars.push_back(new_arg);
                info.new_args_size.push_back(info.new_args.size());
                info.new_instances_size.push_back(info.new_instances.size());
            } else {
                break;
            }
            info.new_args.push_back(new_arg);
            /* See comment above at visit_base_app_core */
            type_before_whnf = instantiate(binding_body(type), new_arg);
            type             = whnf(type_before_whnf);
        }
        type = type_before_whnf;
        if (optional<expr> new_type = process_optional_and_auto_params(type, ref, info.eta_args, info.new_args)) {
            type = *new_type;
            /* If next argument is implicit, then keep consuming */
            type_before_whnf = *new_type;
            type             = whnf(type_before_whnf);
            if (!is_pi(type) || is_explicit(binding_info(type))) {
                type = type_before_whnf;
                break;
            }
        } else {
            break;
        }
    }

    if (i != args.size()) {
        /* failed to consume all explicit arguments, use base elaboration for applications */
        throw elaborator_exception(ref, "too many arguments");
    }
    lean_assert(args.size() == info.args_expected_types.size());
    lean_assert(args.size() == info.args_mvars.size());
    lean_assert(args.size() == info.new_args_size.size());
    lean_assert(args.size() == info.new_instances_size.size());

    if (!is_def_eq(expected_type, type)) {
        expr e = mk_app(fn, info.new_args);
        throw elaborator_exception(ref, format("type mismatch, term") + pp_type_mismatch(e, type, expected_type))
            .ignore_if(has_synth_sorry({type, expected_type, e}));
    }
}

std::tuple<expr, expr, optional<expr>> elaborator::elaborate_arg(expr const & arg, expr const & expected_type, expr const & ref) {
    expr aux_expected_type = expected_type;
    expr new_arg = visit(arg, some_expr(aux_expected_type));
    expr new_arg_type = infer_type(new_arg);
    return std::make_tuple(new_arg, new_arg_type, ensure_has_type(new_arg, new_arg_type, expected_type, ref));
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
        expr ref_arg       = get_ref_for_child(args[i], ref);
        expr expected_type = info.args_expected_types[i];
        info.new_args[info.new_args_size[i]] = recover_expr_from_exception(some_expr(expected_type), ref_arg, [&] {
            if (is_metavar(info.args_mvars[i])) {
                expr new_arg; expr new_arg_type; optional<expr> new_new_arg;
                std::tie(new_arg, new_arg_type, new_new_arg) = elaborate_arg(args[i], expected_type, ref_arg);
                if (!new_new_arg) {
                    buffer<expr> tmp_args;
                    tmp_args.append(info.new_args_size[i], info.new_args.data());
                    tmp_args.push_back(new_arg);
                    throw_app_type_mismatch_error(mk_app(fn, tmp_args), new_arg, new_arg_type,
                                                  info.args_expected_types[i], ref);
                }
                if (!is_def_eq(info.args_mvars[i], *new_new_arg)) {
                    buffer<expr> tmp_args;
                    tmp_args.append(info.new_args_size[i], info.new_args.data());
                    tmp_args.push_back(new_arg);
                    format msg = mk_app_arg_mismatch_error(mk_app(fn, tmp_args),
                                                           new_arg, info.args_mvars[i]);
                    report_or_throw(elaborator_exception(ref, msg).
                        ignore_if(has_synth_sorry({new_arg, instantiate_mvars(info.args_mvars[i])})));
                }
                return *new_new_arg;
            } else {
                return info.args_mvars[i];
            }
        });
    }
    for (; j < info.new_instances.size(); j++) {
        expr const & mvar = info.new_instances[j];
        if (!try_synthesize_type_class_instance(mvar))
            m_instances = cons(mvar, m_instances);
    }
    expr e = Fun(info.eta_args, mk_app(fn, info.new_args.size(), info.new_args.data()));
    for (auto const & new_arg : info.new_args)
        if (m_user_mvars.count(new_arg))
            m_user_mvars[new_arg].m_context = some_expr(e);
    return e;
}

bool elaborator::is_with_expected_candidate(expr const & fn) {
    /* When processing expressions such as (l^.for f), we first resolve the field notation obtaining
           (list.for l)
       Then, when processing ((list.for l) f), we still want to use the expected type.
       So, we should retrieve the constant list.for using get_app_fn.
    */
    expr _fn = get_app_fn(fn);
    if (!is_constant(_fn)) return false;
    return get_elaborator_strategy(m_env, const_name(_fn)) == elaborator_strategy::WithExpectedType;
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
    buffer<expr> eta_args;
    /* Outer loop is used to make sure we consume implicit arguments occurring after auto/option params. */
    while (true) {
        while (true) {
            if (is_pi(type)) {
                binder_info bi = binding_info(type);
                expr const & d = binding_domain(type);
                expr new_arg;
                if (amask == arg_mask::Default && is_strict_implicit(bi) && i == args.size())
                    break;
                if ((amask == arg_mask::Default && !is_explicit(bi)) ||
                    (amask == arg_mask::InstHoExplicit && !is_explicit(bi) && !is_inst_implicit(bi) && !is_pi(d))) {
                    // implicit argument
                    if (is_inst_implicit(bi))
                        new_arg = mk_instance(d, ref);
                    else
                        new_arg = mk_metavar(binding_name(type), d, ref);
                    new_arg = post_process_implicit_arg(new_arg, ref);
                } else if (i < args.size()) {
                    expr expected_type = d;
                    // explicit argument
                    expr ref_arg = get_ref_for_child(args[i], ref);
                    if (args_already_visited) {
                        new_arg = args[i];
                    } else if (is_inst_implicit(bi) && is_placeholder(args[i])) {
                        lean_assert(amask != arg_mask::Default);
                    /* If '@' or '@@' have been used, and the argument is '_', then
                       we use type class resolution. */
                        new_arg = mk_instance(d, ref);
                    } else {
                        new_arg = visit(args[i], some_expr(expected_type));
                    }
                    expr new_arg_type = infer_type(new_arg);
                    if (optional<expr> new_new_arg = ensure_has_type(new_arg, new_arg_type, d, ref_arg)) {
                        new_arg = *new_new_arg;
                    } else {
                        new_args.push_back(new_arg);
                        throw_app_type_mismatch_error(mk_app(fn, new_args.size(), new_args.data()),
                                                      new_arg, new_arg_type, d, ref);
                    }
                    i++;
                } else {
                    break;
                }
                new_args.push_back(new_arg);
                /* See comment above at first type_before_whnf assignment */
                type_before_whnf = instantiate(binding_body(type), new_arg);
                type             = whnf(type_before_whnf);
           } else if (i < args.size()) {
                bool progress = false;
                /* If type is of the form `?m ...`, we may try to synthesize pending type class problems,
                   and check whether `?m` has been instantiated or not.

                   We need this trick to handle `monad_run.run`. This function has type
                   ```
                   run : Π {out m : Type u_1 → Type u_2} [c : monad_run out m] {α : Type u_1}, m α → out α
                   ```
                   The resultant type `out α` depends on resolving the type class resolution problem `monad_run out m`
                   since `out` is marked as an `out_param`.

                   Without this approach, we would have to write
                   ```
                   @[reducible] def type_checker_m := except_t format (reader_t (environment × list result) (state_t context id))

                   def type_checker_m.run {α} (a : type_checker_m α) (env : environment) (r : list result) : except format α :=
                   (run a (env, r) mk_context).1
                   ```
                   as
                   ```
                   @[reducible] def type_checker_m := except_t format (reader_t (environment × list result) (state_t context id))

                   def type_checker_m.run {α} (a : type_checker_m α) (env : environment) (r : list result) : except format α :=
                   let tmp := run a in
                   (tmp (env, r) mk_context).1
                   ```
                   or completely avoid `run`. */
                if (is_metavar_app(type)) {
                    synthesize_type_class_instances();
                    expr new_type = instantiate_mvars(type);
                    if (new_type != type) {
                        type = new_type;
                        progress = true;
                    }
                }
                if (!progress) {
                    expr new_fn = mk_app(fn, new_args.size(), new_args.data());
                    new_args.clear();
                    fn = ensure_function(new_fn, ref);
                    type_before_whnf = infer_type(fn);
                    type = whnf(type_before_whnf);
                }
            } else {
                lean_assert(i == args.size());
                break;
            }
        }
        type = instantiate_mvars(type_before_whnf);

        /* We ignore optional/auto params when `@` is used */
        if (amask != arg_mask::Default)
            break;

        if (optional<expr> new_type = process_optional_and_auto_params(type, ref, eta_args, new_args)) {
            /* If next argument is implicit, then keep consuming */
            type_before_whnf = *new_type;
            type             = whnf(type_before_whnf);
            if (!is_pi(type) || is_explicit(binding_info(type))) {
                type = type_before_whnf;
                break;
            }
        } else {
            break;
        }
    }

    expr r = Fun(eta_args, mk_app(fn, new_args.size(), new_args.data()));
    for (auto const & new_arg : new_args)
        if (m_user_mvars.count(new_arg))
            m_user_mvars[new_arg].m_context = some_expr(r);
    if (expected_type) {
        if (auto new_r = ensure_has_type(r, type, *expected_type, ref)) {
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

           The first one cannot be solved by type_context_old, and an approximate
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

           which, as described above, cannot be solved by type_context_old.
           However, this constraint becomes trivial after we propagate the expected type
           (list name), and we have to solve (list name) =?= (list ?m)
        */
        type_context_old::full_postponed_scope scope(m_ctx, false);
        flet<bool> dont_recover(m_recover_from_errors, false);
        first_pass(fn, args, *expected_type, ref, info);
    } catch (elaborator_exception & ex1) {
        C.restore(*this);
        try {
            return visit_base_app_simple(fn, amask, args, args_already_visited, expected_type, ref);
        } catch (elaborator_exception & ex2) {
            throw nested_elaborator_exception(ref, std::current_exception(),
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

expr elaborator::visit_overloaded_app_core(buffer<expr> const & fns, buffer<expr> const & args,
                                           optional<expr> const & expected_type, expr const & ref) {
    buffer<expr> new_args;
    for (expr const & arg : args) {
        new_args.push_back(visit(arg, none_expr()));
    }

    snapshot S(*this);

    buffer<pair<expr, snapshot>> candidates;
    buffer<elaborator_exception> error_msgs;
    for (expr const & fn : fns) {
        try {
            flet<bool> dont_recover(m_recover_from_errors, false);
            // Restore state
            S.restore(*this);
            bool has_args = !args.empty();
            expr new_fn   = visit_function(fn, has_args, has_args ? none_expr() : expected_type, ref);
            expr c        = visit_overload_candidate(new_fn, new_args, expected_type, ref);
            synthesize_type_class_instances();

            if (expected_type) {
                expr c_type = infer_type(c);
                if (ensure_has_type(c, c_type, *expected_type, ref)) {
                    candidates.emplace_back(c, snapshot(*this));
                } else {
                    throw elaborator_exception(ref, format("invalid overload, term") +
                            pp_type_mismatch(c, c_type, *expected_type));
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

        throw elaborator_exception(ref, mk_no_overload_applicable_msg(fns, error_msgs));
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
            flet<bool> dont_recover(m_recover_from_errors, false);
            // Restore state
            S.restore(*this);
            bool has_args = !args.empty();
            expr new_fn   = visit_function(fn, has_args, has_args ? none_expr() : some(expected_type), ref);
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
            throw nested_elaborator_exception(ref, std::current_exception(), msg);
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

            throw nested_elaborator_exception(ref, std::current_exception(), msg);
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
        throw nested_elaborator_exception(ref, std::current_exception(), msg);
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
            throw nested_elaborator_exception(ref, std::current_exception(), msg);
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
    inductive_val I_val  = m_env.get(I_name).to_inductive_val();
    unsigned nparams     = I_val.get_nparams();
    unsigned nindices    = I_val.get_nindices();
    buffer<expr> new_args;
    for (unsigned i = 0; i < nparams + nindices; i++) {
        new_args.push_back(copy_pos(ref, mk_expr_placeholder()));
    }
    new_args.push_back(copy_pos(ref, mk_as_is(*expected_type)));
    new_args.push_back(copy_pos(ref, mk_expr_placeholder())); // lhs
    new_args.push_back(copy_pos(ref, mk_expr_placeholder())); // rhs
    new_args.push_back(copy_pos(args[0], mk_as_is(Heq)));
    for (unsigned i = 1; i < args.size(); i++)
        new_args.push_back(args[i]);
    return visit_base_app_core(fn, arg_mask::AllExplicit, new_args, false, expected_type, ref);
}

expr elaborator::visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type,
                                expr const & ref) {
    arg_mask amask = arg_mask::Default;
    expr ufn = unwrap_pos(fn);
    if (is_explicit(ufn)) {
        fn   = get_explicit_arg(ufn);
        amask = arg_mask::AllExplicit;
    } else if (is_partial_explicit(ufn)) {
        fn   = get_partial_explicit_arg(ufn);
        amask = arg_mask::InstHoExplicit;
    }

    bool has_args = !args.empty();

    expr orig_fn = fn;
    fn = unwrap_pos(fn);
    while (is_annotation(fn))
        fn = get_annotation_arg(fn);

    if (is_choice(fn)) {
        buffer<expr> fns;
        if (amask != arg_mask::Default) {
            format fmt = format("invalid explicit annotation because of overloading (possible solution: use fully qualified names) ");
            for (unsigned i = 0; i < get_num_choices(fn); i++)
                fns.push_back(get_choice(fn, i));
            auto pp_fn = mk_pp_ctx();
            fmt += pp_overloads(pp_fn, fns);
            throw elaborator_exception(ref, fmt);
        }
        for (unsigned i = 0; i < get_num_choices(fn); i++) {
            expr const & fn_i = get_choice(fn, i);
            fns.push_back(fn_i);
        }
        validate_overloads(fns, ref);
        return visit_overloaded_app(fns, args, expected_type, ref);
    } else if (is_field_notation(fn) && amask == arg_mask::Default) {
        expr s           = visit(mdata_expr(fn), none_expr());
        expr s_type      = head_beta_reduce(instantiate_mvars(infer_type(s)));
        auto field_res   = find_field_fn(fn, s, s_type);
        expr proj, proj_type;
        if (field_res.m_ldecl) {
            proj      = copy_pos(fn, field_res.m_ldecl->mk_ref());
            proj_type = field_res.m_ldecl->get_type();
        } else {
            proj      = copy_pos(fn, mk_constant(field_res.get_full_fname()));
            proj_type = m_env.get(field_res.get_full_fname()).get_type();
        }
        buffer<expr> new_args;
        unsigned i       = 0;
        while (is_pi(proj_type)) {
            if (is_explicit(binding_info(proj_type))) {
                if (is_app_of(extract_mdata(binding_domain(proj_type)), field_res.m_base_S_name)) {
                    /* found s location */
                    expr coerced_s = *mk_base_projections(m_env, field_res.m_S_name, field_res.m_base_S_name, mk_as_is(s));
                    new_args.push_back(copy_pos(fn, std::move(coerced_s)));
                    for (; i < args.size(); i++)
                        new_args.push_back(args[i]);
                    expr new_proj = visit_function(proj, has_args, has_args ? none_expr() : expected_type, ref);
                    return visit_base_app(new_proj, amask, new_args, expected_type, ref);
                } else {
                    if (i >= args.size()) {
                        throw elaborator_exception(ref, sstream() << "invalid field notation, insufficient number of arguments for '"
                                                   << field_res.get_full_fname() << "'");
                    }
                    new_args.push_back(args[i]);
                    i++;
                }
            }
            proj_type = binding_body(proj_type);
        }
        throw elaborator_exception(ref, sstream() << "invalid field notation, function '"
                                   << field_res.get_full_fname() << "' does not have explicit argument with type ("
                                   << field_res.m_base_S_name << " ...)");
    } else {
        expr new_fn = visit_function(fn, has_args, has_args ? none_expr() : expected_type, orig_fn);
        /* Check if we should use a custom elaboration procedure for this application. */
        if (is_constant(new_fn) && amask == arg_mask::Default) {
            if (auto info = use_elim_elab(const_name(new_fn))) {
                if (args.size() >= info->m_nexplicit) {
                    return visit_elim_app(new_fn, *info, args, expected_type, ref);
                } else {
                    try {
                        return visit_base_app(new_fn, amask, args, expected_type, ref);
                    } catch (elaborator_exception & ex) {
                        throw nested_elaborator_exception(ref, std::current_exception(),
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
                        throw nested_elaborator_exception(ref, std::current_exception(), *error_msg);
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
    new_args.push_back(copy_pos(e, mk_expr_placeholder()));
    new_args.push_back(copy_pos(e, mk_prenum(mpz(line))));
    new_args.push_back(copy_pos(e, mk_prenum(mpz(col))));
    new_args.push_back(app_arg(e));
    return visit(mk_app(copy_pos(e, mk_explicit(app_fn(e))), new_args.size(), new_args.data()), expected_type);
}

expr elaborator::visit_app(expr const & e, optional<expr> const & expected_type) {
    if (is_app_of(e, get_scope_trace_name(), 1))
        return visit_scope_trace(e, expected_type);
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    flet<optional<pos_info>> _(m_last_pos, get_pos(fn));
    expr ufn = unwrap_pos(fn);
    if (is_infix_function(ufn)) {
        expr infix_fn = get_annotation_arg(ufn);
        lean_assert(is_lambda(infix_fn));
        return visit(head_beta_reduce(copy_pos(e, mk_app(infix_fn, args))), expected_type);
    } else if (is_equations(ufn)) {
        return visit_convoy(e, expected_type);
    } else {
        return visit_app_core(fn, args, expected_type, e);
    }
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
    if (is_private(I_name) && !is_expr_aliased(m_env, I_name))
        throw elaborator_exception(e, "invalid constructor ⟨...⟩, type is a private inductive datatype");
    constant_info I_info = m_env.get(I_name);
    if (!I_info.is_inductive())
        throw elaborator_exception(e, sstream() << "invalid constructor ⟨...⟩, '" << I_name << "' is not an inductive type");
    names c_names = I_info.to_inductive_val().get_cnstrs();
    if (!c_names || tail(c_names))
        throw elaborator_exception(e, sstream() << "invalid constructor ⟨...⟩, '" << I_name << "' must have only one constructor");
    expr type = m_env.get(head(c_names)).get_type();
    unsigned num_explicit = 0;
    while (is_pi(type)) {
        if (is_explicit(binding_info(type)))
            num_explicit++;
        type = binding_body(type);
    }
    if (num_explicit > 1 && args.size() > num_explicit) {
        unsigned num_extra = args.size() - num_explicit;
        expr rest = copy_pos(e, mk_app(c, num_extra + 1, args.data() + num_explicit - 1));
        rest = copy_pos(e, mk_anonymous_constructor(rest));
        args.shrink(num_explicit);
        args.back() = rest;
    }
    expr new_e = copy_pos(e, mk_app(mk_constant(head(c_names)), args));
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
    if (!has_loose_bvars(a))
        return a;
    auto fn = [=](expr const & m, unsigned offset) -> optional<expr> {
        if (offset >= get_loose_bvar_range(m))
            return some_expr(m); // expression m does not contain free variables with idx >= offset
        if (is_var(m)) {
            unsigned vidx = bvar_idx(m).get_small_value();
            if (vidx >= offset) {
                unsigned h = offset + n;
                if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                    expr local = subst[n - (vidx - offset) - 1];
                    lean_assert(is_local(local));
                    return some_expr(copy_pos(m, copy(local)));
                } else {
                    return some_expr(copy_pos(m, mk_bvar(vidx - n)));
                }
            }
        }
        return none_expr();
    };
    return replace(a, fn);
}

static expr instantiate_rev_locals(expr const & e, type_context_old::tmp_locals const & locals) {
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
    lean_assert(is_equations(unwrap_pos(get_app_fn(e))));
    expr const & ref = e;
    buffer<expr> args, new_args;
    expr eqns = unwrap_pos(get_app_args(e, args));
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
        try {
            check(m_ctx, new_fn_type);
        } catch (exception & ex) {
            throw nested_exception("invalid match/convoy expression, "
                                   "user did not provide type for the expression, "
                                   "lean tried to infer one using expected type information, "
                                   "but result is not type correct", std::current_exception());
        }
    } else {
        // User provided some typing information for the match
        type_context_old::tmp_locals locals(m_ctx);
        expr it = fn_type;
        for (unsigned i = 0; i < args.size(); i++) {
            it = unwrap_pos(it);
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
#if 0
    /* The following check is too restrictive in do blocks. */
    if (has_expr_metavar(new_fn_type)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(ref, format("invalid match/convoy expression, type contains meta-variables") +
                                   pp_indent(pp_fn, new_fn_type));
    }
#endif
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
    } else if (is_binding(source) && is_binding(target)) {
        return update_binding(source, mk_as_is(binding_domain(source)),
                              copy_domain(num-1, binding_body(source), binding_body(target)));
    } else {
        return target;
    }
}

static void throw_ill_formed_equation(expr const & ref) {
    throw elaborator_exception(ref, "ill-formed match/equation expression");
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
            if (!is_var(fn) || bvar_idx(fn) >= nbinders)
                throw_ill_formed_equation(eqn);
            unsigned fidx    = nbinders - bvar_idx(fn).get_small_value() - 1;
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
            throw_ill_formed_equation(curr);
        }
    }
}

bool elaborator::keep_do_failure_eq(expr const & first_eq) {
    if (!is_lambda(first_eq))
        return false; // possible with error recovery
    expr type = binding_domain(first_eq);
    if (!is_pi(type))
        return false;
    type = binding_body(type);
    if (has_loose_bvars(type))
        return false;
    return is_app(type) && is_monad_fail(app_fn(type));
}

expr elaborator::mk_aux_meta_def(expr const & e, expr const & ref) {
    name aux_name(m_decl_name, "_aux_meta");
    aux_name = aux_name.append_after(m_aux_meta_idx);
    m_aux_meta_idx++;
    expr new_c;
    metavar_context mctx = m_ctx.mctx();
    std::tie(m_env, new_c) = mk_aux_definition(m_env, mctx, local_context(),
                                               aux_name, e, optional<bool>(true));
    if (!is_constant(new_c)) {
        throw elaborator_exception(ref, "failed to create auxiliary definition");
    }
    m_env = compile(m_env, m_opts, const_name(new_c));
    m_ctx.set_env(m_env);
    m_ctx.set_mctx(mctx);
    return new_c;
}

static void mvar_dep_sort_aux(type_context_old & ctx, expr const & m,
                              name_set const & mvar_names, name_set & visited, buffer<expr> & result) {
    if (visited.contains(mvar_name(m)))
        return;
    for_each(ctx.instantiate_mvars(ctx.infer(m)), [&](expr const & e, unsigned) {
            if (is_mvar(e) && mvar_names.contains(mvar_name(e))) {
                mvar_dep_sort_aux(ctx, e, mvar_names, visited, result);
                return false; // do not visit types
            }
            if (is_local(e)) {
                return false; // do not visit types
            }
            return true;
        });
    visited.insert(mvar_name(m));
    result.push_back(m);
}

/* Topological sort based on dependencies. */
static void mvar_dep_sort(type_context_old & ctx, buffer<expr> & mvars) {
    name_set visited;
    buffer<expr> result;
    name_set mvar_names;
    for (expr const & m : mvars)
        mvar_names.insert(mvar_name(m));
    for (expr const & m : mvars)
        mvar_dep_sort_aux(ctx, m, mvar_names, visited, result);
    mvars.clear();
    mvars.append(result);
}

/* We preprocess the equation left-hand-side by first elaborating it using metavariables.
   This process allows us to refine pattern variables whose value is fixed by type inference.
   Before processing the right-hand-side, we must convert back these metavariables into
   pattern variables (i.e., local constants).
   This visitor collects metavariables that must be converted into pattern variables, and
   validates the equation left-hand-side. It returns the input expression expanded to
   expose its primitive patterns. */
class validate_and_collect_lhs_mvars : public replace_visitor {
    elaborator &    m_elab;
    bool            m_has_invalid_pattern = false;
    expr            m_ref;
    /* m_mctx0 is the metavariable context before processing the equation.
       Only metavariables created when processing the equation can be
       converted into pattern variables. */
    metavar_context m_mctx0;
    buffer<expr> &  m_unassigned_mvars;
    name_set        m_collected;

    type_context_old & ctx() { return m_elab.m_ctx; }

    environment const & env() { return m_elab.env(); }

    optional<expr> expand(expr const & e) {
        /* We don't simply use whnf because we want to avoid exposing the internal implementation
           of definitions compiled using the equation compiler */
        {
            /* Try without use delta reduction */
            type_context_old::transparency_scope scope(ctx(), transparency_mode::None);
            expr new_e = ctx().whnf(e);
            if (new_e != e) return some_expr(new_e);
        }
        if (auto new_e = ctx().reduce_projection(e))
            return new_e;
        // HACK: trying to delete `dunfold`
        // /* Try to unfold using refl equations */
        // if (auto new_e = dunfold(ctx(), e))
        // return new_e;
        /* Last resort, whnf using current setting */
        expr new_e = ctx().whnf(e);
        if (new_e != e) return some_expr(new_e);
        return none_expr();
    }

    void throw_invalid_pattern(char const * msg, expr const & e) {
        m_elab.report_or_throw(
            elaborator_exception(m_ref, format(msg)
                + format(" (possible solution, mark term as inaccessible using '.( )')")
                + m_elab.pp_indent(e))
            .ignore_if(m_elab.has_synth_sorry(e)));
        m_has_invalid_pattern = true;
    }

    virtual expr visit_local(expr const & e) override {
        return e;
    }

    virtual expr visit_lambda(expr const & e) override {
        throw_invalid_pattern("invalid occurrence of lambda expression in pattern", e);
        return e;
    }

    virtual expr visit_pi(expr const & e) override {
        throw_invalid_pattern("invalid occurrence of pi/forall expression in pattern", e);
        return e;
    }

    virtual expr visit_let(expr const & e) override {
        return visit(instantiate(let_body(e), let_value(e)));
    }

    virtual expr visit_sort(expr const & e) override {
        throw_invalid_pattern("invalid occurrence of sort in pattern", e);
        return e;
    }

    virtual expr visit_meta(expr const & m) override {
        if (is_metavar_decl_ref(m) && !m_mctx0.find_metavar_decl(m)) {
            if (!m_collected.contains(mvar_name(m))) {
                m_unassigned_mvars.push_back(m);
                m_collected.insert(mvar_name(m));
            }
            return m;
        } else {
            throw_invalid_pattern("invalid occurrence of metavariable in pattern", m);
            return m;
        }
    }

    void throw_invalid_app(expr const & e) {
        if (is_constant(e))
            throw_invalid_pattern("invalid constant in pattern, it cannot be reduced to a constructor", e);
        else
            throw_invalid_pattern("invalid function application in pattern, it cannot be reduced to a constructor", e);
    }

    virtual expr visit_app(expr const & e) override {
        expr it = e;
        while (true) {
            if (is_nat_int_char_string_name_value(ctx(), it))
                return e;
            if (!is_app(it) && !is_constant(it))
                return visit(it);
            buffer<expr> args;
            expr const & fn = get_app_args(it, args);
            if (!is_constant(fn)) {
                throw_invalid_app(e);
                return e;
            }

            constant_info fn_info = env().get(const_name(fn));
            if (fn_info.is_constructor()) {
                unsigned num_params = fn_info.to_constructor_val().get_nparams();
                for (unsigned i = num_params; i < args.size(); i++) {
                    visit(args[i]);
                }
                return e;
            } else {
                if (auto r = expand(it)) {
                    it = *r;
                } else {
                    throw_invalid_app(e);
                    return e;
                }
            }
        }
    }

    virtual expr visit_constant(expr const & e) override {
        return visit_app(e);
    }

    virtual expr visit_mdata(expr const & e) override {
        if (is_inaccessible(e)) {
            return e;
        } else if (is_as_pattern(e)) {
            expr new_lhs = visit(get_as_pattern_lhs(e));
            expr new_rhs = visit(get_as_pattern_rhs(e));
            return mk_as_pattern(new_lhs, new_rhs);
        } else if (is_structure_instance(e)) {
            auto info = get_structure_instance_info(e);
            if (info.m_sources.size())
                throw elaborator_exception(info.m_sources[0], "invalid occurrence of structure notation source in pattern");
            for (expr & val : info.m_field_values)
                val = visit(val);
            return mk_structure_instance(info);
        } else {
            return visit(mdata_expr(e));
        }
    }

public:
    validate_and_collect_lhs_mvars(elaborator & elab, expr const & ref, metavar_context const & mctx0,
                                   buffer<expr> & unassigned_mvars):
        m_elab(elab),
        m_ref(ref),
        m_mctx0(mctx0),
        m_unassigned_mvars(unassigned_mvars) {
    }

    bool operator()(expr const & lhs) {
        buffer<expr> args;
        get_app_args(lhs, args);
        for (expr & arg : args)
            visit(arg);
        return m_has_invalid_pattern;
    }
};

/* Similar to instantiate_mvars, but add an inaccessible pattern annotation around metavariables
   whose value has been fixed by type inference. */
static expr instantiate_pattern_mvars(type_context_old & ctx, expr const & lhs) {
    return replace(lhs, [&](expr const & e, unsigned) {
            if (is_metavar_decl_ref(e) && ctx.is_assigned(e)) {
                expr v = ctx.instantiate_mvars(e);
                if (!is_local(v) && !is_metavar(v))
                    return some_expr(copy_pos(e, mk_inaccessible(v)));
                else
                    return some_expr(v);
            } else {
                return none_expr();
            }
        });
}

expr elaborator::visit_equation(expr const & e, unsigned num_fns) {
    expr const & ref = e;
    type_context_old::tmp_locals fns(m_ctx);
    expr it = e;
    for (unsigned i = 0; i < num_fns; i++) {
        if (!is_lambda(it))
            throw_ill_formed_equation(ref);
        expr d     = instantiate_rev_locals(binding_domain(it), fns);
        expr new_d = visit(d, none_expr());
        expr ref_d = get_ref_for_child(binding_domain(it), it);
        expr fn    = push_local(fns, binding_name(it), new_d, binding_info(it), ref_d);
        it = binding_body(it);
    }
    if (is_no_equation(it)) {
        return fns.mk_lambda(it);
    } else {
        trace_elab_equation(tout() << "visit_equation\n";);
        metavar_context mctx0 = m_ctx.mctx();
        it = instantiate_rev_locals(it, fns);
        buffer<expr> local_mvars;
        buffer<expr> type_mvars;
        while (is_lambda(it)) {
            expr type = mk_type_metavar(it);
            type_mvars.push_back(type);
            expr mvar = m_ctx.mk_metavar_decl(binding_name(it), m_ctx.lctx(), type);
            local_mvars.push_back(mvar);
            it = binding_body(it);
        }
        if (!is_equation(it))
            throw_ill_formed_equation(ref);
        expr lhs    = instantiate_rev(equation_lhs(it), local_mvars);
        expr lhs_fn = get_app_fn(lhs);
        if (is_explicit_or_partial_explicit(lhs_fn))
            lhs_fn = get_explicit_or_partial_explicit_arg(lhs_fn);
        if (!is_local_p(lhs_fn))
            throw_ill_formed_equation(ref);
        expr new_lhs;
        {
            flet<bool> set(m_in_pattern, true);
            flet<bool> dont_recover(m_recover_from_errors, false);
            /* Note that pattern elaboration is more sensitive than standard elaboration:
             * mvars in `new_lhs` will be turned into pattern variables below, so care must be taken when instantiating
             * or introducing them. See the very end of `visit_structure_instance` for an example. */
            new_lhs = visit(lhs, none_expr());
            synthesize();
        }
        trace_elab_equation(tout() << "new_lhs:\n" << new_lhs << "\n";);
        new_lhs = instantiate_pattern_mvars(m_ctx, new_lhs);
        trace_elab_equation(tout() << "new_lhs (after instantiate_pattern_mvars):\n" << new_lhs << "\n";);
        // collect unassigned metavariables not in mctx0
        buffer<expr> unassigned_mvars;
        validate_and_collect_lhs_mvars(*this, ref, mctx0, unassigned_mvars)(new_lhs);
        // sort using dependencies
        mvar_dep_sort(m_ctx, unassigned_mvars);
        // create local variables for each unassigned metavar
        type_context_old::tmp_locals new_locals(m_ctx);
        unsigned next_idx = 1;
        for (expr & m : unassigned_mvars) {
            expr type      = instantiate_mvars(m_ctx.infer(m));
            name user_name;
            if (optional<metavar_decl> mdecl = m_ctx.find_metavar_decl(m)) {
                user_name = mdecl->get_user_name();
            } else {
                user_name = name("_x").append_after(next_idx);
                next_idx++;
            }
            expr new_local = new_locals.push_local(user_name, type, mk_binder_info());
            m_ctx.assign(m, new_local);
        }
        // replace metavariables with new locals
        new_lhs           = instantiate_mvars(new_lhs);
        expr new_lhs_type = instantiate_mvars(infer_type(new_lhs));
        // process rhs
        buffer<expr> rhs_subst;
        for (expr const & local_mvar : local_mvars) {
            expr s = instantiate_mvars(local_mvar);
            if (!is_local(s)) {
                /* The `as_is` annotation affects how applications are elaborated.
                   See comment at first_pass method.
                   So, we only use it if it is really needed. That is,
                   the metavariable was fixed to a non trivial term by type inference rules.
                   For example, in the following definition

                   ```
                   inductive Vec (A : Type) : nat → Type
                   | nil {} : Vec 0
                   | cons   : Π {n}, A → Vec n → Vec (succ n)

                   open Vec

                   def append1 {A : Type} : Π {m n : nat}, Vec A m -> Vec A n -> Vec A (n + m)
                   | n m nil         ys := ys
                   | n m (cons x xs) ys := cons x (append1 xs ys)
                   ```

                   The variable n is refined to 0 and (succ n') in the first and second equations.
                */
                s = mk_as_is(s);
            }
            rhs_subst.push_back(s);
        }
        expr rhs     = instantiate_rev(equation_rhs(it), rhs_subst);
        expr new_rhs = visit(rhs, some_expr(new_lhs_type));
        // synthesize();
        // new_rhs       = instantiate_mvars(new_rhs);
        new_rhs       = enforce_type(new_rhs, new_lhs_type, "equation type mismatch", it);
        expr new_eq = copy_pos(it, mk_equation(new_lhs, new_rhs, ignore_equation_if_unused(it)));
        trace_elab_equation(tout() << new_eq << "\n";);
        expr r = copy_pos(ref, fns.mk_lambda(new_locals.mk_lambda(new_eq)));
        return r;
    }
}

expr elaborator::visit_equations(expr const & e) {
    expr const & ref = e;
    buffer<expr> eqs;
    buffer<expr> new_eqs;
    optional<expr> new_tacs;
    equations_header const & header = get_equations_header(e);
    unsigned num_fns = header.m_num_fns;
    to_equations(e, eqs);
    lean_assert(!eqs.empty());

    if (is_wf_equations(e)) {
        expr type = mk_constant(get_well_founded_tactics_name());
        new_tacs  = visit(equations_wf_tactics(e), some_expr(type));
        new_tacs  = enforce_type(*new_tacs, type, "well_founded_tactics object expected", ref);
        if (!is_constant(*new_tacs)) {
            new_tacs = mk_aux_meta_def(*new_tacs, ref);
        }
    }

    optional<expr> first_eq;
    for (expr const & eq : eqs) {
        expr new_eq;
        if (first_eq) {
            if (is_do_failure_eq(eq) && !keep_do_failure_eq(*first_eq)) {
                /* skip equation since it doesn't implement the monad_fail interface */
            } else {
                /* Replace first num_fns domains of eq with the ones in first_eq.
                   This is a trick/hack to ensure the fns in each equation have
                   the same elaborated type. */
                new_eq   = copy_pos(eq, visit_equation(copy_domain(num_fns, *first_eq, eq), num_fns));
                new_eqs.push_back(new_eq);
            }
        } else {
            new_eq   = copy_pos(eq, visit_equation(eq, num_fns));
            first_eq = new_eq;
            new_eqs.push_back(new_eq);
        }
    }
    check_equations_arity(new_eqs);
    synthesize();
    expr new_e;
    if (new_tacs) {
        new_e = copy_pos(e, mk_equations(header, new_eqs.size(), new_eqs.data(), *new_tacs));
    } else {
        new_e = copy_pos(e, mk_equations(header, new_eqs.size(), new_eqs.data()));
    }
    new_e = instantiate_mvars(new_e);
    ensure_no_unassigned_metavars_core(new_e);
    if (has_sorry(new_e))
        // aborting here prevents many additional errors
        throw elaborator_exception(e, "[abort visit_equation]").ignore_if(true);
    if (!has_synth_sorry(new_e) && has_expr_metavar(e)) {
        /* We perform this check to be able to reject code such as:
           ```
           @[pattern] def badPattern (x : Nat) : Nat := 0
           def tst (x : Nat) : Nat :=
           match x with
           | (@badPattern _) := 1
           | _               := 2
           ```
        */
        // TODO(Leo, Kha): enable the following check
        // throw elaborator_exception(new_e, "invalid pattern");
    }
    metavar_context mctx = m_ctx.mctx();
    expr r = compile_equations(m_env, *this, mctx, m_ctx.lctx(), new_e);
    m_ctx.set_env(m_env);
    m_ctx.set_mctx(mctx);
    return r;
}

expr elaborator::visit_inaccessible(expr const & e, optional<expr> const & expected_type) {
    if (!m_in_pattern)
        throw elaborator_exception(e, "invalid occurrence of 'inaccessible' annotation, "
                                   "it must only occur in patterns");
    expr a = get_annotation_arg(e);
    expr new_a;
    {
        flet<bool> set(m_in_pattern, false);
        new_a = visit(a, expected_type);
    }
    return copy_pos(e, mk_inaccessible(new_a));
}

elaborator::field_resolution elaborator::field_to_decl(expr const & e, expr const & s, expr const & s_type) {
    // prefer 'unknown identifier' error when lhs is a constant of non-value type
    if (is_field_notation(e)) {
        auto lhs = unwrap_pos(mdata_expr(e));
        if (is_constant(lhs)) {
            type_context_old::tmp_locals locals(m_ctx);
            expr t = whnf(s_type);
            while (is_pi(t)) {
                t = whnf(instantiate(binding_body(t), locals.push_local_from_binding(t)));
            }
            if (is_sort(t) && !is_anonymous_field_notation(e)) {
                name fname = get_field_notation_field_name(e);
                throw elaborator_exception(lhs, format("unknown identifier '") + format(const_name(lhs)) + format(".") +
                                           format(fname) + format("'"));
            }
        }
    }
    expr I      = get_app_fn(s_type);
    if (!is_constant(I)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(e, format("invalid field notation, type is not of the form (C ...) where C is a constant") +
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
        auto fnames = get_structure_fields(m_env, const_name(I));
        unsigned fidx = get_field_notation_field_idx(e);
        if (fidx  == 0) {
            throw elaborator_exception(e, "invalid projection, index must be greater than 0");
        }
        if (fidx > fnames.size()) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(e, format("invalid projection, structure has only ") +
                                       format(fnames.size()) + format(" field(s)") +
                                       pp_indent(pp_fn, s) +
                                       line() + format("which has type") +
                                       pp_indent(pp_fn, s_type));
        }
        return const_name(I) + fnames[fidx-1];
    } else {
        name fname  = get_field_notation_field_name(e);
        // search for "true" fields first, including in parent structures
        if (is_structure_like(m_env, const_name(I)))
            if (auto p = find_field(m_env, const_name(I), fname))
                return field_resolution(const_name(I), *p, fname);
        name full_fname = const_name(I) + fname;
        name local_name = full_fname.replace_prefix(get_namespace(env()), {});
        if (auto ldecl = m_ctx.lctx().find_if([&](local_decl const & decl) {
            return is_rec(decl.get_info()) && decl.get_user_name() == local_name;
        })) {
            // projection is recursive call
            return field_resolution(full_fname, ldecl);
        }
        if (!m_env.find(full_fname)) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(e, format("invalid field notation, '") + format(fname) + format("'") +
                                       format(" is not a valid \"field\" because environment does not contain ") +
                                       format("'") + format(full_fname) + format("'") +
                                       pp_indent(pp_fn, s) +
                                       line() + format("which has type") +
                                       pp_indent(pp_fn, s_type));
        }
        return full_fname;
    }
}

elaborator::field_resolution elaborator::find_field_fn(expr const & e, expr const & s, expr const & s_type) {
    try {
        return field_to_decl(e, s, s_type);
    } catch (elaborator_exception & ex1) {
        expr new_s_type = s_type;
        if (auto d = unfold_term(env(), new_s_type))
            new_s_type = *d;
        new_s_type = m_ctx.whnf_head_pred(new_s_type, [](expr const &) { return false; });
        if (new_s_type == s_type)
            throw;
        std::exception_ptr ex1_ptr = std::current_exception();
        try {
            return find_field_fn(e, s, new_s_type);
        } catch (elaborator_exception & ex2) {
            throw nested_elaborator_exception(ex2.get_pos(), ex1_ptr, ex2.pp());
        }
    }
}

expr elaborator::visit_field(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_field_notation(e));
    expr s         = visit(mdata_expr(e), none_expr());
    expr s_type    = head_beta_reduce(instantiate_mvars(infer_type(s)));
    auto field_res = find_field_fn(e, s, s_type);
    expr proj_app;
    if (field_res.m_ldecl) {
        proj_app   = copy_pos(e, mk_app(field_res.m_ldecl->mk_ref(), mk_as_is(s)));
    } else {
        expr new_e = *mk_base_projections(m_env, field_res.m_S_name, field_res.m_base_S_name, mk_as_is(s));
        proj_app   = mk_proj_app(m_env, field_res.m_base_S_name, field_res.m_fname, new_e, e);
    }
    return visit(proj_app, expected_type);
}

class reduce_projections_visitor : public replace_visitor {
private:
    type_context_old & m_ctx;
protected:
    expr visit_app(expr const & e) override {
        expr e2 = replace_visitor::visit_app(e);
        if (has_metavar(e2)) {
            if (auto e3 = m_ctx.reduce_projection(e2))
                return *e3;
        }
        return e2;
    }
public:
    reduce_projections_visitor(type_context_old & ctx): m_ctx(ctx) {}
};

/* Predicated variant of `lean::instantiate_mvars`. It does not support universe mvars. */
expr elaborator::instantiate_mvars(expr const & e, std::function<bool(expr const &)> pred) { // NOLINT
    return replace(e, [&](expr const & e) {
        if (m_ctx.is_mvar(e) && pred(e))
            if (auto asn = m_ctx.get_assignment(e))
                return some_expr(instantiate_mvars(*asn, pred));
        return none_expr();
    });
}

/** Elaborate the structure instance notation `{... := ..., ...}` */
class visit_structure_instance_fn {
    // an elaborated source `..(m_e : m_S_name ...)`
    struct source {
        expr m_e;
        // known to be a structure
        name m_S_name;
    };

    elaborator & m_elab;
    // note: fields needed by trace macros
    environment & m_env = m_elab.m_env;
    type_context_old & m_ctx = m_elab.m_ctx;

    // inputs
    expr m_e, m_ref = m_e;
    optional<expr> m_expected_type;
    bool m_use_subobjects = !m_elab.m_opts.get_bool("old_structure_cmd", false);
    structure_instance_info m_info = get_structure_instance_info(m_e);
    name & m_S_name = m_info.m_struct_name;
    buffer<name> const & m_fnames = m_info.m_field_names;
    buffer<expr> const & m_fvalues = m_info.m_field_values;

    // set of fnames that have been used by `create_field_mvars`. Not using all of them is an error.
    name_set m_fnames_used;
    // fields for which no value could be found
    buffer<name> m_missing_fields;
    // elaborated sources
    buffer<source> m_sources;

    /* Because field default values may introduce arbitrary dependencies on other field values (not only within a structure,
     * but even between a structure and its parent structures, in either direction), we cannot elaborate fields in a static
     * order. Instead, we register a metavar and an elaboration function for each field (create_field_mvars).
     * We call the elaboration function and substitute the metavar with its result (insert_field_values)
     * only after all field metavars in its expected type have been resolved (reduce_and_check_dependencies). */

    // field -> elaboration function
    name_map<std::function<expr(expr const & expected_type)>> m_field2elab;
    // field <-> metavar for each field to be elaborated
    name_map<expr> m_field2mvar;
    name_map<name> m_mvar2field;

    bool field_from_source(name const & S_fname) {
        for (source const & src : m_sources) {
            if (optional<name> base_S_name = find_field(m_env, src.m_S_name, S_fname)) {
                expr base_src = *mk_base_projections(m_env, src.m_S_name, *base_S_name, src.m_e);
                expr f = mk_proj_app(m_env, *base_S_name, S_fname, base_src);
                m_field2elab.insert(S_fname, [=](expr const & d) {
                    return m_elab.visit(f, some_expr(d));
                });
                return true;
            }
        }
        return false;
    }

    struct field_not_ready_to_synthesize_exception : exception {
        std::function<format()> m_fmt;
        explicit field_not_ready_to_synthesize_exception(std::function<format()> m_fmt) : m_fmt(m_fmt) {}
    };

    void field_from_default_value(name const & S_fname) {
        m_field2elab.insert(S_fname, [=](expr const & d) {
            if (m_elab.m_in_pattern) {
                // insert placeholder during pattern elaboration
                return m_elab.mk_metavar(d, m_ref);
            } else {
                name full_S_fname = m_S_name + S_fname;
                expr pre_fval = mk_field_default_value(m_env, full_S_fname, [&](name const & fname) {
                    // just insert mvars for now, we will check for any uninstantiated ones in `reduce_and_check_deps` below
                    return m_field2mvar[fname];
                });
                expr fval = m_elab.visit(pre_fval, some_expr(d));
                /* Delta- and beta-reduce `_default` definition. This can remove dependencies when defaulting
                 * a field of a parent structure.
                 * For example, monad defaults applicative.seq in terms of map and bind. However, since map is part
                 * of the subobject to_applicative as well, we get the recursive constraint
                 * `?seq =?= monad.seq._default {to_functor := {map := ?map, ...}, seq := ?seq, ...} ?bind ...`
                 * Reducing monad.seq._default allows `reduce_and_check_deps` below to remove the ?seq dependency. */
                buffer<expr> args;
                expr fn = get_app_args(fval, args);
                if (is_constant(fn)) {
                    constant_info decl = m_env.get(const_name(fn));
                    expr default_val = instantiate_value_lparams(decl, const_levels(fn));
                    // clean up 'id' application inserted by `structure_cmd::declare_defaults`
                    default_val = replace(default_val, [](expr const & e) {
                        if (is_app_of(e, get_id_name(), 2)) {
                            return some_expr(app_arg(e));
                        }
                        return none_expr();
                    });
                    fval = mk_app(default_val, args);
                    fval = head_beta_reduce(fval);
                }
                reduce_and_check_deps(fval, full_S_fname);
                return fval;
            }
        });
    }

    /** Recurse over structure hierarchy and build structure expression, introducing mvars for each parameter and
        leaf field.

        Example: `create_field_mvars('applicative') =
                    (applicative.mk ?p1 (functor.mk ?p2 ?f1 ?f2...) ?f3..., applicative ?p1)` */
    std::pair<expr, expr> create_field_mvars(name const & nested_S_name) {
        buffer<name> c_names;
        get_constructor_names(m_env, nested_S_name, c_names);
        lean_assert(c_names.size() == 1);
        expr c = m_elab.visit_const_core(copy_pos(m_e, mk_constant(c_names[0])));
        buffer<expr> c_args;
        expr c_type = m_elab.infer_type(c);
        unsigned nparams = m_env.get(nested_S_name).to_inductive_val().get_nparams();

        // iterate over nested_S_name's constructor parameters
        for (unsigned i = 0; is_pi(c_type); i++) {
            name S_fname = deinternalize_field_name(binding_name(c_type));
            expr c_arg;
            expr d = binding_domain(c_type);

            if (i < nparams) {
                /* struct type parameter */
                if (is_explicit(binding_info(c_type)) && !m_expected_type) {
                    m_elab.report_or_throw(elaborator_exception(m_e, sstream()
                            << "invalid structure value {...}, structure parameter '" <<
                            binding_name(c_type)
                            << "' is explicit in the structure constructor '" <<
                            c_names[0] << "' and the expected type is not known"));
                }
                c_arg = m_elab.mk_metavar(d, m_ref);
            } else {
                /* struct field */
                c_arg = m_elab.mk_metavar(S_fname, d, m_ref);

                /* Try to find field value, in the following order:
                 * 1) explicit value from m_fvalues
                 * 2) subobject field: recurse
                 * 3) value from source
                 * 4) opt/auto/implicit param
                 * 6) `..` catchall: placeholder
                 */
                auto it = std::find(m_fnames.begin(), m_fnames.end(), S_fname);
                if (it != m_fnames.end()) {
                    /* explicitly passed field */
                    m_fnames_used.insert(S_fname);
                    expr const & p = m_fvalues[it - m_fnames.begin()];
                    m_field2elab.insert(S_fname, [=](expr const & d) {
                        return m_elab.visit(p, some_expr(consume_auto_opt_param(d)));
                    });
                } else if (auto p = is_subobject_field(m_env, nested_S_name, S_fname)) {
                    /* subobject field */
                    auto num_used = m_fnames_used.size();
                    auto old_missing_fields = m_missing_fields;
                    auto nested = create_field_mvars(*p);
                    if (m_fnames_used.size() == num_used && field_from_source(S_fname)) {
                        // If the subobject doesn't contain any explicitly passed fields, we prefer to use
                        // its value directly from a source so that the two are definitionally equal
                    } else if (!is_explicit(binding_info(c_type)) && m_fnames_used.size() == num_used &&
                            old_missing_fields.size() < m_missing_fields.size()) {
                        // If the subobject is a superclass, doesn't contain any explicitly passed fields,
                        // and has missing fields, we fall back to type inference
                        m_field2elab.insert(S_fname, [=](expr const & d) {
                            return m_elab.mk_instance(d, m_ref);
                        });
                        m_missing_fields = old_missing_fields;
                    } else {
                        // We assign the subtree to the mvar eagerly so that the mvars representing the nested
                        // structure parameters are assigned, which are not inlcuded in the m_mvar2field dependency
                        // tracking
                        lean_always_assert(m_elab.is_def_eq(c_arg, nested.first));
                        // should always hold because `nested.first` is a constructor application
                        lean_always_assert(m_elab.is_mvar_assigned(c_arg));
                    }
                } else if (field_from_source(S_fname)) {
                } else if (has_default_value(m_env, m_S_name, S_fname)) { // note: S_name instead of nested_S_name
                    field_from_default_value(S_fname);
                } else if (is_auto_param(d)) {
                    /* auto param */
                    m_field2elab.insert(S_fname, [=](expr const & d) {
                        if (m_elab.m_in_pattern) {
                            // insert placeholder during pattern elaboration
                            return m_elab.mk_metavar(d, m_ref);
                        } else {
                            auto p = is_auto_param(d);
                            return m_elab.mk_auto_param(p->second, p->first, m_ref);
                        }
                    });
                } else if (!is_explicit(binding_info(c_type))) {
                    /* implicit field */
                    m_field2elab.insert(S_fname, [=](expr const & d) {
                        return is_inst_implicit(binding_info(c_type)) ? m_elab.mk_instance(d, m_ref) : m_elab.mk_metavar(d, m_ref);
                    });
                } else if (m_info.m_catchall) {
                    /* catchall: insert placeholder */
                    m_field2elab.insert(S_fname, [=](expr const & d) {
                        return m_elab.mk_metavar(d, m_ref);
                    });
                } else {
                    /* failure */
                    // Do not log an error immediately because subobjects may need backtracking
                    m_missing_fields.push_back(S_fname);
                    m_field2elab.insert(S_fname, [=](expr const & d) {
                        return m_elab.mk_sorry(some_expr(d), m_ref);
                    });
                }

                m_field2mvar.insert(S_fname, c_arg);
                m_mvar2field.insert(mvar_name(c_arg), S_fname);
            }

            c_args.push_back(c_arg);
            c_type = instantiate(binding_body(c_type), c_arg);
        }
        return mk_pair(mk_app(c, c_args), c_type);
    }

    /** Check `e` for dependencies on fields that have not been inserted yet.
     * Also reduce projections containing mvars, which may remove dependencies.
     * Example: `functor.map (functor.mk ?p1 ?m1 ?m2...) => ?m1`
     */
    void reduce_and_check_deps(expr & e, name const & full_S_fname) {
        if (m_use_subobjects)
            e = reduce_projections_visitor(m_ctx)(e);
        name_set deps;
        e = m_elab.instantiate_mvars(e);
        for_each(e, [&](expr const & e, unsigned) {
            name const *n;
            if (is_metavar(e) && (n = m_mvar2field.find(mvar_name(e))) && !m_ctx.is_assigned(e))
                deps.insert(*n);
            return has_expr_metavar(e);
        });
        if (!deps.empty()) {
            throw field_not_ready_to_synthesize_exception([=]() {
                format error = format("Failed to insert value for '") + format(full_S_fname) +
                               format("', it depends on field(s) '");
                bool first = true;
                deps.for_each([&](name const & dep) {
                    if (!first) error += format("', '");
                    error += format(dep);
                    first = false;
                });
                error += format("', but the value for these fields is not available.") + line() +
                         format("Unfolded type/default value:") + line() +
                         pp_until_meta_visible(m_elab.mk_fmt_ctx(), e) + line() +
                         line();
                return error;
            });
        }
    }

    void elaborate_sources() {
        for (expr src : m_info.m_sources) {
            lean_assert(!m_elab.m_in_pattern);
            src = m_elab.visit(src, none_expr());
            m_elab.synthesize_type_class_instances();
            expr type = m_elab.instantiate_mvars(m_elab.whnf(m_elab.infer_type(src)));
            expr src_S = get_app_fn(type);
            if (!is_constant(src_S) || !is_structure(m_env, const_name(src_S))) {
                auto pp_fn = m_elab.mk_pp_ctx();
                m_elab.report_or_throw(elaborator_exception(m_e,
                                                            format("invalid structure notation source, not a structure") +
                                                            m_elab.pp_indent(pp_fn, src) +
                                                            line() + format("which has type") +
                                                            m_elab.pp_indent(pp_fn, type)));
            } else {
                m_sources.push_back(source {copy_pos(src, mk_as_is(src)), const_name(src_S)});
            }
        }
    }

    void find_structure_name() {
        if (m_expected_type) {
            expr type = m_elab.whnf(*m_expected_type);
            expr S = get_app_fn(type);
            if (!is_constant(S) || !is_structure(m_env, const_name(S))) {
                auto pp_fn = m_elab.mk_pp_ctx();
                throw elaborator_exception(m_e,
                                           format("invalid structure value {...}, expected type is known, "
                                                          "but it is not a structure") +
                                           m_elab.pp_indent(pp_fn, *m_expected_type));
            }
            m_S_name = const_name(S);
        } else if (m_sources.size() == 1 && !m_info.m_catchall) {
            m_S_name = m_sources[0].m_S_name;
        } else {
            throw elaborator_exception(m_e, "invalid structure value {...}, expected type is not known"
                    "(solution: use qualified structure instance { struct_id . ... }");
        }
    }

    /** Repeatedly try to elaborate fields whose dependencies have been elaborated.
      * If we have not made any progress in a round, do a last one collecting any errors. */
    void insert_field_values(expr const & e) {
        bool done = false;
        bool last_progress = true;

        while (!done) {
            done = true;
            bool progress = false;
            format error;
            // Try to resolve helper metavars reachable from e. Note that `m_mvar2field` etc. may contain
            // metavars unreachable from e because of backtracking.
            expr e2 = m_elab.instantiate_mvars(e);
            for_each(e2, [&](expr const & e, unsigned) {
                if (is_metavar(e) && m_mvar2field.contains(mvar_name(e))) {
                    name S_fname = m_mvar2field[mvar_name(e)];
                    name full_S_fname = m_S_name + S_fname;
                    expr expected_type = m_elab.infer_type(e);
                    expr reduced_expected_type = m_elab.instantiate_mvars(expected_type);
                    expr val;

                    try {
                        reduce_and_check_deps(reduced_expected_type, full_S_fname);
                        /* note: we pass the reduced, mvar-free expected type. Otherwise auto params may fail with
                         * "result contains meta-variables". */
                        val = (*m_field2elab.find(S_fname))(reduced_expected_type);
                    } catch (field_not_ready_to_synthesize_exception const & e) {
                        done = false;
                        if (!last_progress)
                            error += e.m_fmt();
                        return true;
                    }

                    expr val_type = m_elab.infer_type(val);
                    if (auto val2 = m_elab.ensure_has_type(val, val_type, expected_type, m_ref)) {
                        /* Make sure mvar is assigned, even if val2 is a meta var as well.
                         * This is important for termination and the `instantiate_mvars` call in `operator()`.
                         * Note that `ensure_has_type` has already unified their types, so this should not result
                         * in any missed unifications.
                         */
                        lean_always_assert(m_ctx.match(e, *val2));
                        trace_elab_detail(tout() << "inserted field '" << S_fname << "' with value '" << *val2 << "'"
                                                 << "\n";)
                        progress = true;
                    } else {
                        format msg = format("type mismatch at field '") + format(S_fname) + format("'");
                        msg += m_elab.pp_type_mismatch(val, val_type, expected_type);
                        throw elaborator_exception(val, msg);
                    }
                }
                return has_metavar(e);
            });
            if (!last_progress && !progress)
                throw elaborator_exception(m_ref, error);
            last_progress = progress;
        }
    }
public:
    visit_structure_instance_fn(elaborator & m_elab, expr const & e, optional<expr> const & expected_type) :
            m_elab(m_elab), m_e(e), m_expected_type(expected_type) {}

    expr operator()() {
        if (!m_S_name.is_anonymous() && !is_structure(m_elab.env(), m_S_name))
            throw elaborator_exception(m_e, sstream() << "invalid structure instance, '" <<
                                                    m_S_name << "' is not the name of a structure type");
        lean_assert(m_fnames.size() == m_fvalues.size());

        elaborate_sources();

        if (m_S_name.is_anonymous())
            find_structure_name();

        if (is_private(m_S_name) && !is_expr_aliased(m_env, m_S_name))
            throw elaborator_exception(m_e, "invalid structure instance, type is a private structure");

        expr e2, c_type;
        std::tie(e2, c_type) = create_field_mvars(m_S_name);

        /* Report missing fields. */
        for (name const & S_fname : m_missing_fields) {
            m_elab.report_or_throw(elaborator_exception(m_e, sstream() << "invalid structure value { ... }, field '"
                                                                       << S_fname << "' was not provided"));
        }

        /* Check if there are alien fields. */
        for (name const & fname : m_fnames) {
            if (!m_fnames_used.contains(fname)) {
                m_elab.report_or_throw(
                        elaborator_exception(m_e, sstream() << "invalid structure value { ... }, '" << fname << "'"
                                                          << " is not a field of structure '" << m_S_name << "'"));
            }
        }

        /* Make sure to unify first to propagate the expected type, we'll report any errors later on. */
        bool type_def_eq = !m_expected_type || m_elab.is_def_eq(*m_expected_type, c_type);

        insert_field_values(e2);

        /* Check expected type */
        if (!type_def_eq) {
            throw elaborator_exception(m_ref, format("type mismatch as structure instance") +
                                            m_elab.pp_type_mismatch(e2, c_type, *m_expected_type));
        }

        if (m_elab.m_in_pattern) {
            /* Instantiate all helper mvars introduced by this function. This is important when elaborating patterns because
             * all mvars left in the final expression are turned into pattern variables by `visit_equation` (see there).
             * For example, the pattern `{a := a}` will result in the input `m_e = {a := ?a}` and result `e2 = foo.mk ?m` with
             * the assignment `?m := ?a` from field elaboration. We want the return value to be `foo.mk ?a` regardless of
             * whether ?a has an assignment (from a dependent pattern) or not. */
            e2 = m_elab.instantiate_mvars(e2, [&](expr const & e) { return m_mvar2field.contains(mvar_name(e)); });
        }
        return e2;
    }
};

expr elaborator::visit_structure_instance(expr const & e, optional<expr> expected_type) {
    synthesize_type_class_instances();
    if (expected_type) {
        expected_type = instantiate_mvars(*expected_type);
        if (is_metavar(*expected_type))
            expected_type = none_expr();
    }
    return visit_structure_instance_fn(*this, e, expected_type)();
}

expr elaborator::visit_node_macro(expr const & e, optional<expr> const & expected_type) {
    name macro = *get_name(mdata_data(e), "node!");
    name esc_macro = macro.is_atomic() ? "«" + macro.to_string() + "»" : macro;
    expr e2 = mdata_expr(e);
    expr macro_e = app_arg(app_fn(e2));
    name full_macro = const_name(macro_e);
    if (!expected_type)
        throw elaborator_exception(e, "node!: expected type must be known");
    expr exp = expected_type.value();
    sstream params, args, struc, binds, mk_args, view_pat, reviews, default_val;
    unsigned i = 0;
    collected_locals ls;
    collect_locals(e2, ls);
    for (auto const & p : ls.get_collected()) {
        params << "(" << local_pp_name_p(p) << " : " << instantiate_mvars(infer_type(p)) << ")";
        args << " " << local_pp_name_p(p);
    }
    struc << "@[pattern] def " << esc_macro.to_string() << " " << params.str();
    struc << " := {SyntaxNodeKind . name := `" << full_macro.to_string() << "}\n"
            << "structure " << macro.to_string() << ".View :=\n";
    buffer<expr> new_args;
    // unhygiene when nested in namespaces
    auto opts = options().update({"pp", "full_names"}, true);
    auto pp = ::lean::mk_pp_ctx(m_env, opts, m_ctx.mctx(), m_ctx.lctx());
    for (expr args = app_arg(e2); is_app(args); args = app_arg(args)) {
        expr r = app_arg(app_fn(args));
        std::function<expr(expr)> add_field;
        add_field = [&](expr r) {
            name fname = *get_name(mdata_data(r), "fname");
            r = mdata_expr(r);
            r = visit(r, expected_type);
            if (expected_type)
                r = enforce_type(r, *expected_type, "type mismatch", r);
            synthesize_type_class_instances();
            auto m = mk_metavar(mk_Type(), r);
            auto inst = m_ctx.mk_class_instance(mk_app(mk_const(name{"Lean", "Parser", "HasView"}), exp, m, r));
            if (!inst)
                throw elaborator_exception(e, sstream() << "Could not infer instance of Parser.HasView for '" << r
                                                        << "'");
            auto m2 = mk_metavar(m, r);
            auto defval_inst = m_ctx.mk_class_instance(
                    mk_app(mk_app(mk_const(name{"Lean", "Parser", "HasViewDefault"}), exp, r, m), *inst, m2));
            if (defval_inst)
                struc << "(«" << fname << "» : " << instantiate_mvars(m) << " := " << pp(instantiate_mvars(m2)) << ")\n";
            else
                struc << "(«" << fname << "» : " << instantiate_mvars(m) << ")\n";

            binds << "let (stxs, stx) := match stxs : _ -> Prod (List Syntax) Syntax with (stx::stxs) := (stxs, stx) | _ := (stxs, Syntax.missing) in\n"
            << "let a" << i << " := Parser.HasView.view (" << pp(r) << " : " << pp(exp) << ")" << " stx in\n";
            mk_args << "a" << i << " ";
            if (i != 0)
                view_pat << ", ";
            view_pat << "a" << i;
            if (i != 0)
                reviews << ", ";
            reviews << "review (" << pp(r) << " : " << pp(exp) << ") a" << i;
            i++;
            return mk_as_is(r);
        };
        if (is_mdata(r)) {
            new_args.push_back(add_field(r));
        } else {// try block
            binds << "let stxs := match stxs with stx::stxs := (match stx.asNode with some n := n.args ++ stxs | _ := stxs) | _ := stxs in\n";
            reviews << "Syntax.list [";
            buffer<expr> new_try_args;
            for (expr args = app_arg(app_arg(r)); is_app(args); args = app_arg(args)) {
                expr r = app_arg(app_fn(args));
                new_try_args.push_back(add_field(r));
            }
            reviews << "]";
            new_args.push_back(mk_app(mk_const({"Lean", "Parser", "MonadParsec", "try"}),
                                      mk_app(mk_const({"Lean", "Parser", "Combinators", "seq"}),
                                             mk_lean_list(new_try_args))));
        }
    }
    struc << "def " << macro.to_string() << ".HasView' " << params.str() << " : HasView " << macro.to_string() << ".View (" << esc_macro.to_string() << args.str() << ") :=\n"
            << "{ view := fun stx, let stxs : List Syntax := match stx.asNode with"
            << "| some n := n.args | _ := [] in\n"
            << binds.str()
            << macro.to_string() << ".View.mk " << mk_args.str() << ",\n"
            << "review := fun ⟨" << view_pat.str() << "⟩, Syntax.mkNode " << esc_macro.to_string() << " [" << reviews.str() << "] }";
    struc << "instance " << macro.to_string() << ".HasView  := @" << macro.to_string() << ".HasView'";
    trace_elab_detail(tout() << "expansion of node! macro:\n" << struc.str(););
    std::istringstream in(struc.str());
    parser p(m_env, get_global_ios(), in, get_pos_info_provider()->get_file_name());
    p.set_imports_parsed();
    p.parse_command_like();
    p.parse_command_like();
    p.parse_command_like();
    p.parse_command_like();
    m_env = p.env();
    m_ctx.set_env(m_env);
    return visit(mk_app(mk_const({"Lean", "Parser", "Combinators", "node"}), mk_const(get_namespace(p.env()) + macro), mk_lean_list(new_args)),
                 expected_type);
}

expr elaborator::visit_node_choice_macro(expr const & e, bool longest_match, optional<expr> const & expected_type) {
    name macro = *get_name(mdata_data(e), longest_match ? "nodeLongestChoice!" : "nodeChoice!");
    name esc_macro = macro.is_atomic() ? "«" + macro.to_string() + "»" : macro;
    expr args = mdata_expr(e);
    name full_macro = get_namespace(m_env) + macro;
    if (!expected_type)
        throw elaborator_exception(e, "nodeChoice!: expected type must be known");
    expr exp = expected_type.value();
    sstream params, pargs, struc, default_view_case, view_cases, review_cases;
    unsigned i = 0;
    collected_locals ls;
    collect_locals(e, ls);
    for (auto const & p : ls.get_collected()) {
        params << "(" << local_pp_name_p(p) << " : " << instantiate_mvars(infer_type(p)) << ")";
        pargs << " " << local_pp_name_p(p);
    }
    struc << "@[pattern] def " << esc_macro.to_string() << " " << params.str();
    struc << " := {SyntaxNodeKind . name := `" << full_macro.to_string() << "}\n"
          << "inductive " << macro.to_string() << ".View\n";
    buffer<expr> new_args;
    // unhygiene when nested in namespaces
    auto opts = options().update({"pp", "full_names"}, true);
    auto pp = ::lean::mk_pp_ctx(m_env, opts, m_ctx.mctx(), m_ctx.lctx());
    for (expr e = args; is_app(e); e = app_arg(e)) {
        expr r = app_arg(app_fn(e));
        std::string fname = "«" + get_name(mdata_data(r), "fname")->to_string() + "»";
        r = mdata_expr(r);
        auto m = mk_metavar(mk_Type(), r);
        r = visit(r, expected_type);
        synthesize_type_class_instances();
        auto inst = m_ctx.mk_class_instance(mk_app(mk_const(name{"Lean", "Parser", "HasView"}), exp, m, r));
        if (!inst)
            throw elaborator_exception(e, sstream() << "Could not infer instance of Parser.HasView for '" << instantiate_mvars(r)
                                                    << "'");
        auto m2 = mk_metavar(m, r);
        auto defval_inst = m_ctx.mk_class_instance(
                mk_app(mk_app(mk_const(name{"Lean", "Parser", "HasViewDefault"}), exp, r, m), *inst, m2));
        if (defval_inst)
            struc << "| " << fname << " : optParam (" << instantiate_mvars(m) << ") ("
                    << pp(instantiate_mvars(m2)) << ") -> " << macro.to_string() << ".View\n";
        else
            struc << "| " << fname << " : " << instantiate_mvars(m) << " -> " << macro.to_string() << ".View\n";

        view_cases << "| ";
        if (is_app(app_arg(e)))
            view_cases << i;
        else
            view_cases << "_";
        view_cases << " := " << macro.to_string() << ".View." << fname << " $ Parser.HasView.view (" << pp(r)
                << " : " << pp(exp) << ") stx\n";
        review_cases << "| " << macro.to_string() << ".View." << fname << " a := "
                << "Syntax.mkNode (SyntaxNodeKind.mk (Name.mkNumeral Name.anonymous " << i << ")) "
                << "[review (" << pp(r) << " : " << pp(exp) << ") a]\n";
        i++;
        new_args.push_back(mk_as_is(r));
    }
    struc << "def " << macro.to_string() << ".HasView' " << params.str() << " : HasView " << macro.to_string() << ".View ("
          << esc_macro.to_string() << " " << pargs.str() << ") :=\n"
          << "{ view := fun stx, let (stx, i) := match stx.asNode : _ -> Prod Syntax Nat with\n"
          << "| some {kind := @" << esc_macro.to_string() << " " << pargs.str() << ", args := [stx], ..} := (match stx.asNode  : _ -> Prod Syntax Nat with\n"
          << "  | some {kind := SyntaxNodeKind.mk (Name.mkNumeral Name.anonymous i), args := [stx], ..} := (stx, i)\n"
          << "  | _ := (Syntax.missing, 0))\n"
          << "| _ := (Syntax.missing, 0) in\n"
          << "match i with\n"
          << view_cases.str() << ",\n"
          << "review := fun v, Syntax.mkNode (" << esc_macro.to_string() << " " << pargs.str() << ")"
          << " [match v with\n"
          << review_cases.str()
          << "] }";
    struc << "instance " << macro.to_string() << ".HasView := @" << macro.to_string() << ".HasView'";
    trace_elab_detail(tout() << "expansion of nodeChoice! macro:\n" << struc.str(););
    std::istringstream in(struc.str());
    parser p(m_env, get_global_ios(), in, "foo");
    p.set_imports_parsed();
    p.parse_command_like();
    p.parse_command_like();
    p.parse_command_like();
    p.parse_command_like();
    m_env = p.env();
    m_ctx.set_env(m_env);
    return visit(mk_app(mk_const({"Lean", "Parser", "Combinators", "node"}),
                        mk_const(full_macro),
                        mk_app(mk_const({"List", "cons"}),
                               mk_app(mk_const({"Lean", "Parser", "Combinators", longest_match ? "longestChoice" : "choice"}),
                                      mk_lean_list(new_args)),
                               mk_const({"List", "nil"}))), expected_type);
}

expr elaborator::visit_mdata(expr const & e, optional<expr> const & expected_type, bool is_app_fn) {
    if (is_as_is(e)) {
        return get_as_is_arg(e);
    } else if (is_choice(e)) {
        return visit_app_core(e, buffer<expr>(), expected_type, e);
    } else if (is_explicit(e) || is_partial_explicit(e)) {
        return visit_app_core(e, buffer<expr>(), expected_type, e);
    } else if (is_anonymous_constructor(e)) {
        if (is_app_fn)
            throw elaborator_exception(e, "invalid constructor ⟨...⟩, function expected");
        return visit_anonymous_constructor(e, expected_type);
    } else if (is_as_atomic(e)) {
        /* ignore annotation */
        expr new_e = visit(get_as_atomic_arg(e), none_expr());
        if (is_app_fn)
            return new_e;
        /* If the as_atomic is not the the function in a function application, then we need to consume
           implicit arguments. */
        return visit_base_app_core(new_e, arg_mask::Default, buffer<expr>(), true, expected_type, e);
    } else if (is_inaccessible(e)) {
        if (is_app_fn)
            throw elaborator_exception(e, "invalid inaccessible term, function expected");
        return visit_inaccessible(e, expected_type);
    } else if (is_frozen_name(e)) {
        return visit(get_annotation_arg(e), expected_type);
    } else if (is_structure_instance(e)) {
        return visit_structure_instance(e, expected_type);
    } else if (is_field_notation(e)) {
        return visit_field(e, expected_type);
    } else if (is_as_pattern(e)) {
        if (!m_in_pattern)
            throw elaborator_exception(e, "invalid occurrence of aliasing pattern, it must only occur in patterns");
        expr new_rhs = visit(get_as_pattern_rhs(e), expected_type);
        expr lhs = get_as_pattern_lhs(e);
        if (!is_def_eq(lhs, new_rhs))
            throw elaborator_exception(e, "cannot unify terms of aliasing pattern");
        return new_rhs;
    } else if (is_equation(e)) {
        throw elaborator_exception(e, "unexpected occurrence of equation");
    } else if (is_equations(e)) {
        lean_assert(!is_app_fn); // visit_convoy is used in this case
        return visit_equations(e);
    } else if (get_name(mdata_data(e), "node!")) {
        return visit_node_macro(e, expected_type);
    } else if (get_name(mdata_data(e), "nodeChoice!")) {
        return visit_node_choice_macro(e, false, expected_type);
    } else if (get_name(mdata_data(e), "nodeLongestChoice!")) {
        return visit_node_choice_macro(e, true, expected_type);
    } else {
        expr new_e = visit(mdata_expr(e), expected_type);
        return update_mdata(e, new_e);
    }
}

/* If the instance fingerprint has been set, then make sure `type` is not a local instance.
   Then, add a new local declaration to locals. */
expr elaborator::push_local(type_context_old::tmp_locals & locals,
                            name const & n, expr const & type, binder_info binfo, expr const & /* ref */) {
#if 0 // TODO(Leo): the following check is too restrictive
    if (m_ctx.lctx().get_instance_fingerprint() &&
        m_ctx.is_class(type)) {
        throw elaborator_exception(ref, "invalid occurrence of local instance, it must be a declaration parameter");
    }
#endif
    return locals.push_local(n, type, binfo);
}

/* See method above */
expr elaborator::push_let(type_context_old::tmp_locals & locals,
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
    type_context_old::tmp_locals locals(m_ctx);
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
        expr l     = push_local(locals, binding_name(it), new_d, binding_info(it), ref_d);
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
    type_context_old::tmp_locals locals(m_ctx);
    expr it  = e;
    expr parent_it = e;
    while (is_pi(it)) {
        expr d     = instantiate_rev_locals(binding_domain(it), locals);
        expr new_d = visit(d, none_expr());
        expr ref_d = get_ref_for_child(binding_domain(it), it);
        new_d      = ensure_type(new_d, ref_d);
        expr ref   = binding_domain(it);
        expr l     = push_local(locals, binding_name(it), new_d, binding_info(it), ref);
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
    synthesize();
    expr new_value = visit(let_value(e), some_expr(new_type));
    expr ref_value = get_ref_for_child(let_value(e), ref);
    new_value      = enforce_type(new_value, new_type, "invalid let-expression", ref_value);
    synthesize();
    new_type       = instantiate_mvars(new_type);
    new_value      = instantiate_mvars(new_value);
    ensure_no_unassigned_metavars(new_value);
    type_context_old::tmp_locals locals(m_ctx);
    expr l = push_let(locals, let_name(e), new_type, new_value, ref);
    expr body      = instantiate_rev_locals(let_body(e), locals);
    expr new_body  = visit(body, expected_type);
    synthesize();
    expr new_e     = locals.mk_lambda(new_body);
    return new_e;
}

expr elaborator::visit_placeholder(expr const & e, optional<expr> const & expected_type) {
    expr const & ref = e;
    return mk_metavar(expected_type, ref);
}

static bool is_have_expr(expr const & e) {
    return is_app(e) && is_have_annotation(unwrap_pos(app_fn(e)));
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
    expr lambda     = unwrap_pos(get_annotation_arg(app_fn(e)));
    expr type       = binding_domain(lambda);
    expr proof      = app_arg(e);
    expr new_type   = visit(type, none_expr());
    synthesize();
    new_type        = ensure_type(new_type, type);
    expr new_proof  = visit(proof, some_expr(new_type));
    new_proof       = enforce_type(new_proof, new_type, "invalid have-expression", proof);
    synthesize();
    ensure_no_unassigned_metavars(new_proof);
    type_context_old::tmp_locals locals(m_ctx);
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
    expr fn   = unwrap_pos(app_fn(body));
    expr rest = app_arg(body);
    if (!is_lambda(fn)) throw elaborator_exception(e, "ill-formed suffices expression");
    expr new_fn;
    expr type     = binding_domain(fn);
    expr new_type = visit(type, none_expr());
    synthesize();
    {
        type_context_old::tmp_locals locals(m_ctx);
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

static expr mk_emptyc(expr const & src) {
    return copy_pos(src, mk_app(copy_pos(src, mk_constant(get_has_emptyc_emptyc_name())),
                                copy_pos(src, mk_expr_placeholder())));
}

expr elaborator::visit_emptyc_or_emptys(expr const & e, optional<expr> const & expected_type) {
    if (!expected_type) {
        return visit(mk_emptyc(e), expected_type);
    } else {
        synthesize_type_class_instances();
        expr new_expected_type = instantiate_mvars(*expected_type);
        if (is_optional_param(new_expected_type))
            new_expected_type = app_arg(app_fn(new_expected_type));
        expr S = get_app_fn(new_expected_type);
        if (is_constant(S) && is_structure(m_env, const_name(S))) {
            expr empty_struct = copy_pos(e, mk_structure_instance(name(), buffer<name>(), buffer<expr>()));
            return visit(empty_struct, expected_type);
        } else {
            return visit(mk_emptyc(e), expected_type);
        }
    }
}

expr elaborator::visit(expr const & e, optional<expr> const & expected_type) {
    flet<unsigned> inc_depth(m_depth, m_depth+1);
    trace_elab_detail(tout() << "[" << m_depth << "] visiting\n" << e << "\n";
                      if (expected_type) tout() << "expected type:\n" << instantiate_mvars(*expected_type) << "\n";);
    expr e2 = recover_expr_from_exception(expected_type, e, [&] () -> expr {
        if (auto p = get_pos(e)) {
            flet<optional<pos_info>> _(m_last_pos, p);
            return visit(unwrap_pos(e), expected_type);
        } else if (is_placeholder(e)) {
            return visit_placeholder(e, expected_type);
        } else if (is_typed_expr(e)) {
            return visit_typed_expr(e);
        } else if (is_have_expr(e)) {
            return copy_pos(e, visit_have_expr(e, expected_type));
        } else if (is_suffices_annotation(e)) {
            return copy_pos(e, visit_suffices_expr(e, expected_type));
        } else if (is_no_info(e)) {
            flet<bool> set(m_no_info, true);
            return visit(get_annotation_arg(e), expected_type);
        } else if (is_emptyc_or_emptys(e)) {
            return visit_emptyc_or_emptys(e, expected_type);
        } else if (is_sort_wo_universe(e)) {
            return visit(get_annotation_arg(e), expected_type);
        } else {
            switch (e.kind()) {
                case expr_kind::BVar: lean_unreachable();  // LCOV_EXCL_LINE
                case expr_kind::MVar:
                    return e;
                case expr_kind::Lit:
                    switch (lit_value(e).kind()) {
                    case literal_kind::Nat:
                        return visit_prenum(e, expected_type);
                    case literal_kind::String:
                        return e;
                    }
                    lean_unreachable();
                case expr_kind::MData:
                    return visit_mdata(e, expected_type, false);
                case expr_kind::Proj:
                    throw elaborator_exception(e, "unexpected occurrence of proj constructor");
                case expr_kind::Sort:
                    return visit_sort(e);
                case expr_kind::FVar:
                    return visit_local(e, expected_type);
                case expr_kind::Const:
                    return visit_constant(e, expected_type);
                case expr_kind::Lambda:
                    return visit_lambda(e, expected_type);
                case expr_kind::Pi:
                    return visit_pi(e);
                case expr_kind::App:
                    return visit_app(e, expected_type);
                case expr_kind::Let:
                    return visit_let(e, expected_type);
            }
            lean_unreachable(); // LCOV_EXCL_LINE
        }
    });
    return e2;
}

expr elaborator::get_default_numeral_type() {
    // TODO(Leo): allow user to modify default?
    return mk_constant(get_nat_name());
}

void elaborator::synthesize_numeral_types() {
    for (expr const & A : m_numeral_types) {
        trace_elab_numeral(tout() << "synthesize num type: " << A << ", " << instantiate_mvars(A) << "\n";);
        if (is_metavar_app(instantiate_mvars(A))) {
            if (!is_def_eq(A, get_default_numeral_type()))
                report_or_throw(elaborator_exception(A, "invalid numeral, failed to force numeral to be a nat"));
        }
    }
    m_numeral_types = list<expr>();
}

bool elaborator::synthesize_type_class_instance_core(expr const & mvar, expr const & inferred_inst, expr const & inst_type) {
    if (!ready_to_synthesize(inst_type))
        return false;
    metavar_decl mdecl = m_ctx.mctx().get_metavar_decl(mvar);
    expr ref = mvar;
    expr synthesized_inst = mk_instance_core(mdecl.get_context(), inst_type, ref);
    trace_elab_instances(tout() << inferred_inst << " =?= " << synthesized_inst << "\n";);
    if (!m_ctx.is_def_eq_at(mdecl.get_context(), inferred_inst, synthesized_inst)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(mvar,
                                   format("synthesized type class instance is not definitionally equal to expression "
                                          "inferred by typing rules, synthesized")
                                   + pp_indent(pp_fn, synthesized_inst)
                                   + line() + format("inferred")
                                   + pp_indent(pp_fn, inferred_inst)).ignore_if(has_synth_sorry(synthesized_inst));
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
        if (!ready_to_synthesize(inst_type)) {
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
    metavar_decl mdecl   = mctx.get_metavar_decl(mvar);
    local_context lctx   = mdecl.get_context().instantiate_mvars(mctx);
    lctx                 = erase_inaccessible_annotations(lctx);
    expr type            = mctx.instantiate_mvars(mdecl.get_type());
    type                 = erase_inaccessible_annotations(type);
    m_ctx.set_mctx(mctx);
    return ::lean::mk_tactic_state_for(m_env, m_opts, m_decl_name, mctx, lctx, type);
}

void elaborator::synthesize() {
    synthesize_numeral_types();
    synthesize_type_class_instances();
}

void elaborator::ensure_no_unassigned_metavars_core(expr & e) {
    e = instantiate_mvars(e);
    if (!has_expr_metavar(e))
        return;
    name_set unassigned;
    for_each(e, [&](expr const & e, unsigned) {
        if (is_metavar_decl_ref(e))
            unassigned.insert(mvar_name(e));
        return true;
    });

    for (auto p : m_user_mvars) {
        auto const & m = p.first;
        auto const & info = p.second;
        auto m2 = get_app_fn(instantiate_mvars(m));
        // `m2` is still `m`, or it looks like a helper mvar introduced by the type_context_old
        if (is_mvar(m2) && unassigned.contains(mvar_name(m2))) {
            tactic_state s = mk_tactic_state_for(m);
            if (m_recover_from_errors) {
                // report error at `m`, but put `sorry` in `m2`
                if (!has_synth_sorry(infer_type(m))) {
                    auto tc = std::make_shared<type_context_old>(m_env, m_opts, m_ctx.mctx(), m_ctx.lctx());
                    message_builder out(tc, m_env, get_global_ios(), get_pos_info_provider()->get_file_name(),
                                        info.m_pos, ERROR);
                    out << "don't know how to synthesize placeholder";
                    if (info.m_context)
                        out << pp_until_meta_visible(mk_fmt_ctx(), *info.m_context);
                    out << "\n";
                    out << "context:\n" << mk_pair(s.pp(), m_opts);
                    out.report();
                    m_has_errors = true;
                }
                m_ctx.assign(m2, mk_sorry(infer_type(m2)));
            } else {
                throw failed_to_synthesize_placeholder_exception(m, s);
            }
        }
    }
    e = instantiate_mvars(e);
}

void elaborator::ensure_no_unassigned_metavars(expr & e) {
    ensure_no_unassigned_metavars_core(e);
    /* If we still have an unassigned mvar, it means the mvar doesn't directly correspond to a user-facing mvar.
     * That's bad (because we can't generate a sensible error message) and shouldn't happen. */
    lean_assert(has_synth_sorry(e) || !has_expr_metavar(e));
}

elaborator::snapshot::snapshot(elaborator const & e) {
    m_saved_mctx               = e.m_ctx.mctx();
    m_saved_instances          = e.m_instances;
    m_saved_numeral_types      = e.m_numeral_types;
}

void elaborator::snapshot::restore(elaborator & e) {
    e.m_ctx.set_mctx(m_saved_mctx);
    e.m_instances          = m_saved_instances;
    e.m_numeral_types      = m_saved_numeral_types;
}

/**
    \brief Auxiliary class for creating nice names for universe
    parameters introduced by the elaborator.

    This class also transforms remaining universe metavariables
    into parameters */
struct sanitize_param_names_fn : public replace_visitor {
    type_context_old &  m_ctx;
    name            m_p{"u"};
    name_set        m_L; /* All parameter names in the input expression. */
    unsigned        m_idx{1};
    buffer<name> &  m_new_param_names;
    /* If m_fixed == true, then we do not introduce new parameters.
       Remark: we should be able to infer the set of universe variables using just the
       theorem type. */
    bool            m_fixed;

    sanitize_param_names_fn(type_context_old & ctx, buffer<name> & new_lp_names):
        m_ctx(ctx), m_new_param_names(new_lp_names), m_fixed(false) {}

    sanitize_param_names_fn(type_context_old & ctx, elaborator::theorem_finalization_info const & info,
                            buffer<name> & new_lp_names):
        m_ctx(ctx), m_L(info.m_L),
        m_new_param_names(new_lp_names), m_fixed(true) {}

    level mk_param() {
        while (true) {
            name new_n = m_p.append_after(m_idx);
            m_idx++;
            if (!m_L.contains(new_n)) {
                m_new_param_names.push_back(new_n);
                return mk_univ_param(new_n);
            }
        }
    }

    level sanitize(level const & l) {
        name p("u");
        return replace(l, [&](level const & l) -> optional<level> {
                if (is_mvar(l)) {
                    if (is_metavar_decl_ref(l) && m_ctx.is_assigned(l)) {
                        return some_level(sanitize(*m_ctx.get_assignment(l)));
                    } else {
                        auto p = m_fixed ? mk_level_zero() : mk_param();
                        m_ctx.assign(l, p);
                        return some_level(p);
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
        return {m_L};
    }
};

/** When the output of the elaborator may contain meta-variables, we convert the type_context_old level meta-variables
    into regular kernel meta-variables. */
static expr replace_with_simple_metavars(metavar_context mctx, name_map<expr> & cache, expr const & e) {
    if (!has_expr_metavar(e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (is_metavar(e)) {
                if (auto r = cache.find(mvar_name(e))) {
                    return some_expr(*r);
                } else if (auto decl = mctx.find_metavar_decl(e)) {
                    expr new_type = replace_with_simple_metavars(mctx, cache, mctx.instantiate_mvars(decl->get_type()));
                    expr new_mvar = mk_metavar(mvar_name(e), new_type);
                    cache.insert(mvar_name(e), new_mvar);
                    return some_expr(new_mvar);
                } else if (is_metavar_decl_ref(e)) {
                    throw exception("unexpected occurrence of internal elaboration metavariable");
                } else {
                    return none_expr();
                }
            } else {
                return none_expr();
            }
        });
}

expr elaborator::elaborate(expr const & e) {
    expr r = visit(e,  none_expr());
    trace_elab_detail(tout() << "result before final checkpoint\n" << r << "\n";);
    synthesize();
    return r;
}

expr elaborator::elaborate_type(expr const & e) {
    expr const & ref = e;
    expr new_e = ensure_type(visit(e, none_expr()), ref);
    synthesize();
    return new_e;
}

expr_pair elaborator::elaborate_with_type(expr const & e, expr const & e_type) {
    expr const & ref = e;
    expr new_e, new_e_type;
    {
        expr Type  = visit(copy_pos(e_type, mk_sort(mk_level_placeholder())), none_expr());
        new_e_type = visit(e_type, some_expr(Type));
        new_e_type = ensure_type(new_e_type, e_type);
        new_e      = visit(e,      some_expr(new_e_type));
        synthesize();
    }
    new_e = enforce_type(new_e, new_e_type, "type mismatch", ref);
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

pair<expr, names> elaborator::finalize(expr const & e, bool check_unassigned, bool to_simple_metavar) {
    buffer<expr> es; es.push_back(e);
    buffer<name> new_lp_names;
    finalize(es, new_lp_names, check_unassigned, to_simple_metavar);
    return mk_pair(es[0], names(new_lp_names));
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

pair<expr, names>
elaborate(environment & env, options const & opts, name const & decl_name,
          metavar_context & mctx, local_context const & lctx, expr const & e,
          bool check_unassigned, bool recover_from_errors) {
    elaborator elab(env, opts, decl_name, mctx, lctx, recover_from_errors);
    expr r = elab.elaborate(e);
    auto p = elab.finalize(r, check_unassigned, true);
    mctx = elab.mctx();
    env  = elab.env();
    return p;
}

void initialize_elaborator() {
    g_elab_strategy = new name("elab_strategy");
    register_trace_class("elaborator");
    register_trace_class(name({"elaborator", "numeral"}));
    register_trace_class(name({"elaborator", "instances"}));
    register_trace_class(name({"elaborator", "equation"}));
    register_trace_class("elaborator_detail");
    register_trace_class("elaborator_debug");

    char const * elab_simple             = "elabSimple";
    char const * elab_with_expected_type = "elabWithExpectedType";
    char const * elab_as_eliminator      = "elabAsEliminator";

    register_system_attribute(
        elaborator_strategy_attribute(
            *g_elab_strategy,
            "internal attribute for the elaborator strategy for a given constant"));

    register_system_attribute(
        elaborator_strategy_proxy_attribute(
            elab_with_expected_type,
            "instructs elaborator that the arguments of the function application (f ...) "
            "should be elaborated using information about the expected type",
            elaborator_strategy::WithExpectedType));

    register_system_attribute(
        elaborator_strategy_proxy_attribute(
            elab_as_eliminator,
            "instructs elaborator that the arguments of the function application (f ...) "
            "should be elaborated as f were an eliminator",
            elaborator_strategy::AsEliminator));

    register_system_attribute(
        elaborator_strategy_proxy_attribute(
            elab_simple,
            "instructs elaborator that the arguments of the function application (f ...) "
            "should be elaborated from left to right, and without propagating information from the expected type "
            "to its arguments",
            elaborator_strategy::Simple));

    register_incompatible(elab_simple, elab_with_expected_type);
    register_incompatible(elab_simple, elab_as_eliminator);
    register_incompatible(elab_with_expected_type, elab_as_eliminator);

    g_elaborator_coercions          = new name{"elaborator", "coercions"};
    register_bool_option(*g_elaborator_coercions, LEAN_DEFAULT_ELABORATOR_COERCIONS,
                         "(elaborator) if true, the elaborator will automatically introduce coercions");
}

void finalize_elaborator() {
    delete g_elab_strategy;
    delete g_elaborator_coercions;
}
}
