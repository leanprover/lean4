/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/lbool.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/metavar.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/normalize.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/local_context.h"
#include "library/generic_exception.h"
#include "library/io_state_stream.h"
#include "library/replace_visitor.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/choice_iterator.h"
#include "library/type_inference.h"
#include "library/class_instance_resolution.h"

#ifndef LEAN_DEFAULT_CLASS_TRACE_INSTANCES
#define LEAN_DEFAULT_CLASS_TRACE_INSTANCES false
#endif

#ifndef LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH
#define LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH 32
#endif

#ifndef LEAN_DEFAULT_CLASS_TRANS_INSTANCES
#define LEAN_DEFAULT_CLASS_TRANS_INSTANCES true
#endif

namespace lean {
[[ noreturn ]] void throw_class_exception(char const * msg, expr const & m) { throw_generic_exception(msg, m); }
[[ noreturn ]] void throw_class_exception(expr const & m, pp_fn const & fn) { throw_generic_exception(m, fn); }

static name * g_class_trace_instances        = nullptr;
static name * g_class_instance_max_depth     = nullptr;
static name * g_class_trans_instances        = nullptr;
static name * g_prefix                       = nullptr;

LEAN_THREAD_PTR(ci_local_metavar_types, g_lm_types);
LEAN_THREAD_PTR(io_state,               g_ios);

bool get_class_trace_instances(options const & o) {
    return o.get_bool(*g_class_trace_instances, LEAN_DEFAULT_CLASS_TRACE_INSTANCES);
}

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

bool get_class_trans_instances(options const & o) {
    return o.get_bool(*g_class_trans_instances, LEAN_DEFAULT_CLASS_TRANS_INSTANCES);
}

class default_ci_local_metavar_types : public ci_local_metavar_types {
public:
    virtual expr infer_local(expr const & e) { return mlocal_type(e); }
    virtual expr infer_metavar(expr const & e) { return mlocal_type(e); }
};

static expr ci_infer_local(expr const & e) {
    return g_lm_types->infer_local(e);
}

static expr ci_infer_metavar(expr const & e) {
    return g_lm_types->infer_metavar(e);
}

/** \brief The following global thread local constant is a big hack for mk_subsingleton_instance.
    When g_subsingleton_hack is true, the following type-class resolution problem fails
    Given (A : Type{?u}), where ?u is a universe meta-variable created by an external module,

    ?Inst : subsingleton.{?u} A := subsingleton_prop ?M

    This case generates the unification problem

       subsingleton.{?u} A =?= subsingleton.{0} ?M

    which can be solved by assigning (?u := 0) and (?M := A)
    when the hack is enabled, the is_def_eq method in the type class module fails at the subproblem:
                ?u =?= 0

    That is, when the hack is on, type-class resolution cannot succeed by instantiating an external universe
    meta-variable with 0.
*/
LEAN_THREAD_VALUE(bool, g_subsingleton_hack, false);

struct cienv {
    typedef rb_map<unsigned, level, unsigned_cmp> uassignment;
    typedef rb_map<unsigned, expr,  unsigned_cmp> eassignment;
    typedef std::unique_ptr<type_inference>       ti_ptr;
    environment               m_env;
    pos_info_provider const * m_pip;
    ti_ptr                    m_ti_ptr;
    optional<pos_info>        m_pos;
    expr_struct_map<expr>     m_cache;
    name_predicate            m_not_reducible_pred;

    list<expr>                m_ctx;
    buffer<pair<name, expr>>  m_local_instances;

    unsigned                  m_next_local_idx;
    unsigned                  m_next_uvar_idx;
    unsigned                  m_next_mvar_idx;

    struct state {
        list<pair<unsigned, expr>> m_stack; // stack of meta-variables that need to be synthesized;
        uassignment                m_uassignment;
        eassignment                m_eassignment;
    };

    state                     m_state; // active state

    struct choice {
        list<expr>            m_local_instances;
        list<name>            m_trans_instances;
        list<name>            m_instances;
        state                 m_state;
    };

    std::vector<choice>       m_choices;
    expr                      m_main_mvar;

    bool                      m_multiple_instances;

    bool                      m_displayed_trace_header;

    // configuration
    options                   m_options; // it is used for pretty printing
    unsigned                  m_max_depth;
    bool                      m_trans_instances;
    bool                      m_trace_instances;

    class ti : public type_inference {
        cienv &            m_cienv;
        std::vector<state> m_stack;
    public:
        ti(cienv & e):type_inference(e.m_env), m_cienv(e) {}
        virtual bool is_extra_opaque(name const & n) const { return m_cienv.is_not_reducible(n); }
        virtual expr mk_tmp_local(expr const & type, binder_info const & bi) { return m_cienv.mk_local(type, bi); }
        virtual bool is_tmp_local(expr const & e) const { return m_cienv.is_internal_local(e); }
        virtual bool is_uvar(level const & l) const { return cienv::is_uvar(l); }
        virtual bool is_mvar(expr const & e) const { return m_cienv.is_mvar(e); }
        virtual level const * get_assignment(level const & u) const { return m_cienv.get_assignment(u); }
        virtual expr const * get_assignment(expr const & m) const { return m_cienv.get_assignment(m); }
        virtual void update_assignment(level const & u, level const & v) { return m_cienv.update_assignment(u, v); }
        virtual void update_assignment(expr const & m, expr const & v) { return m_cienv.update_assignment(m, v); }
        virtual expr infer_local(expr const & e) const { return ci_infer_local(e); }
        virtual expr infer_metavar(expr const & e) const { return ci_infer_metavar(e); }
        virtual void push() { m_stack.push_back(m_cienv.m_state); }
        virtual void pop() { m_cienv.m_state = m_stack.back(); m_stack.pop_back(); }
        virtual void commit() { m_stack.pop_back(); }

        virtual bool ignore_universe_def_eq(level const & l1, level const & l2) const {
            if (is_meta(l1) || is_meta(l2)) {
                // The unifier may invoke this module before universe metavariables in the class
                // have been instantiated. So, we just ignore and assume they will be solved by
                // the unifier.

                // See comment at g_subsingleton_hack declaration.
                if (g_subsingleton_hack && (is_zero(l1) || is_zero(l2)))
                    return false;
                return true; // we ignore
            } else {
                return false;
            }
        }


        virtual bool validate_assignment(expr const & m, buffer<expr> const & locals, expr const & v) {
            // We must check
            //   1. Any (internal) local constant occurring in v occurs in locals
            //   2. m does not occur in v
            bool ok = true;
            for_each(v, [&](expr const & e, unsigned) {
                    if (!ok)
                        return false; // stop search
                    if (is_tmp_local(e)) {
                        if (std::all_of(locals.begin(), locals.end(), [&](expr const & a) {
                                    return mlocal_name(a) != mlocal_name(e); })) {
                            ok = false; // failed 1
                            return false;
                        }
                    } else if (is_mvar(e)) {
                        if (m == e) {
                            ok = false; // failed 2
                            return false;
                        }
                        return false;
                    }
                    return true;
                });
            return ok;
        }
    };

    cienv(bool multiple_instances = false):
        m_next_local_idx(0),
        m_next_uvar_idx(0),
        m_next_mvar_idx(0),
        m_multiple_instances(multiple_instances) {}

    bool is_not_reducible(name const & n) const {
        return m_not_reducible_pred(n);
    }

    void clear_cache() {
        expr_struct_map<expr> fresh;
        fresh.swap(m_cache);
        if (m_ti_ptr)
            m_ti_ptr->clear_cache();
    }

    void clear_cache_and_ctx() {
        m_next_local_idx = 0;
        m_next_uvar_idx  = 0;
        m_next_mvar_idx  = 0;
        m_ctx = list<expr>();
        m_local_instances.clear();
        clear_cache();
    }

    optional<expr> check_cache(expr const & type) const {
        if (m_multiple_instances) {
            // We do not cache results when multiple instances have to be generated.
            return none_expr();
        }
        auto it = m_cache.find(type);
        if (it != m_cache.end())
            return some_expr(it->second);
        else
            return none_expr();
    }

    void cache_result(expr const & type, expr const & inst) {
        if (m_multiple_instances) {
            // We do not cache results when multiple instances have to be generated.
            return;
        }
        m_cache.insert(mk_pair(type, inst));
    }

    void set_options(options const & o) {
        m_options = o;
        if (m_trace_instances) {
            m_options = m_options.update_if_undef(get_pp_purify_metavars_name(), false);
            m_options = m_options.update_if_undef(get_pp_implicit_name(), true);
        }
        unsigned max_depth    = get_class_instance_max_depth(o);
        bool trans_instances  = get_class_trans_instances(o);
        bool trace_instances  = get_class_trace_instances(o);

        if (m_max_depth        != max_depth        ||
            m_trans_instances  != trans_instances  ||
            m_trace_instances  != trace_instances) {
            clear_cache_and_ctx();
        }
        m_max_depth        = max_depth;
        m_trans_instances  = trans_instances;
        m_trace_instances  = trace_instances;
    }

    void set_env(environment const & env) {
        // Remark: We can implement the following potential refinement.
        // If env is a descendant of m_env, and env does not add new global instances,
        // then we don't need to reset the cache
        if (!m_env.is_descendant(m_env) || !m_env.is_descendant(env)) {
            m_env                = env;
            m_not_reducible_pred = mk_not_reducible_pred(m_env);
            m_ti_ptr             = nullptr;
            clear_cache_and_ctx();
        }

        if (!m_ti_ptr) {
            m_ti_ptr.reset(new ti(*this));
            clear_cache_and_ctx();
        }
    }

    expr whnf(expr const & e) {
        return m_ti_ptr->whnf(e);
    }

    expr infer_type(expr const & e) {
        return m_ti_ptr->infer(e);
    }

    bool is_def_eq(expr const & e1, expr const & e2) {
        return m_ti_ptr->is_def_eq(e1, e2);
    }

    expr instantiate_uvars_mvars(expr const & e) {
        return m_ti_ptr->instantiate_uvars_mvars(e);
    }

    expr mk_local(expr const & type, binder_info const & bi = binder_info()) {
        unsigned idx = m_next_local_idx;
        m_next_local_idx++;
        name n(*g_prefix, idx);
        return lean::mk_local(n, n, type, bi);
    }

    bool is_internal_local(expr const & e) {
        if (!is_local(e))
            return false;
        name const & n = mlocal_name(e);
        return !n.is_atomic() && n.get_prefix() == *g_prefix;
    }

    /** \brief If the constant \c e is a class, return its name */
    optional<name> constant_is_class(expr const & e) {
        name const & cls_name = const_name(e);
        if (lean::is_class(m_env, cls_name)) {
            return optional<name>(cls_name);
        } else {
            return optional<name>();
        }
    }

    optional<name> is_full_class(expr type) {
        type = whnf(type);
        if (is_pi(type)) {
            return is_full_class(instantiate(binding_body(type), mk_local(binding_domain(type))));
        } else {
            expr f = get_app_fn(type);
            if (!is_constant(f))
                return optional<name>();
            return constant_is_class(f);
       }
    }

    /** \brief Partial/Quick test for is_class. Result
        l_true:   \c type is a class, and the name of the class is stored in \c result.
        l_false:  \c type is not a class.
        l_undef:  procedure did not establish whether \c type is a class or not.
    */
    lbool is_quick_class(expr const & type, name & result) {
        expr const * it         = &type;
        while (true) {
            switch (it->kind()) {
            case expr_kind::Var:  case expr_kind::Sort:   case expr_kind::Local:
            case expr_kind::Meta: case expr_kind::Lambda:
                return l_false;
            case expr_kind::Macro:
                return l_undef;
            case expr_kind::Constant:
                if (auto r = constant_is_class(*it)) {
                    result = *r;
                    return l_true;
                } else if (is_not_reducible(const_name(*it))) {
                    return l_false;
                } else {
                    return l_undef;
                }
            case expr_kind::App: {
                expr const & f = get_app_fn(*it);
                if (is_constant(f)) {
                    if (auto r = constant_is_class(f)) {
                        result = *r;
                        return l_true;
                    } else if (is_not_reducible(const_name(f))) {
                        return l_false;
                    } else {
                        return l_undef;
                    }
                } else if (is_lambda(f) || is_macro(f)) {
                    return l_undef;
                } else {
                    return l_false;
                }
            }
            case expr_kind::Pi:
                it = &binding_body(*it);
                break;
            }
        }
    }

    /** \brief Return true iff \c type is a class or Pi that produces a class. */
    optional<name> is_class(expr const & type) {
        name result;
        switch (is_quick_class(type, result)) {
        case l_true:  return optional<name>(result);
        case l_false: return optional<name>();
        case l_undef: break;
        }
        return is_full_class(type);
    }


    // Auxiliary method for set_ctx
    void set_local_instance(unsigned i, name const & cname, expr const & e) {
        lean_assert(i <= m_local_instances.size());
        if (i == m_local_instances.size()) {
            clear_cache();
            m_local_instances.push_back(mk_pair(cname, e));
        } else if (e != m_local_instances[i].second) {
            clear_cache();
            m_local_instances[i] = mk_pair(cname, e);
        } else {
            // we don't need to reset the cache since this local instance
            // is equal to the one used in a previous call
        }
    }

    void set_ctx(list<expr> const & ctx) {
        if (is_eqp(m_ctx, ctx)) {
            // we can keep the cache because the local context
            // is still pointing to the same object.
            return;
        }
        m_ctx = ctx;
        unsigned i = 0;
        for (expr const & e : ctx) {
            // Remark: we use infer_type(e) instead of mlocal_type because we want to allow
            // customers (e.g., blast) of this class to store the type of local constants
            // in a different place.
            if (auto cname = is_class(infer_type(e))) {
                set_local_instance(i, *cname, e);
                i++;
            }
        }
        if (i < m_local_instances.size()) {
            // new ctx has fewer local instances than previous one
            m_local_instances.resize(i);
            clear_cache();
        }
    }

    void set_pos_info(pos_info_provider const * pip, expr const & type) {
        m_pip = pip;
        if (m_pip)
            m_pos = m_pip->get_pos_info(type);
    }

    // Create an internal universal metavariable
    level mk_uvar() {
        unsigned idx = m_next_uvar_idx;
        m_next_uvar_idx++;
        return mk_meta_univ(name(*g_prefix, idx));
    }

    // Return true iff \c l is an internal universe metavariable created by this module.
    static bool is_uvar(level const & l) {
        if (!is_meta(l))
            return false;
        name const & n = meta_id(l);
        return !n.is_atomic() && n.get_prefix() == *g_prefix;
    }

    static unsigned uvar_idx(level const & l) {
        lean_assert(is_uvar(l));
        return meta_id(l).get_numeral();
    }

    level const * get_assignment(level const & u) const {
        return m_state.m_uassignment.find(uvar_idx(u));
    }

    bool is_assigned(level const & u) const {
        return get_assignment(u) != nullptr;
    }

    // Assign \c v to the universe metavariable \c u.
    void update_assignment(level const & u, level const & v) {
        m_state.m_uassignment.insert(uvar_idx(u), v);
    }

    // Create an internal metavariable.
    expr mk_mvar(expr const & type) {
        unsigned idx = m_next_mvar_idx;
        m_next_mvar_idx++;
        return mk_metavar(name(*g_prefix, idx), type);
    }

    // Return true iff \c e is an internal metavariable created by this module.
    static bool is_mvar(expr const & e) {
        if (!is_metavar(e))
            return false;
        name const & n = mlocal_name(e);
        return !n.is_atomic() && n.get_prefix() == *g_prefix;
    }

    static unsigned mvar_idx(expr const & m) {
        lean_assert(is_mvar(m));
        return mlocal_name(m).get_numeral();
    }

    expr const * get_assignment(expr const & m) const {
        return m_state.m_eassignment.find(mvar_idx(m));
    }

    bool is_assigned(expr const & m) const {
        return get_assignment(m) != nullptr;
    }

    void update_assignment(expr const & m, expr const & v) {
        m_state.m_eassignment.insert(mvar_idx(m), v);
        lean_assert(is_assigned(m));
    }

    // Assign \c v to the metavariable \c m.
    void assign(expr const & m, expr const & v) {
        lean_assert(!is_assigned(m));
        update_assignment(m, v);
    }

    io_state_stream diagnostic() {
        io_state ios(*g_ios);
        ios.set_options(m_options);
        return lean::diagnostic(m_env, ios);
    }

    void trace(unsigned depth, expr const & mvar, expr const & mvar_type, expr const & r) {
        lean_assert(m_trace_instances);
        auto out = diagnostic();
        if (!m_displayed_trace_header && m_choices.size() == 1) {
            if (m_pip) {
                if (auto fname = m_pip->get_file_name()) {
                    out << fname << ":";
                }
                if (m_pos)
                    out << m_pos->first << ":" << m_pos->second << ":";
            }
            out << " class-instance resolution trace" << endl;
            m_displayed_trace_header = true;
        }
        for (unsigned i = 0; i < depth; i++)
            out << " ";
        if (depth > 0)
            out << "[" << depth << "] ";
        out << mvar << " : " << instantiate_uvars_mvars(mvar_type) << " := " << r << endl;
    }

    bool try_instance(unsigned depth, expr const & mvar, expr const & inst, expr const & inst_type) {
        try {
            buffer<expr> locals;
            expr mvar_type = mlocal_type(mvar);
            while (true) {
                mvar_type = whnf(mvar_type);
                if (!is_pi(mvar_type))
                    break;
                expr local  = mk_local(binding_domain(mvar_type));
                locals.push_back(local);
                mvar_type = instantiate(binding_body(mvar_type), local);
            }
            expr type  = inst_type;
            expr r     = inst;
            buffer<expr> new_inst_mvars;
            while (true) {
                type = whnf(type);
                if (!is_pi(type))
                    break;
                expr new_mvar = mk_mvar(Pi(locals, binding_domain(type)));
                if (binding_info(type).is_inst_implicit()) {
                    new_inst_mvars.push_back(new_mvar);
                }
                expr new_arg = mk_app(new_mvar, locals);
                r    = mk_app(r, new_arg);
                type = instantiate(binding_body(type), new_arg);
            }
            if (m_trace_instances) {
                trace(depth, mk_app(mvar, locals), mvar_type, r);
            }
            if (!is_def_eq(mvar_type, type)) {
                return false;
            }
            r = Fun(locals, r);
            if (is_assigned(mvar)) {
                // Remark: if the metavariable is already assigned, we should check whether
                // the previous assignment (obtained by solving unification constraints) and the
                // synthesized one are definitionally equal. We don't do that for performance reasons.
                // Moreover, the is_def_eq defined here is not complete (e.g., it only unfolds reducible constants).
                update_assignment(mvar, r);
            } else {
                assign(mvar, r);
            }
            // copy new_inst_mvars to stack
            unsigned i = new_inst_mvars.size();
            while (i > 0) {
                --i;
                m_state.m_stack = cons(mk_pair(depth+1, new_inst_mvars[i]), m_state.m_stack);
            }
            return true;
        } catch (exception &) {
            return false;
        }
    }

    bool try_instance(unsigned depth, expr const & mvar, name const & inst_name) {
        if (auto decl = m_env.find(inst_name)) {
            buffer<level> ls_buffer;
            unsigned num_univ_ps = decl->get_num_univ_params();
            for (unsigned i = 0; i < num_univ_ps; i++)
                ls_buffer.push_back(mk_uvar());
            levels ls = to_list(ls_buffer.begin(), ls_buffer.end());
            expr inst_cnst = mk_constant(inst_name, ls);
            expr inst_type = instantiate_type_univ_params(*decl, ls);
            return try_instance(depth, mvar, inst_cnst, inst_type);
        } else {
            return false;
        }
    }

    list<expr> get_local_instances(name const & cname) {
        buffer<expr> selected;
        for (pair<name, expr> const & p : m_local_instances) {
            if (p.first == cname)
                selected.push_back(p.second);
        }
        return to_list(selected);
    }

    bool is_done() const {
        return empty(m_state.m_stack);
    }

    bool mk_choice_point(expr const & mvar) {
        lean_assert(is_mvar(mvar));
        if (m_choices.size() > m_max_depth) {
            throw_class_exception("maximum class-instance resolution depth has been reached "
                                  "(the limit can be increased by setting option 'class.instance_max_depth') "
                                  "(the class-instance resolution trace can be visualized by setting option 'class.trace_instances')",
                                  mlocal_type(m_main_mvar));
        }
        m_choices.push_back(choice());
        choice & r = m_choices.back();
        expr mvar_type = instantiate_uvars_mvars(mlocal_type(mvar));
        if (has_expr_metavar_relaxed(mvar_type)) {
            // Remark: we use has_expr_metavar_relaxed instead of has_expr_metavar, because
            // we want to ignore metavariables occurring in the type of local constants occurring in mvar_type.
            // This can happen when type class resolution is invoked from the unifier.
            return false;
        }
        auto cname = is_class(mvar_type);
        if (!cname)
            return false;
        r.m_local_instances = get_local_instances(*cname);
        if (m_trans_instances && m_choices.empty()) {
            // we only use transitive instances in the top-level
            r.m_trans_instances = get_class_derived_trans_instances(m_env, *cname);
        }
        r.m_instances = get_class_instances(m_env, *cname);
        if (empty(r.m_local_instances) && empty(r.m_trans_instances) && empty(r.m_instances))
            return false;
        r.m_state = m_state;
        return true;
    }

    bool process_next_alt_core(unsigned depth, expr const & mvar, list<expr> & insts) {
        while (!empty(insts)) {
            expr inst       = head(insts);
            insts           = tail(insts);
            expr inst_type  = infer_type(inst);
            if (try_instance(depth, mvar, inst, inst_type))
                return true;
        }
        return false;
    }

    bool process_next_alt_core(unsigned depth, expr const & mvar, list<name> & inst_names) {
        while (!empty(inst_names)) {
            name inst_name    = head(inst_names);
            inst_names        = tail(inst_names);
            if (try_instance(depth, mvar, inst_name))
                return true;
        }
        return false;
    }

    bool process_next_alt(unsigned depth, expr const & mvar) {
        lean_assert(!m_choices.empty());
        choice & c = m_choices.back();
        if (process_next_alt_core(depth, mvar, c.m_local_instances))
            return true;
        if (process_next_alt_core(depth, mvar, c.m_trans_instances))
            return true;
        if (process_next_alt_core(depth, mvar, c.m_instances))
            return true;
        return false;
    }

    bool process_next_mvar() {
        lean_assert(!is_done());
        unsigned depth  = head(m_state.m_stack).first;
        expr mvar       = head(m_state.m_stack).second;
        if (!mk_choice_point(mvar))
            return false;
        m_state.m_stack = tail(m_state.m_stack);
        return process_next_alt(depth, mvar);
    }

    bool backtrack() {
        if (m_choices.empty())
            return false;
        while (true) {
            m_choices.pop_back();
            if (m_choices.empty())
                return false;
            m_state         = m_choices.back().m_state;
            unsigned depth  = head(m_state.m_stack).first;
            expr mvar       = head(m_state.m_stack).second;
            m_state.m_stack = tail(m_state.m_stack);
            if (process_next_alt(depth, mvar))
                return true;
        }
    }

    optional<expr> search() {
        while (!is_done()) {
            if (!process_next_mvar()) {
                if (!backtrack())
                    return none_expr();
            }
        }
        return some_expr(instantiate_uvars_mvars(m_main_mvar));
    }

    optional<expr> next_solution() {
        if (m_choices.empty())
            return none_expr();
        m_state         = m_choices.back().m_state;
        unsigned depth  = head(m_state.m_stack).first;
        expr mvar       = head(m_state.m_stack).second;
        m_state.m_stack = tail(m_state.m_stack);
        if (process_next_alt(depth, mvar))
            return search();
        else if (backtrack())
            return search();
        else
            return none_expr();
    }

    void init_search(expr const & type) {
        m_state     = state();
        m_main_mvar = mk_mvar(type);
        m_state.m_stack = cons(mk_pair(0u, m_main_mvar), m_state.m_stack);
        m_displayed_trace_header = false;
        m_choices.clear();
    }

    optional<expr> ensure_no_meta(optional<expr> r) {
        while (true) {
            if (!r)
                return none_expr();
            if (!has_expr_metavar_relaxed(*r)) {
                cache_result(mlocal_type(m_main_mvar), *r);
                return r;
            }
            r = next_solution();
        }
    }

    optional<expr> operator()(environment const & env, options const & o, pos_info_provider const * pip, list<expr> const & ctx, expr const & type,
                              expr const & pos_ref) {
        set_env(env);
        set_options(o);
        set_ctx(ctx);
        set_pos_info(pip, pos_ref);

        if (auto r = check_cache(type)) {
            if (m_trace_instances) {
                auto out = diagnostic();
                out << "cached instance for " << type << "\n" << *r << "\n";
            }
            return r;
        }

        init_search(type);
        auto r = search();
        return ensure_no_meta(r);
    }

    optional<expr> next() {
        if (!m_multiple_instances)
            return none_expr();
        auto r = next_solution();
        return ensure_no_meta(r);
    }
};

MK_THREAD_LOCAL_GET_DEF(cienv, get_cienv);

static void clear_cache_and_ctx() {
    get_cienv().clear_cache_and_ctx();
}

ci_local_metavar_types_scope::ci_local_metavar_types_scope(ci_local_metavar_types & t):
    m_old(g_lm_types) {
    g_lm_types = &t;
    clear_cache_and_ctx();
}

ci_local_metavar_types_scope::~ci_local_metavar_types_scope() {
    clear_cache_and_ctx();
    g_lm_types = m_old;
}

static optional<expr> mk_class_instance(environment const & env, io_state const & ios, list<expr> const & ctx, expr const & e, pos_info_provider const * pip,
                                        expr const & pos_ref) {
    flet<io_state*> set_ios(g_ios, const_cast<io_state*>(&ios));
    return get_cienv()(env, ios.get_options(), pip, ctx, e, pos_ref);
}

optional<expr> mk_class_instance(environment const & env, io_state const & ios, list<expr> const & ctx, expr const & e, pos_info_provider const * pip) {
    return mk_class_instance(env, ios, ctx, e, pip, e);
}

optional<expr> mk_class_instance(environment const & env, list<expr> const & ctx, expr const & e, pos_info_provider const * pip) {
    return mk_class_instance(env, get_dummy_ios(), ctx, e, pip);
}

// Auxiliary class for generating a lazy-stream of instances.
class class_multi_instance_iterator : public choice_iterator {
    io_state       m_ios;
    cienv          m_cienv;
    expr           m_new_meta;
    justification  m_new_j;
    optional<expr> m_first;
public:
    class_multi_instance_iterator(environment const & env, io_state const & ios, list<expr> const & ctx,
                                  expr const & e, pos_info_provider const * pip, expr const & pos_ref,
                                  expr const & new_meta, justification const & new_j,
                                  bool is_strict):
        choice_iterator(!is_strict),
        m_ios(ios),
        m_cienv(true),
        m_new_meta(new_meta),
        m_new_j(new_j) {
        flet<io_state*> set_ios(g_ios, const_cast<io_state*>(&m_ios));
        m_first = m_cienv(env, ios.get_options(), pip, ctx, e, pos_ref);
    }

    virtual ~class_multi_instance_iterator() {}

    virtual optional<constraints> next() {
        optional<expr> r;
        if (m_first) {
            r       = m_first;
            m_first = none_expr();
        } else {
            flet<io_state*> set_ios(g_ios, const_cast<io_state*>(&m_ios));
            r = m_cienv.next();
        }
        if (r) {
            constraint c = mk_eq_cnstr(m_new_meta, *r, m_new_j);
            return optional<constraints>(constraints(c));
        } else {
            return optional<constraints>();
        }
    }
};

static constraint mk_class_instance_root_cnstr(environment const & env, io_state const & ios, local_context const & _ctx, expr const & m, bool is_strict,
                                               bool use_local_instances, pos_info_provider const * pip) {
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s, name_generator &&) {
        cienv & cenv = get_cienv();
        cenv.set_env(env);
        auto cls_name = cenv.is_class(meta_type);
        if (!cls_name) {
            // do nothing, since type is not a class.
            return lazy_list<constraints>(constraints());
        }
        bool multiple_insts = try_multiple_instances(env, *cls_name);
        local_context ctx;
        if (use_local_instances)
            ctx = _ctx.instantiate(substitution(s));
        pair<expr, justification> mj = update_meta(meta, s);
        expr new_meta                = mj.first;
        justification new_j          = mj.second;
        if (multiple_insts) {
            return choose(std::shared_ptr<choice_iterator>(new class_multi_instance_iterator(env, ios, ctx.get_data(),
                                                                                             meta_type, pip, meta,
                                                                                             new_meta, new_j, is_strict)));
        } else {
            if (auto r = mk_class_instance(env, ios, ctx.get_data(), meta_type, pip, meta)) {
                constraint c = mk_eq_cnstr(new_meta, *r, new_j);
                return lazy_list<constraints>(constraints(c));
            } else if (is_strict) {
                return lazy_list<constraints>();
            } else {
                return lazy_list<constraints>(constraints());
            }
        }
    };
    bool owner = false;
    delay_factor factor;
    return mk_choice_cnstr(m, choice_fn, factor, owner, j);
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances
*/
pair<expr, constraint> mk_class_instance_elaborator(
    environment const & env, io_state const & ios, local_context const & ctx,
    name const & prefix, optional<name> const & suffix, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g, pos_info_provider const * pip) {
    name_generator ngen(prefix);
    expr m       = ctx.mk_meta(ngen, suffix, type, g);
    constraint c = mk_class_instance_root_cnstr(env, ios, ctx, m, is_strict,
                                                use_local_instances, pip);
    return mk_pair(m, c);
}

optional<expr> mk_class_instance(environment const & env, io_state const & ios, local_context const & ctx, expr const & type, bool use_local_instances) {
    if (use_local_instances)
        return mk_class_instance(env, ios, ctx.get_data(), type, nullptr);
    else
        return mk_class_instance(env, ios, list<expr>(), type, nullptr);
}

optional<expr> mk_class_instance(environment const & env, local_context const & ctx, expr const & type) {
    return mk_class_instance(env, ctx.get_data(), type, nullptr);
}

optional<expr> mk_hset_instance(type_checker & tc, io_state const & ios, list<expr> const & ctx, expr const & type) {
    level lvl        = sort_level(tc.ensure_type(type).first);
    expr is_hset     = tc.whnf(mk_app(mk_constant(get_is_trunc_is_hset_name(), {lvl}), type)).first;
    return mk_class_instance(tc.env(), ios, ctx, is_hset);
}

optional<expr> mk_subsingleton_instance(type_checker & tc, io_state const & ios, list<expr> const & ctx, expr const & type) {
    flet<bool> set(g_subsingleton_hack, true);
    level lvl        = sort_level(tc.ensure_type(type).first);
    expr subsingleton;
    if (is_standard(tc.env()))
        subsingleton = mk_app(mk_constant(get_subsingleton_name(), {lvl}), type);
    else
        subsingleton = tc.whnf(mk_app(mk_constant(get_is_trunc_is_hprop_name(), {lvl}), type)).first;
    return mk_class_instance(tc.env(), ios, ctx, subsingleton);
}

void initialize_class_instance_resolution() {
    g_prefix                       = new name(name::mk_internal_unique_name());
    g_class_trace_instances        = new name{"class", "trace_instances"};
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    g_class_trans_instances        = new name{"class", "trans_instances"};

    register_bool_option(*g_class_trace_instances,  LEAN_DEFAULT_CLASS_TRACE_INSTANCES,
                         "(class) display messages showing the class-instances resolution execution trace");

    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");

    register_bool_option(*g_class_trans_instances,  LEAN_DEFAULT_CLASS_TRANS_INSTANCES,
                         "(class) use automatically derived instances from the transitive closure of "
                         "the structure instance graph");
    g_lm_types = new default_ci_local_metavar_types();
}

void finalize_class_instance_resolution() {
    delete g_lm_types;
    delete g_prefix;
    delete g_class_trace_instances;
    delete g_class_instance_max_depth;
    delete g_class_trans_instances;
}
}
