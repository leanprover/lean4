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
#include "library/type_context.h"
#include "library/class_instance_resolution.h"
// The following include files are need by the old type class resolution procedure
#include "util/lazy_list_fn.h"
#include "library/unifier.h"
#include "library/metavar_closure.h"

namespace lean {
[[ noreturn ]] void throw_class_exception(char const * msg, expr const & m) { throw_generic_exception(msg, m); }
[[ noreturn ]] void throw_class_exception(expr const & m, pp_fn const & fn) { throw_generic_exception(m, fn); }

static name * g_class_force_new              = nullptr;
static name * g_prefix                       = nullptr;

bool get_class_force_new(options const & o) {
    return o.get_bool(*g_class_force_new, false);
}

struct cienv {
    typedef std::unique_ptr<default_type_context> ti_ptr;
    ti_ptr m_ti_ptr;

    void reset(environment const & env, io_state const & ios, list<expr> const & ctx) {
        m_ti_ptr.reset(new default_type_context(env, ios, ctx));
    }

    bool compatible_env(environment const & env) {
        environment const & curr_env = m_ti_ptr->env();
        return env.is_descendant(curr_env) && curr_env.is_descendant(env);
    }

    void ensure_compatible(environment const & env, io_state const & ios, list<expr> const & ctx) {
        if (!m_ti_ptr || !compatible_env(env) || !m_ti_ptr->compatible_local_instances(ctx))
            reset(env, ios, ctx);
        if (!m_ti_ptr->update_options(ios.get_options()))
            m_ti_ptr->clear_cache();
    }

    optional<expr> operator()(environment const & env, io_state const & ios,
                              pos_info_provider const * pip, list<expr> const & ctx, expr const & type,
                              expr const & pos_ref) {
        ensure_compatible(env, ios, ctx);
        type_context::scope_pos_info scope(*m_ti_ptr, pip, pos_ref);
        return m_ti_ptr->mk_class_instance(type);
    }
};

MK_THREAD_LOCAL_GET_DEF(cienv, get_cienv);

static optional<expr> mk_class_instance(environment const & env, io_state const & ios, list<expr> const & ctx,
                                        expr const & e, pos_info_provider const * pip, expr const & pos_ref) {
    return get_cienv()(env, ios, pip, ctx, e, pos_ref);
}

optional<expr> mk_class_instance(environment const & env, io_state const & ios, list<expr> const & ctx,
                                 expr const & e, pos_info_provider const * pip) {
    return mk_class_instance(env, ios, ctx, e, pip, e);
}

optional<expr> mk_class_instance(environment const & env, list<expr> const & ctx, expr const & e, pos_info_provider const * pip) {
    return mk_class_instance(env, get_dummy_ios(), ctx, e, pip);
}

// Auxiliary class for generating a lazy-stream of instances.
class class_multi_instance_iterator : public choice_iterator {
    io_state                     m_ios;
    default_type_context         m_ti;
    type_context::scope_pos_info m_scope_pos_info;
    expr                         m_new_meta;
    justification                m_new_j;
    optional<expr>               m_first;
public:
    class_multi_instance_iterator(environment const & env, io_state const & ios, list<expr> const & ctx,
                                  expr const & e, pos_info_provider const * pip, expr const & pos_ref,
                                  expr const & new_meta, justification const & new_j,
                                  bool is_strict):
        choice_iterator(!is_strict),
        m_ios(ios),
        m_ti(env, ios, ctx, true),
        m_scope_pos_info(m_ti, pip, pos_ref),
        m_new_meta(new_meta),
        m_new_j(new_j) {
        m_first = m_ti.mk_class_instance(e);
    }

    virtual ~class_multi_instance_iterator() {}

    virtual optional<constraints> next() {
        optional<expr> r;
        if (m_first) {
            r       = m_first;
            m_first = none_expr();
        } else {
            r = m_ti.next_class_instance();
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
        local_context ctx;
        if (use_local_instances)
            ctx = _ctx.instantiate(substitution(s));
        cienv & cenv = get_cienv();
        cenv.ensure_compatible(env, ios, ctx.get_data());
        auto cls_name = cenv.m_ti_ptr->is_class(meta_type);
        if (!cls_name) {
            // do nothing, since type is not a class.
            return lazy_list<constraints>(constraints());
        }
        bool multiple_insts = try_multiple_instances(env, *cls_name);
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
pair<expr, constraint> mk_new_class_instance_elaborator(
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
    cienv & cenv = get_cienv();
    cenv.ensure_compatible(tc.env(), ios, ctx);
    flet<bool> set(cenv.m_ti_ptr->get_ignore_if_zero(), true);
    level lvl    = sort_level(tc.ensure_type(type).first);
    expr subsingleton;
    if (is_standard(tc.env()))
        subsingleton = mk_app(mk_constant(get_subsingleton_name(), {lvl}), type);
    else
        subsingleton = tc.whnf(mk_app(mk_constant(get_is_trunc_is_hprop_name(), {lvl}), type)).first;
    return cenv.m_ti_ptr->mk_class_instance(subsingleton);
}

void initialize_class_instance_resolution() {
    g_prefix                       = new name(name::mk_internal_unique_name());
    g_class_force_new              = new name{"class", "force_new"};

    register_bool_option(*g_class_force_new,  false,
                         "(class) force new type class resolution procedure to be used even in HoTT mode (THIS IS TEMPORARY OPTION)");
}

void finalize_class_instance_resolution() {
    delete g_prefix;
    delete g_class_force_new;
}

/*
  The rest of this module implements the old more powerful and *expensive* type class
  resolution procedure. We still have it because the HoTT library contains
  type class instances that require full-higher order unification to be solved.

  Example:

  definition is_equiv_tr [instance] [constructor] {A : Type} (P : A → Type) {x y : A}
    (p : x = y) : (is_equiv (transport P p)) := ...
*/

/** \brief Context for handling class-instance metavariable choice constraint */
struct class_instance_context {
    io_state                  m_ios;
    name_generator            m_ngen;
    type_checker_ptr          m_tc;
    expr                      m_main_meta;
    bool                      m_use_local_instances;
    bool                      m_trace_instances;
    bool                      m_conservative;
    unsigned                  m_max_depth;
    bool                      m_trans_instances;
    char const *              m_fname;
    optional<pos_info>        m_pos;
    class_instance_context(environment const & env, io_state const & ios,
                           name const & prefix, bool use_local_instances):
        m_ios(ios),
        m_ngen(prefix),
        m_use_local_instances(use_local_instances) {
        m_fname           = nullptr;
        m_trace_instances = get_class_trace_instances(ios.get_options());
        m_max_depth       = get_class_instance_max_depth(ios.get_options());
        m_conservative    = true; // We removed the option class.conservative
        m_trans_instances = get_class_trans_instances(ios.get_options());
        m_tc              = mk_class_type_checker(env, m_ngen.mk_child(), m_conservative);
        options opts      = m_ios.get_options();
        opts              = opts.update_if_undef(get_pp_purify_metavars_name(), false);
        opts              = opts.update_if_undef(get_pp_implicit_name(), true);
        m_ios.set_options(opts);
    }

    environment const & env() const { return m_tc->env(); }
    io_state const & ios() const { return m_ios; }
    bool use_local_instances() const { return m_use_local_instances; }
    type_checker & tc() const { return *m_tc; }
    bool trace_instances() const { return m_trace_instances; }
    void set_main_meta(expr const & meta) { m_main_meta = meta; }
    expr const & get_main_meta() const { return m_main_meta; }
    void set_pos(char const * fname, optional<pos_info> const & pos) {
        m_fname = fname;
        m_pos   = pos;
    }
    optional<pos_info> const & get_pos() const { return m_pos; }
    char const * get_file_name() const { return m_fname; }
    unsigned get_max_depth() const { return m_max_depth; }
    bool use_trans_instances() const { return m_trans_instances; }
};

static pair<expr, constraint>
mk_class_instance_elaborator(std::shared_ptr<class_instance_context> const & C, local_context const & ctx,
                             optional<expr> const & type, tag g, unsigned depth, bool use_globals);

/** \brief Choice function \c fn for synthesizing class instances.
    The function \c fn produces a stream of alternative solutions for ?m.
    In this case, \c fn will do the following:
    1) if the elaborated type of ?m is a 'class' C, then the stream will start with
         a) all local instances of class C (if elaborator.local_instances == true)
         b) all global instances of class C
*/
struct class_instance_elaborator : public choice_iterator {
    std::shared_ptr<class_instance_context> m_C;
    local_context           m_ctx;
    expr                    m_meta;
    // elaborated type of the metavariable
    expr                    m_meta_type;
    // local instances that should also be included in the
    // class-instance resolution.
    // This information is retrieved from the local context
    list<expr>              m_local_instances;
    // global declaration names that are class instances.
    // This information is retrieved using #get_class_instances.
    list<name>              m_trans_instances;
    list<name>              m_instances;
    justification           m_jst;
    unsigned                m_depth;
    bool                    m_displayed_trace_header;

    class_instance_elaborator(std::shared_ptr<class_instance_context> const & C, local_context const & ctx,
                              expr const & meta, expr const & meta_type,
                              list<expr> const & local_insts, list<name> const & trans_insts, list<name> const & instances,
                              justification const & j, unsigned depth):
        choice_iterator(), m_C(C), m_ctx(ctx), m_meta(meta), m_meta_type(meta_type),
        m_local_instances(local_insts), m_trans_instances(trans_insts), m_instances(instances), m_jst(j), m_depth(depth) {
        if (m_depth > m_C->get_max_depth()) {
            throw_class_exception("maximum class-instance resolution depth has been reached "
                                  "(the limit can be increased by setting option 'class.instance_max_depth') "
                                  "(the class-instance resolution trace can be visualized "
                                  "by setting option 'class.trace_instances')",
                                  C->get_main_meta());
        }
        m_displayed_trace_header = false;
    }

    constraints mk_constraints(constraint const & c, buffer<constraint> const & cs) {
        return cons(c, to_list(cs.begin(), cs.end()));
    }

    void trace(expr const & t, expr const & r) {
        if (!m_C->trace_instances())
            return;
        auto out = diagnostic(m_C->env(), m_C->ios());
        if (!m_displayed_trace_header && m_depth == 0) {
            if (auto fname = m_C->get_file_name()) {
                out << fname << ":";
            }
            if (auto pos = m_C->get_pos()) {
                out << pos->first << ":" << pos->second << ":";
            }
            out << " class-instance resolution trace" << endl;
            m_displayed_trace_header = true;
        }
        for (unsigned i = 0; i < m_depth; i++)
            out << " ";
        if (m_depth > 0)
            out << "[" << m_depth << "] ";
        out << m_meta << " : " << t << " := " << r << endl;
    }

    optional<constraints> try_instance(expr const & inst, expr const & inst_type, bool use_globals) {
        type_checker & tc     = m_C->tc();
        name_generator & ngen = m_C->m_ngen;
        tag g                 = inst.get_tag();
        try {
            flet<local_context> scope(m_ctx, m_ctx);
            buffer<expr> locals;
            expr meta_type = m_meta_type;
            while (true) {
                meta_type = tc.whnf(meta_type).first;
                if (!is_pi(meta_type))
                    break;
                expr local  = mk_local(ngen.next(), binding_name(meta_type),
                                       binding_domain(meta_type), binding_info(meta_type));
                m_ctx.add_local(local);
                locals.push_back(local);
                meta_type = instantiate(binding_body(meta_type), local);
            }
            expr type  = inst_type;
            expr r     = inst;
            buffer<constraint> cs;
            while (true) {
                type = tc.whnf(type).first;
                if (!is_pi(type))
                    break;
                expr arg;
                if (binding_info(type).is_inst_implicit()) {
                    pair<expr, constraint> ac = mk_class_instance_elaborator(m_C, m_ctx, some_expr(binding_domain(type)),
                                                                             g, m_depth+1, use_globals);
                    arg = ac.first;
                    cs.push_back(ac.second);
                } else {
                    arg = m_ctx.mk_meta(m_C->m_ngen, some_expr(binding_domain(type)), g);
                }
                r    = mk_app(r, arg, g);
                type = instantiate(binding_body(type), arg);
            }
            r = Fun(locals, r);
            trace(meta_type, r);
            constraint c = mk_eq_cnstr(m_meta, r, m_jst);
            return optional<constraints>(mk_constraints(c, cs));
        } catch (exception &) {
            return optional<constraints>();
        }
    }

    optional<constraints> try_instance(name const & inst, bool use_globals) {
        environment const & env = m_C->env();
        if (auto decl = env.find(inst)) {
            name_generator & ngen = m_C->m_ngen;
            buffer<level> ls_buffer;
            unsigned num_univ_ps = decl->get_num_univ_params();
            for (unsigned i = 0; i < num_univ_ps; i++)
                ls_buffer.push_back(mk_meta_univ(ngen.next()));
            levels ls = to_list(ls_buffer.begin(), ls_buffer.end());
            expr inst_cnst = copy_tag(m_meta, mk_constant(inst, ls));
            expr inst_type = instantiate_type_univ_params(*decl, ls);
            return try_instance(inst_cnst, inst_type, use_globals);
        } else {
            return optional<constraints>();
        }
    }

    virtual optional<constraints> next() {
        while (!empty(m_local_instances)) {
            expr inst         = head(m_local_instances);
            m_local_instances = tail(m_local_instances);
            if (!is_local(inst))
                continue;
            bool use_globals = true;
            if (auto r = try_instance(inst, mlocal_type(inst), use_globals))
                return r;
        }
        while (!empty(m_trans_instances)) {
            bool use_globals  = false;
            name inst         = head(m_trans_instances);
            m_trans_instances = tail(m_trans_instances);
            if (auto cs = try_instance(inst, use_globals))
                return cs;
        }
        while (!empty(m_instances)) {
            bool use_globals = true;
            name inst   = head(m_instances);
            m_instances = tail(m_instances);
            if (auto cs = try_instance(inst, use_globals))
                return cs;
        }
        return optional<constraints>();
    }
};

// Remarks:
//  - we only use get_class_instances and get_class_derived_trans_instances when use_globals is true
static constraint mk_class_instance_cnstr(std::shared_ptr<class_instance_context> const & C,
                                          local_context const & ctx, expr const & m, unsigned depth, bool use_globals) {
    environment const & env = C->env();
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const &, name_generator const &) {
        if (auto cls_name_it = is_ext_class(C->tc(), meta_type)) {
            name cls_name = *cls_name_it;
            list<expr> const & ctx_lst = ctx.get_data();
            list<expr> local_insts;
            if (C->use_local_instances())
                local_insts = get_local_instances(C->tc(), ctx_lst, cls_name);
            list<name>  trans_insts, insts;
            if (use_globals) {
                if (depth == 0 && C->use_trans_instances())
                    trans_insts = get_class_derived_trans_instances(env, cls_name);
                insts       = get_class_instances(env, cls_name);
            }
            if (empty(local_insts) && empty(insts))
                return lazy_list<constraints>(); // nothing to be done
            // we are always strict with placeholders associated with classes
            return choose(std::make_shared<class_instance_elaborator>(C, ctx, meta, meta_type, local_insts, trans_insts, insts, j, depth));
        } else {
            // do nothing, type is not a class...
            return lazy_list<constraints>(constraints());
        }
    };
    bool owner      = false;
    return mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::Basic), owner, j);
}

static pair<expr, constraint> mk_class_instance_elaborator(std::shared_ptr<class_instance_context> const & C, local_context const & ctx,
                                                           optional<expr> const & type, tag g, unsigned depth, bool use_globals) {
    expr m       = ctx.mk_meta(C->m_ngen, type, g);
    constraint c = mk_class_instance_cnstr(C, ctx, m, depth, use_globals);
    return mk_pair(m, c);
}

static constraint mk_class_instance_root_cnstr(std::shared_ptr<class_instance_context> const & C, local_context const & _ctx,
                                               expr const & m, bool is_strict, unifier_config const & cfg, delay_factor const & factor) {
    environment const & env = C->env();
    justification j         = mk_failed_to_synthesize_jst(env, m);

    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s,
                         name_generator && ngen) {
        environment const & env  = C->env();
        auto cls_name_it = is_ext_class(C->tc(), meta_type);
        if (!cls_name_it) {
            // do nothing, since type is not a class.
            return lazy_list<constraints>(constraints());
        }
        local_context ctx        = _ctx.instantiate(substitution(s));
        pair<expr, justification> mj = update_meta(meta, s);
        expr new_meta            = mj.first;
        justification new_j      = mj.second;
        unsigned depth           = 0;
        bool use_globals         = true;
        constraint c             = mk_class_instance_cnstr(C, ctx, new_meta, depth, use_globals);
        unifier_config new_cfg(cfg);
        new_cfg.m_discard        = false;
        new_cfg.m_use_exceptions = false;
        new_cfg.m_pattern        = true;
        new_cfg.m_kind           = C->m_conservative ? unifier_kind::VeryConservative : unifier_kind::Liberal;

        auto to_cnstrs_fn = [=](substitution const & subst, constraints const & cnstrs) -> constraints {
            substitution new_s = subst;
            // some constraints may have been postponed (example: universe level constraints)
            constraints  postponed = map(cnstrs,
                                         [&](constraint const & c) {
                                             // we erase internal justifications
                                             return update_justification(c, mk_composite1(j, new_j));
                                         });
            metavar_closure cls(new_meta);
            cls.add(meta_type);
            constraints cs = cls.mk_constraints(new_s, new_j);
            return append(cs, postponed);
        };

        auto no_solution_fn = [=]() {
            if (is_strict)
                return lazy_list<constraints>();
            else
                return lazy_list<constraints>(constraints());
        };

        unify_result_seq seq1    = unify(env, 1, &c, std::move(ngen), substitution(), new_cfg);
        unify_result_seq seq2    = filter(seq1, [=](pair<substitution, constraints> const & p) {
                substitution new_s = p.first;
                expr result = new_s.instantiate(new_meta);
                // We only keep complete solutions (modulo universe metavariables)
                return !has_expr_metavar_relaxed(result);
            });

        if (try_multiple_instances(env, *cls_name_it)) {
            lazy_list<constraints> seq3 = map2<constraints>(seq2, [=](pair<substitution, constraints> const & p) {
                    return to_cnstrs_fn(p.first, p.second);
                });
            if (is_strict) {
                return seq3;
            } else {
                // make sure it does not fail by appending empty set of constraints
                return append(seq3, lazy_list<constraints>(constraints()));
            }
        } else {
            auto p  = seq2.pull();
            if (!p)
                return no_solution_fn();
            else
                return lazy_list<constraints>(to_cnstrs_fn(p->first.first, p->first.second));
        }
    };
    bool owner = false;
    return mk_choice_cnstr(m, choice_fn, factor, owner, j);
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances
*/
pair<expr, constraint> mk_old_class_instance_elaborator(
    environment const & env, io_state const & ios, local_context const & ctx,
    name const & prefix, optional<name> const & suffix, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g, unifier_config const & cfg,
    pos_info_provider const * pip) {
    auto C       = std::make_shared<class_instance_context>(env, ios, prefix, use_local_instances);
    expr m       = ctx.mk_meta(C->m_ngen, suffix, type, g);
    C->set_main_meta(m);
    if (pip)
        C->set_pos(pip->get_file_name(), pip->get_pos_info(m));
    constraint c = mk_class_instance_root_cnstr(C, ctx, m, is_strict, cfg, delay_factor());
    return mk_pair(m, c);
}

pair<expr, constraint> mk_class_instance_elaborator(
    environment const & env, io_state const & ios, local_context const & ctx,
    name const & prefix, optional<name> const & suffix, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g,
    pos_info_provider const * pip) {
    if (is_standard(env) || get_class_force_new(ios.get_options())) {
        return mk_new_class_instance_elaborator(env, ios, ctx, prefix, suffix, use_local_instances,
                                                is_strict, type, g, pip);
    } else {
        unifier_config cfg(ios.get_options(), true /* use exceptions */, true /* discard */);
        return mk_old_class_instance_elaborator(env, ios, ctx, prefix, suffix, use_local_instances,
                                                is_strict, type, g, cfg, pip);
    }
}
}
