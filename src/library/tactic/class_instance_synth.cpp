/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lazy_list_fn.h"
#include "util/flet.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/error_msgs.h"
#include "library/unifier.h"
#include "library/reducible.h"
#include "library/metavar_closure.h"
#include "library/error_handling/error_handling.h"
#include "library/class.h"
#include "library/local_context.h"
#include "library/choice_iterator.h"
#include "library/pp_options.h"
#include "library/generic_exception.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/tactic/util.h"
#include "library/tactic/class_instance_synth.h"

#ifndef LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES
#define LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES false
#endif

#ifndef LEAN_DEFAULT_CLASS_TRACE_INSTANCES
#define LEAN_DEFAULT_CLASS_TRACE_INSTANCES false
#endif

#ifndef LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH
#define LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH 32
#endif

#ifndef LEAN_DEFAULT_CLASS_CONSERVATIVE
#define LEAN_DEFAULT_CLASS_CONSERVATIVE true
#endif

namespace lean {
static name * g_class_unique_class_instances = nullptr;
static name * g_class_trace_instances        = nullptr;
static name * g_class_instance_max_depth     = nullptr;
static name * g_class_conservative           = nullptr;

[[ noreturn ]] void throw_class_exception(char const * msg, expr const & m) { throw_generic_exception(msg, m); }
[[ noreturn ]] void throw_class_exception(expr const & m, pp_fn const & fn) { throw_generic_exception(m, fn); }

void initialize_class_instance_elaborator() {
    g_class_unique_class_instances = new name{"class", "unique_instances"};
    g_class_trace_instances        = new name{"class", "trace_instances"};
    g_class_instance_max_depth     = new name{"class", "instance_max_depth"};
    g_class_conservative           = new name{"class", "conservative"};

    register_bool_option(*g_class_unique_class_instances,  LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES,
                         "(class) generate an error if there is more than one solution "
                         "for a class-instance resolution problem");

    register_bool_option(*g_class_trace_instances,  LEAN_DEFAULT_CLASS_TRACE_INSTANCES,
                         "(class) display messages showing the class-instances resolution execution trace");

    register_unsigned_option(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH,
                             "(class) max allowed depth in class-instance resolution");

    register_bool_option(*g_class_conservative,  LEAN_DEFAULT_CLASS_CONSERVATIVE,
                         "(class) use conservative unification (only unfold reducible definitions, and avoid delta-delta case splits)");
}

void finalize_class_instance_elaborator() {
    delete g_class_unique_class_instances;
    delete g_class_trace_instances;
    delete g_class_instance_max_depth;
    delete g_class_conservative;
}

bool get_class_unique_class_instances(options const & o) {
    return o.get_bool(*g_class_unique_class_instances, LEAN_DEFAULT_CLASS_UNIQUE_CLASS_INSTANCES);
}

bool get_class_trace_instances(options const & o) {
    return o.get_bool(*g_class_trace_instances, LEAN_DEFAULT_CLASS_TRACE_INSTANCES);
}

unsigned get_class_instance_max_depth(options const & o) {
    return o.get_unsigned(*g_class_instance_max_depth, LEAN_DEFAULT_CLASS_INSTANCE_MAX_DEPTH);
}

bool get_class_conservative(options const & o) {
    return o.get_bool(*g_class_conservative, LEAN_DEFAULT_CLASS_CONSERVATIVE);
}

/** \brief Context for handling class-instance metavariable choice constraint */
struct class_instance_context {
    io_state                  m_ios;
    name_generator            m_ngen;
    type_checker_ptr          m_tc;
    expr                      m_main_meta;
    bool                      m_relax;
    bool                      m_use_local_instances;
    bool                      m_trace_instances;
    bool                      m_conservative;
    unsigned                  m_max_depth;
    char const *              m_fname;
    optional<pos_info>        m_pos;
    class_instance_context(environment const & env, io_state const & ios,
                           name const & prefix, bool relax, bool use_local_instances):
        m_ios(ios),
        m_ngen(prefix),
        m_relax(relax),
        m_use_local_instances(use_local_instances) {
        m_fname           = nullptr;
        m_trace_instances = get_class_trace_instances(ios.get_options());
        m_max_depth       = get_class_instance_max_depth(ios.get_options());
        m_conservative    = get_class_conservative(ios.get_options());
        if (m_conservative)
            m_tc = mk_type_checker(env, m_ngen.mk_child(), false, UnfoldReducible);
        else
            m_tc = mk_type_checker(env, m_ngen.mk_child(), m_relax);
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
};

pair<expr, constraint> mk_class_instance_elaborator(std::shared_ptr<class_instance_context> const & C, local_context const & ctx,
                                                 optional<expr> const & type, tag g, unsigned depth);

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
    list<name>              m_instances;
    justification           m_jst;
    unsigned                m_depth;
    bool                    m_displayed_trace_header;

    class_instance_elaborator(std::shared_ptr<class_instance_context> const & C, local_context const & ctx,
                              expr const & meta, expr const & meta_type,
                              list<expr> const & local_insts, list<name> const & instances,
                              justification const & j, unsigned depth):
        choice_iterator(), m_C(C), m_ctx(ctx), m_meta(meta), m_meta_type(meta_type),
        m_local_instances(local_insts), m_instances(instances), m_jst(j), m_depth(depth) {
        if (m_depth > m_C->get_max_depth()) {
            throw_class_exception("maximum class-instance resolution depth has been reached "
                                  "(the limit can be increased by setting option 'class.instance_max_depth') "
                                  "(the class-instance resolution trace can be visualized by setting option 'class.trace_instances')",
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

    optional<constraints> try_instance(expr const & inst, expr const & inst_type) {
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
                                                                             g, m_depth+1);
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
            bool relax   = m_C->m_relax;
            constraint c = mk_eq_cnstr(m_meta, r, m_jst, relax);
            return optional<constraints>(mk_constraints(c, cs));
        } catch (exception &) {
            return optional<constraints>();
        }
    }

    optional<constraints> try_instance(name const & inst) {
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
            return try_instance(inst_cnst, inst_type);
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
            if (auto r = try_instance(inst, mlocal_type(inst)))
                return r;
        }
        while (!empty(m_instances)) {
            name inst   = head(m_instances);
            m_instances = tail(m_instances);
            if (auto cs = try_instance(inst))
                return cs;
        }
        return optional<constraints>();
    }
};

constraint mk_class_instance_cnstr(std::shared_ptr<class_instance_context> const & C, local_context const & ctx, expr const & m, unsigned depth) {
    environment const & env = C->env();
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const &, name_generator const &) {
        if (auto cls_name_it = is_ext_class(C->tc(), meta_type)) {
            name cls_name = *cls_name_it;
            list<expr> const & ctx_lst = ctx.get_data();
            list<expr> local_insts;
            if (C->use_local_instances())
                local_insts = get_local_instances(C->tc(), ctx_lst, cls_name);
            list<name>  insts = get_class_instances(env, cls_name);
            if (empty(local_insts) && empty(insts))
                return lazy_list<constraints>(); // nothing to be done
            // we are always strict with placeholders associated with classes
            return choose(std::make_shared<class_instance_elaborator>(C, ctx, meta, meta_type, local_insts, insts, j, depth));
        } else {
            // do nothing, type is not a class...
            return lazy_list<constraints>(constraints());
        }
    };
    bool owner      = false;
    bool relax      = C->m_relax;
    return mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::Basic),
                           owner, j, relax);
}

pair<expr, constraint> mk_class_instance_elaborator(std::shared_ptr<class_instance_context> const & C, local_context const & ctx,
                                                    optional<expr> const & type, tag g, unsigned depth) {
    expr m       = ctx.mk_meta(C->m_ngen, type, g);
    constraint c = mk_class_instance_cnstr(C, ctx, m, depth);
    return mk_pair(m, c);
}

constraint mk_class_instance_root_cnstr(std::shared_ptr<class_instance_context> const & C, local_context const & _ctx,
                                        expr const & m, bool is_strict, unifier_config const & cfg, delay_factor const & factor) {
    environment const & env = C->env();
    justification j         = mk_failed_to_synthesize_jst(env, m);

    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s,
                         name_generator const & ngen) {
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
        constraint c             = mk_class_instance_cnstr(C, ctx, new_meta, depth);
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
            bool relax     = C->m_relax;
            constraints cs = cls.mk_constraints(new_s, new_j, relax);
            return append(cs, postponed);
        };

        auto no_solution_fn = [=]() {
            if (is_strict)
                return lazy_list<constraints>();
            else
                return lazy_list<constraints>(constraints());
        };

        unify_result_seq seq1    = unify(env, 1, &c, ngen, substitution(), new_cfg);
        unify_result_seq seq2    = filter(seq1, [=](pair<substitution, constraints> const & p) {
                substitution new_s = p.first;
                expr result = new_s.instantiate(new_meta);
                // We only keep complete solutions (modulo universe metavariables)
                return !has_expr_metavar_relaxed(result);
            });

        if (get_class_unique_class_instances(C->m_ios.get_options())) {
            optional<expr> solution;
            substitution subst;
            constraints  cnstrs;
            for_each(seq2, [&](pair<substitution, constraints> const & p) {
                    subst  = p.first;
                    cnstrs = p.second;
                    expr next_solution = subst.instantiate(new_meta);
                    if (solution) {
                        throw_class_exception(m, [=](formatter const & fmt) {
                                format r = format("ambiguous class-instance resolution, "
                                                  "there is more than one solution");
                                r += pp_indent_expr(fmt, *solution);
                                r += compose(line(), format("and"));
                                r += pp_indent_expr(fmt, next_solution);
                                return r;
                            });
                    } else {
                        solution = next_solution;
                    }
                });
            if (!solution) {
                return no_solution_fn();
            } else {
                // some constraints may have been postponed (example: universe level constraints)
                return lazy_list<constraints>(to_cnstrs_fn(subst, cnstrs));
            }
        } else {
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
        }
    };
    bool owner = false;
    bool relax = C->m_relax;
    return mk_choice_cnstr(m, choice_fn, factor, owner, j, relax);
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances
*/
pair<expr, constraint> mk_class_instance_elaborator(
    environment const & env, io_state const & ios, local_context const & ctx,
    name const & prefix, optional<name> const & suffix, bool relax, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g, unifier_config const & cfg,
    pos_info_provider const * pip) {
    auto C       = std::make_shared<class_instance_context>(env, ios, prefix, relax, use_local_instances);
    expr m       = ctx.mk_meta(C->m_ngen, suffix, type, g);
    C->set_main_meta(m);
    if (pip)
        C->set_pos(pip->get_file_name(), pip->get_pos_info(m));
    constraint c = mk_class_instance_root_cnstr(C, ctx, m, is_strict, cfg, delay_factor());
    return mk_pair(m, c);
}

optional<expr> mk_class_instance(environment const & env, io_state const & ios, local_context const & ctx,
                                 name const & prefix, expr const & type, bool relax_opaque, bool use_local_instances,
                                 unifier_config const & cfg) {
    auto C = std::make_shared<class_instance_context>(env, ios, prefix, relax_opaque, use_local_instances);
    if (!is_ext_class(C->tc(), type))
        return none_expr();
    expr meta       = ctx.mk_meta(C->m_ngen, some_expr(type), type.get_tag());
    unsigned depth  = 0;
    constraint c    = mk_class_instance_cnstr(C, ctx, meta, depth);
    unifier_config new_cfg(cfg);
    new_cfg.m_discard        = true;
    new_cfg.m_use_exceptions = true;
    new_cfg.m_pattern        = true;
    new_cfg.m_kind           = C->m_conservative ? unifier_kind::VeryConservative : unifier_kind::Liberal;
    try {
        auto seq = unify(env, 1, &c, C->m_ngen.mk_child(), substitution(), new_cfg);
        while (true) {
            auto p = seq.pull();
            lean_assert(p);
            substitution s = p->first.first;
            expr r = s.instantiate_all(meta);
            if (!has_expr_metavar_relaxed(r))
                return some_expr(r);
            seq = p->second;
        }
    } catch (exception &) {
        return none_expr();
    }
}

optional<expr> mk_class_instance(environment const & env, io_state const & ios, list<expr> const & ctx,
                                 name const & prefix, expr const & type, bool relax_opaque, bool use_local_instances,
                                 unifier_config const & cfg) {
    local_context lctx(ctx);
    return mk_class_instance(env, ios, lctx, prefix, type, relax_opaque, use_local_instances, cfg);
}

optional<expr> mk_hset_instance(type_checker & tc, io_state const & ios, list<expr> const & ctx, expr const & type) {
    expr trunc_index = mk_app(mk_constant(get_is_trunc_trunc_index_of_nat_name()), mk_constant(get_nat_zero_name()));
    level lvl        = sort_level(tc.ensure_type(type).first);
    expr is_hset     = mk_app(mk_constant(get_is_trunc_name(), {lvl}), trunc_index, type);
    return mk_class_instance(tc.env(), ios, ctx, tc.mk_fresh_name(), is_hset);
}
}
