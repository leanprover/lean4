/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "util/list_fn.h"
#include "kernel/instantiate.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "library/kernel_serializer.h"
#include "library/reducible.h"
#include "library/util.h"
#include "library/match.h"
#include "library/projection.h"
#include "library/generic_exception.h"
#include "library/tactic/rewrite_tactic.h"
#include "library/tactic/expr_to_tactic.h"

// #define TRACE_MATCH_PLUGIN

namespace lean {
class unfold_info {
    name      m_name;
    location  m_location;
public:
    unfold_info() {}
    unfold_info(name const & n, location const & loc):m_name(n), m_location(loc) {}
    name const & get_name() const { return m_name; }
    location const & get_location() const { return m_location; }
    friend serializer & operator<<(serializer & s, unfold_info const & elem);
    friend deserializer & operator>>(deserializer & d, unfold_info & e);
};

serializer & operator<<(serializer & s, unfold_info const & e) {
    s << e.m_name << e.m_location;
    return s;
}

deserializer & operator>>(deserializer & d, unfold_info & e) {
    d >> e.m_name >> e.m_location;
    return d;
}

class rewrite_info {
public:
    enum multiplicity { Once, AtMostN, ExactlyN, ZeroOrMore, OneOrMore };
private:
    bool                 m_symm;
    multiplicity         m_multiplicity;
    optional<unsigned>   m_num;
    location             m_location;
    rewrite_info(bool symm, multiplicity m, optional<unsigned> const & n,
                 location const & loc):
        m_symm(symm), m_multiplicity(m), m_num(n), m_location(loc) {}
public:
    rewrite_info():m_symm(false), m_multiplicity(Once) {}
    static rewrite_info mk_once(bool symm, location const & loc) {
        return rewrite_info(symm, Once, optional<unsigned>(), loc);
    }

    static rewrite_info mk_at_most_n(unsigned n, bool symm, location const & loc) {
        return rewrite_info(symm, AtMostN, optional<unsigned>(n), loc);
    }

    static rewrite_info mk_exactly_n(unsigned n, bool symm, location const & loc) {
        return rewrite_info(symm, ExactlyN, optional<unsigned>(n), loc);
    }

    static rewrite_info mk_zero_or_more(bool symm, location const & loc) {
        return rewrite_info(symm, ZeroOrMore, optional<unsigned>(), loc);
    }

    static rewrite_info mk_one_or_more(bool symm, location const & loc) {
        return rewrite_info(symm, OneOrMore, optional<unsigned>(), loc);
    }

    bool symm() const {
        return m_symm;
    }

    multiplicity get_multiplicity() const {
        return m_multiplicity;
    }

    bool has_num() const {
        return multiplicity() == AtMostN || multiplicity() == ExactlyN;
    }

    unsigned num() const {
        lean_assert(has_num());
        return *m_num;
    }

    location const & get_location() const { return m_location; }

    friend serializer & operator<<(serializer & s, rewrite_info const & elem);
    friend deserializer & operator>>(deserializer & d, rewrite_info & e);
};

serializer & operator<<(serializer & s, rewrite_info const & e) {
    s << e.m_symm << static_cast<char>(e.m_multiplicity) << e.m_location;
    if (e.has_num())
        s << e.num();
    return s;
}

deserializer & operator>>(deserializer & d, rewrite_info & e) {
    char multp;
    d >> e.m_symm >> multp >> e.m_location;
    e.m_multiplicity = static_cast<rewrite_info::multiplicity>(multp);
    if (e.has_num())
        e.m_num = d.read_unsigned();
    return d;
}

static expr * g_rewrite_tac                   = nullptr;

static name * g_rewrite_elem_name             = nullptr;
static std::string * g_rewrite_elem_opcode    = nullptr;

static name * g_rewrite_unfold_name             = nullptr;
static std::string * g_rewrite_unfold_opcode    = nullptr;

[[ noreturn ]] static void throw_ru_ex() { throw exception("unexpected occurrence of 'rewrite unfold' expression"); }
[[ noreturn ]] static void throw_re_ex() { throw exception("unexpected occurrence of 'rewrite element' expression"); }

class rewrite_unfold_macro_cell : public macro_definition_cell {
    unfold_info m_info;
public:
    rewrite_unfold_macro_cell(unfold_info const & info):m_info(info) {}
    virtual name get_name() const { return *g_rewrite_unfold_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_ru_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_ru_ex(); }
    virtual void write(serializer & s) const {
        s << *g_rewrite_unfold_opcode << m_info;
    }
    unfold_info const & get_info() const { return m_info; }
};

expr mk_rewrite_unfold(name const & n, location const & loc) {
    macro_definition def(new rewrite_unfold_macro_cell(unfold_info(n, loc)));
    return mk_macro(def);
}

bool is_rewrite_unfold_step(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_rewrite_unfold_name;
}

unfold_info const & get_rewrite_unfold_info(expr const & e) {
    lean_assert(is_rewrite_unfold_step(e));
    return static_cast<rewrite_unfold_macro_cell const*>(macro_def(e).raw())->get_info();
}

class rewrite_element_macro_cell : public macro_definition_cell {
    rewrite_info m_info;
public:
    rewrite_element_macro_cell(rewrite_info const & info):m_info(info) {}
    virtual name get_name() const { return *g_rewrite_elem_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_re_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_re_ex(); }
    virtual void write(serializer & s) const {
        s << *g_rewrite_elem_opcode << m_info;
    }
    rewrite_info const & get_info() const { return m_info; }
};

expr mk_rw_macro(macro_definition const & def, optional<expr> const & pattern, expr const & H) {
    if (pattern) {
        expr args[2] = {H, *pattern};
        return mk_macro(def, 2, args);
    } else {
        return mk_macro(def, 1, &H);
    }
}

expr mk_rewrite_once(optional<expr> const & pattern, expr const & H, bool symm, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_once(symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_zero_or_more(optional<expr> const & pattern, expr const & H, bool symm, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_zero_or_more(symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_one_or_more(optional<expr> const & pattern, expr const & H, bool symm, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_one_or_more(symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_at_most_n(optional<expr> const & pattern, expr const & H, bool symm, unsigned n, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_at_most_n(n, symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

expr mk_rewrite_exactly_n(optional<expr> const & pattern, expr const & H, bool symm, unsigned n, location const & loc) {
    macro_definition def(new rewrite_element_macro_cell(rewrite_info::mk_exactly_n(n, symm, loc)));
    return mk_rw_macro(def, pattern, H);
}

bool is_rewrite_step(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_rewrite_elem_name;
}

bool has_rewrite_pattern(expr const & e) {
    lean_assert(is_rewrite_step(e));
    return macro_num_args(e) == 2;
}

expr const & get_rewrite_rule(expr const & e) {
    lean_assert(is_rewrite_step(e));
    return macro_arg(e, 0);
}

expr const & get_rewrite_pattern(expr const & e) {
    lean_assert(has_rewrite_pattern(e));
    return macro_arg(e, 1);
}

rewrite_info const & get_rewrite_info(expr const & e) {
    lean_assert(is_rewrite_step(e));
    return static_cast<rewrite_element_macro_cell const*>(macro_def(e).raw())->get_info();
}

expr mk_rewrite_tactic_expr(buffer<expr> const & elems) {
    lean_assert(std::all_of(elems.begin(), elems.end(), [](expr const & e) {
                return is_rewrite_step(e) || is_rewrite_unfold_step(e);
            }));
    return mk_app(*g_rewrite_tac, mk_expr_list(elems.size(), elems.data()));
}

class rewrite_match_plugin : public match_plugin {
#ifdef TRACE_MATCH_PLUGIN
    io_state       m_ios;
#endif
    type_checker & m_tc;
public:
#ifdef TRACE_MATCH_PLUGIN
    rewrite_match_plugin(io_state const & ios, type_checker & tc):
        m_ios(ios), m_tc(tc) {}
#else
    rewrite_match_plugin(io_state const &, type_checker & tc):
        m_tc(tc) {}
#endif

    bool is_projection_app(expr const & e) const {
        expr const & f = get_app_fn(e);
        return is_constant(f) && is_projection(m_tc.env(), const_name(f));
    }

    virtual bool on_failure(expr const & p, expr const & t, match_context & ctx) const {
        try {
            constraint_seq cs;
            // We do not unfold projections.
            expr p1 = is_projection_app(p) ? p : m_tc.whnf(p, cs);
            expr t1 = is_projection_app(t) ? t : m_tc.whnf(t, cs);
            return !cs && (p1 != p || t1 != t) && ctx.match(p1, t1);
        } catch (exception&) {
            return false;
        }
    }

    // Return true iff the given declaration contains inst_implicit arguments
    bool has_inst_implicit_args(name const & d) const {
        if (auto decl = m_tc.env().find(d)) {
            expr const * it = &decl->get_type();
            while (is_pi(*it)) {
                if (binding_info(*it).is_inst_implicit())
                    return true;
                it = &binding_body(*it);
            }
            return false;
        } else {
            return false;
        }
    }

    virtual lbool pre(expr const & p, expr const & t, match_context & ctx) const {
        if (!is_app(p) || !is_app(t))
            return l_undef;
        expr const & p_fn = get_app_fn(p);
        if (!is_constant(p_fn))
            return l_undef;
        expr const & t_fn = get_app_fn(t);
        if (!is_constant(t_fn))
            return l_undef;
        if (!ctx.match(p_fn, t_fn))
            return l_undef;
        projection_info const * info = get_projection_info(m_tc.env(), const_name(p_fn));
        if (info && info->m_inst_implicit) {
            // Special support for projections
            buffer<expr> p_args, t_args;
            get_app_args(p, p_args);
            get_app_args(t, t_args);
            if (p_args.size() != t_args.size())
                return l_false;
            for (unsigned i = 0; i < p_args.size(); i++) {
                if (i == info->m_nparams)
                    continue; // skip structure
                if (!ctx.match(p_args[i], t_args[i]))
                    return l_false;
            }
            return l_true;
        }
        if (has_inst_implicit_args(const_name(p_fn))) {
            // Special support for declarations that contains inst_implicit arguments.
            // The idea is to skip them during matching.
            buffer<expr> p_args, t_args;
            get_app_args(p, p_args);
            get_app_args(t, t_args);
            if (p_args.size() != t_args.size())
                return l_false;
            expr const * it = &m_tc.env().get(const_name(p_fn)).get_type();
            for (unsigned i = 0; i < p_args.size(); i++) {
                if (is_pi(*it) && binding_info(*it).is_inst_implicit()) {
                    it = &binding_body(*it);
                    continue; // skip argument
                }
                if (!ctx.match(p_args[i], t_args[i]))
                    return to_lbool(on_failure(p, t, ctx)); // try to unfold if possible
                if (is_pi(*it))
                    it = &binding_body(*it);
            }
            return l_true;
        }
        return l_undef;
    }
};

class rewrite_fn {
    environment          m_env;
    io_state             m_ios;
    elaborate_fn         m_elab;
    proof_state          m_ps;
    name_generator       m_ngen;
    type_checker_ptr     m_tc;
    rewrite_match_plugin m_mplugin;
    goal                 m_g;
    substitution         m_subst;
    expr                 m_expr_loc; // auxiliary expression used for error localization

    buffer<optional<level>> m_lsubst; // auxiliary buffer for pattern matching
    buffer<optional<expr>>  m_esubst; // auxiliary buffer for pattern matching

    [[ noreturn ]] void throw_rewrite_exception(char const * msg) {
        throw_generic_exception(msg, m_expr_loc);
    }

    [[ noreturn ]] void throw_rewrite_exception(sstream const & strm) {
        throw_generic_exception(strm, m_expr_loc);
    }

    expr mk_meta(expr const & type) {
        return m_g.mk_meta(m_ngen.next(), type);
    }

    void elaborate_elems(buffer<expr> const & elems, buffer<expr> & new_elems) {
        for (expr const & elem : elems) {
            if (is_rewrite_unfold_step(elem)) {
                // nothing to be done
                new_elems.push_back(elem);
            } else {
                expr rule = get_rewrite_rule(elem);
                auto rcs       = m_elab(m_g, m_ngen.mk_child(), rule, false);
                rule           = rcs.first;
                if (has_rewrite_pattern(elem)) {
                    auto pcs     = m_elab(m_g, m_ngen.mk_child(), get_rewrite_pattern(elem), false);
                    expr pattern = pcs.first;
                    // We ignore any constraints generated when elaborating patterns.
                    // The pattern is just a hint to locate positions where the rule should be applied.
                    expr new_args[2] = { rule, pattern };
                    new_elems.push_back(mk_macro(macro_def(elem), 2, new_args));
                } else {
                    new_elems.push_back(mk_macro(macro_def(elem), 1, &rule));
                }
            }
        }
    }

    bool process_unfold_step(expr const & elem) {
        lean_assert(is_rewrite_unfold_step(elem));
        // TODO(Leo)
        return false;
    }

    // Replace metavariables with special metavariables for the higher-order matcher. This is method is used when
    // converting an expression into a pattern.
    expr to_meta_idx(expr const & e) {
        m_lsubst.clear();
        m_esubst.clear();
        name_map<expr>  emap;
        name_map<level> lmap;

        auto to_meta_idx = [&](level const & l) {
            return replace(l, [&](level const & l) {
                    if (!has_meta(l)) {
                        return some_level(l);
                    } else if (is_meta(l)) {
                        if (auto it = lmap.find(meta_id(l))) {
                            return some_level(*it);
                        } else {
                            unsigned next_idx = m_lsubst.size();
                            level r = mk_idx_meta_univ(next_idx);
                            m_lsubst.push_back(none_level());
                            lmap.insert(meta_id(l), r);
                            return some_level(r);
                        }
                    } else {
                        return none_level();
                    }
                });
        };

        return replace(e, [&](expr const & e, unsigned) {
                if (!has_metavar(e)) {
                    return some_expr(e); // done
                } else if (is_binding(e)) {
                    throw_rewrite_exception("invalid rewrite tactic, pattern contains binders");
                } else if (is_meta(e)) {
                    expr const & fn = get_app_fn(e);
                    lean_assert(is_metavar(fn));
                    name const & n  = mlocal_name(fn);
                    if (auto it = emap.find(n)) {
                        return some_expr(*it);
                    } else {
                        unsigned next_idx = m_esubst.size();
                        expr r = mk_idx_meta(next_idx, m_tc->infer(e).first);
                        m_esubst.push_back(none_expr());
                        emap.insert(n, r);
                        return some_expr(r);
                    }
                } else if (is_constant(e)) {
                    levels ls = map(const_levels(e), [&](level const & l) { return to_meta_idx(l); });
                    return some_expr(update_constant(e, ls));
                } else {
                    return none_expr();
                }
            });
    }

    // Given the rewrite step \c e, return a pattern to be used to locate the term to be rewritten.
    expr get_pattern(expr const & e) {
        lean_assert(is_rewrite_step(e));
        if (has_rewrite_pattern(e)) {
            return to_meta_idx(get_rewrite_pattern(e));
        } else {
            // Remark: we discard constraints generated producing the pattern.
            // Patterns are only used to locate positions where the rule should be applied.
            expr rule      = get_rewrite_rule(e);
            expr rule_type = m_tc->whnf(m_tc->infer(rule).first).first;
            while (is_pi(rule_type)) {
                expr meta  = mk_meta(binding_domain(rule_type));
                rule_type  = m_tc->whnf(instantiate(binding_body(rule_type), meta)).first;
            }
            if (!is_eq(rule_type))
                throw_rewrite_exception("invalid rewrite tactic, given lemma is not an equality");
            if (get_rewrite_info(e).symm()) {
                return to_meta_idx(app_arg(rule_type));
            } else {
                return to_meta_idx(app_arg(app_fn(rule_type)));
            }
        }
    }

    // Set m_esubst and m_lsubst elements to none
    void reset_subst() {
        for (optional<level> & l : m_lsubst)
            l = none_level();
        for (optional<expr> & e : m_esubst)
            e = none_expr();
    }

    optional<expr> find_target(expr const & e, expr const & pattern) {
        optional<expr> found;
        for_each(e, [&](expr const & t, unsigned) {
                if (found)
                    return false; // stop search
                if (closed(t)) {
                    lean_assert(std::all_of(m_esubst.begin(), m_esubst.end(), [&](optional<expr> const & e) { return !e; }));
                    bool assigned = false;
                    bool r = match(pattern, t, m_lsubst, m_esubst, nullptr, nullptr, &m_mplugin, &assigned);
                    if (assigned)
                        reset_subst();
                    if (r) {
                        found = t;
                        return false;
                    }
                }
                return true;
            });
        return found;
    }

    bool process_rewrite_hypothesis(expr const & hyp, expr const & elem, expr const & pattern) {
        // TODO(Leo)
        return false;
    }

    bool process_rewrite_goal(expr const & elem, expr const & pattern) {
        expr goal_type = m_g.get_type();
        if (auto it = find_target(goal_type, pattern)) {
            regular(m_env, m_ios) << "found: " << *it << "\n";
            // TODO(Leo)
            return false;
        } else {
            return false;
        }
    }

    bool process_rewrite_single_step(expr const & elem, expr const & pattern) {
        check_system("rewrite tactic");
        rewrite_info const & info = get_rewrite_info(elem);
        location const & loc      = info.get_location();
        if (loc.is_goal_only())
            return process_rewrite_goal(elem, pattern);
        bool progress = false;
        buffer<expr> hyps;
        m_g.get_hyps(hyps);
        for (expr const & h : hyps) {
            if (!loc.includes_hypothesis(local_pp_name(h)))
                continue;
            if (process_rewrite_hypothesis(h, elem, pattern))
                progress = true;
        }
        if (loc.includes_goal() && process_rewrite_goal(elem, pattern))
            progress = true;
        return progress;
    }

    bool process_rewrite_step(expr const & elem) {
        lean_assert(is_rewrite_step(elem));
        expr pattern              = get_pattern(elem);
        regular(m_env, m_ios) << "pattern: " << pattern << "\n";
        rewrite_info const & info = get_rewrite_info(elem);
        unsigned num;
        switch (info.get_multiplicity()) {
        case rewrite_info::Once:
            return process_rewrite_single_step(elem, pattern);
        case rewrite_info::AtMostN:
            num = info.num();
            for (unsigned i = 0; i < num; i++) {
                if (!process_rewrite_single_step(elem, pattern))
                    return true;
            }
            return true;
        case rewrite_info::ExactlyN:
            num = info.num();
            for (unsigned i = 0; i < num; i++) {
                if (!process_rewrite_single_step(elem, pattern))
                    return false;
            }
            return true;
        case rewrite_info::ZeroOrMore:
            while (true) {
                if (!process_rewrite_single_step(elem, pattern))
                    return true;
            }
        case rewrite_info::OneOrMore:
            if (!process_rewrite_single_step(elem, pattern))
                return false;
            while (true) {
                if (!process_rewrite_single_step(elem, pattern))
                    return true;
            }
        }
        lean_unreachable();
    }

    // Process the given rewrite element/step. This method destructively update
    // m_g, m_subst, m_ngen. It returns true if it succeeded and false otherwise.
    bool process_step(expr const & elem) {
        if (is_rewrite_unfold_step(elem)) {
            return process_unfold_step(elem);
        } else {
            return process_rewrite_step(elem);
        }
    }

public:
    rewrite_fn(environment const & env, io_state const & ios, elaborate_fn const & elab, proof_state const & ps):
        m_env(env), m_ios(ios), m_elab(elab), m_ps(ps), m_ngen(ps.get_ngen()),
        m_tc(mk_type_checker(m_env, m_ngen.mk_child(), ps.relax_main_opaque())),
        m_mplugin(m_ios, *m_tc) {
        goals const & gs = m_ps.get_goals();
        lean_assert(gs);
        m_g     = head(gs);
        m_subst = m_ps.get_subst();
    }

    proof_state_seq operator()(buffer<expr> const & elems) {
        std::cout << "rewrite_tactic\n";
        buffer<expr> new_elems;
        elaborate_elems(elems, new_elems);

        lean_assert(elems.size() == new_elems.size());
        for (unsigned i = 0; i < new_elems.size(); i++) {
            flet<expr> set1(m_expr_loc, elems[i]);
            if (!process_step(new_elems[i])) {
                return proof_state_seq();
            }
        }

        return proof_state_seq(m_ps);
    }
};

tactic mk_rewrite_tactic(elaborate_fn const & elab, buffer<expr> const & elems) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs))
                return proof_state_seq();
            return rewrite_fn(env, ios, elab, s)(elems);
        });
}

void initialize_rewrite_tactic() {
    name rewrite_tac_name{"tactic", "rewrite_tac"};
    g_rewrite_tac           = new expr(Const(rewrite_tac_name));
    g_rewrite_unfold_name   = new name("rewrite_unfold");
    g_rewrite_unfold_opcode = new std::string("RWU");
    g_rewrite_elem_name     = new name("rewrite_element");
    g_rewrite_elem_opcode   = new std::string("RWE");
    register_macro_deserializer(*g_rewrite_unfold_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    unfold_info info;
                                    d >> info;
                                    macro_definition def(new rewrite_unfold_macro_cell(info));
                                    return mk_macro(def);
                                });
    register_macro_deserializer(*g_rewrite_elem_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1 && num != 2)
                                        throw corrupted_stream_exception();
                                    rewrite_info info;
                                    d >> info;
                                    macro_definition def(new rewrite_element_macro_cell(info));
                                    return mk_macro(def, num, args);
                                });
    register_tac(rewrite_tac_name,
                 [](type_checker &, elaborate_fn const & elab, expr const & e, pos_info_provider const *) {
                     buffer<expr> args;
                     get_tactic_expr_list_elements(app_arg(e), args, "invalid 'rewrite' tactic, invalid argument");
                     for (expr const & arg : args) {
                         if (!is_rewrite_step(arg) && !is_rewrite_unfold_step(arg))
                             throw expr_to_tactic_exception(e, "invalid 'rewrite' tactic, invalid argument");
                     }
                     return mk_rewrite_tactic(elab, args);
                 });
}

void finalize_rewrite_tactic() {
    delete g_rewrite_tac;
    delete g_rewrite_unfold_name;
    delete g_rewrite_unfold_opcode;
    delete g_rewrite_elem_name;
    delete g_rewrite_elem_opcode;
}
}
