/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/replace_visitor.h"
#include "library/blast/state.h"

namespace lean {
namespace blast {
bool metavar_decl::restrict_context_using(metavar_decl const & other) {
    buffer<unsigned> to_erase;
    m_assumptions.for_each([&](unsigned hidx) {
            if (!other.contains_href(hidx))
                to_erase.push_back(hidx);
        });
    for (unsigned hidx : to_erase)
        m_assumptions.erase(hidx);
    return !to_erase.empty();
}

state::state():m_next_uref_index(0), m_next_mref_index(0) {}

/** \brief Mark that hypothesis h with index hidx is fixed by the meta-variable midx.
    That is, `h` occurs in the type of `midx`. */
void state::add_fixed_by(unsigned hidx, unsigned midx) {
    if (auto s = m_fixed_by.find(hidx)) {
        if (!s->contains(midx)) {
            metavar_idx_set new_s(*s);
            new_s.insert(midx);
            m_fixed_by.insert(hidx, new_s);
        }
    } else {
        metavar_idx_set new_s;
        new_s.insert(midx);
        m_fixed_by.insert(hidx, new_s);
    }
}

level state::mk_uref() {
    unsigned idx = m_next_mref_index;
    m_next_mref_index++;
    return blast::mk_uref(idx);
}

expr state::mk_metavar(hypothesis_idx_set const & c, expr const & type) {
    unsigned midx = m_next_mref_index;
    for_each(type, [&](expr const & e, unsigned) {
            if (!has_href(e))
                return false;
            if (is_href(e)) {
                lean_assert(c.contains(href_index(e)));
                add_fixed_by(href_index(e), midx);
                return false;
            }
            return true; // continue search
        });
    m_next_mref_index++;
    m_metavar_decls.insert(midx, metavar_decl(c, type));
    return blast::mk_mref(midx);
}

expr state::mk_metavar(hypothesis_idx_buffer const & b, expr const & type) {
    hypothesis_idx_set ctx;
    for (unsigned const & hidx : b)
        ctx.insert(hidx);
    return mk_metavar(ctx, type);
}

expr state::mk_metavar(expr const & type) {
    return state::mk_metavar(m_main.get_assumptions(), type);
}

void state::restrict_mref_context_using(expr const & mref1, expr const & mref2) {
    metavar_decl const * d1 = m_metavar_decls.find(mref_index(mref1));
    metavar_decl const * d2 = m_metavar_decls.find(mref_index(mref2));
    lean_assert(d1);
    lean_assert(d2);
    metavar_decl new_d1(*d1);
    if (new_d1.restrict_context_using(*d2))
        m_metavar_decls.insert(mref_index(mref1), new_d1);
}

goal state::to_goal(branch const & b) const {
    hypothesis_idx_map<expr> hidx2local;
    metavar_idx_map<expr>    midx2meta;
    name M("M");
    std::function<expr(expr const &)> convert = [&](expr const & e) {
        return lean::replace(e, [&](expr const & e) {
                if (is_href(e)) {
                    auto r = hidx2local.find(href_index(e));
                    lean_assert(r);
                    return some_expr(*r);
                } else if (is_mref(e)) {
                    auto r = midx2meta.find(mref_index(e));
                    if (r) {
                        return some_expr(*r);
                    } else {
                        metavar_decl const * decl = m_metavar_decls.find(mref_index(e));
                        lean_assert(decl);
                        buffer<expr> ctx;
                        decl->get_assumptions().for_each([&](unsigned hidx) {
                                ctx.push_back(*hidx2local.find(hidx));
                            });
                        expr type     = convert(decl->get_type());
                        expr new_type = Pi(ctx, type);
                        expr new_mvar = lean::mk_metavar(name(M, mref_index(e)), new_type);
                        expr new_meta = mk_app(new_mvar, ctx);
                        midx2meta.insert(mref_index(e), new_meta);
                        return some_expr(new_meta);
                    }
                } else {
                    return none_expr();
                }
            });
    };
    name H("H");
    hypothesis_idx_buffer hidxs;
    b.get_sorted_hypotheses(hidxs);
    buffer<expr> hyps;
    for (unsigned hidx : hidxs) {
        hypothesis const * h = b.get(hidx);
        lean_assert(h);
        // after we add support for let-decls in goals, we must convert back h->get_value() if it is available
        expr new_h = lean::mk_local(name(H, hidx), h->get_name(), convert(h->get_type()), binder_info());
        hidx2local.insert(hidx, new_h);
        hyps.push_back(new_h);
    }
    expr new_target    = convert(b.get_target());
    expr new_mvar_type = Pi(hyps, new_target);
    expr new_mvar      = lean::mk_metavar(M, new_mvar_type);
    expr new_meta      = mk_app(new_mvar, hyps);
    return goal(new_meta, new_target);
}

goal state::to_goal() const {
    return to_goal(m_main);
}

void state::display(environment const & env, io_state const & ios) const {
    formatter fmt = ios.get_formatter_factory()(env, ios.get_options());
    ios.get_diagnostic_channel() << mk_pair(to_goal().pp(fmt), ios.get_options());
}

bool state::has_assigned_uref(level const & l) const {
    if (!has_meta(l))
        return false;
    if (m_uassignment.empty())
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (is_uref(l) && is_uref_assigned(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

bool state::has_assigned_uref(levels const & ls) const {
    for (level const & l : ls) {
        if (has_assigned_uref(l))
            return true;
    }
    return false;
}

bool state::has_assigned_uref_mref(expr const & e) const {
    if (!has_mref(e) && !has_univ_metavar(e))
        return false;
    if (m_eassignment.empty() && m_uassignment.empty())
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_mref(e) && !has_univ_metavar(e))
                return false; // stop search
            if (found)
                return false; // stop search
            if ((is_mref(e) && is_mref_assigned(e)) ||
                (is_constant(e) && has_assigned_uref(const_levels(e))) ||
                (is_sort(e) && has_assigned_uref(sort_level(e)))) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

level state::instantiate_urefs(level const & l) {
    if (!has_assigned_uref(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_uref(l)) {
                level const * v1 = get_uref_assignment(l);
                if (v1) {
                    level v2 = instantiate_urefs(*v1);
                    if (*v1 != v2) {
                        assign_uref(l, v2);
                        return some_level(v2);
                    } else {
                        return some_level(*v1);
                    }
                }
            }
            return none_level();
        });
}

struct instantiate_urefs_mrefs_fn : public replace_visitor {
    state & m_state;

    level visit_level(level const & l) {
        return m_state.instantiate_urefs(l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_local(expr const & e) {
        if (is_href(e)) {
            return e;
        } else {
            return update_mlocal(e, visit(mlocal_type(e)));
        }
    }

    virtual expr visit_meta(expr const & m) {
        lean_assert(is_mref(m));
        if (auto v1 = m_state.get_mref_assignment(m)) {
            if (!has_mref(*v1)) {
                return *v1;
            } else {
                expr v2 = m_state.instantiate_urefs_mrefs(*v1);
                if (v2 != *v1)
                    m_state.assign_mref(m, v2);
                return v2;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (is_mref(f)) {
            if (auto v = m_state.get_mref_assignment(f)) {
                expr new_app = apply_beta(*v, args.size(), args.data());
                if (has_mref(new_app))
                    return visit(new_app);
                else
                    return new_app;
            }
        }
        expr new_f = visit(f);
        buffer<expr> new_args;
        bool modified = !is_eqp(new_f, f);
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified)
            return e;
        else
            return mk_rev_app(new_f, new_args, e.get_tag());
    }

    virtual expr visit_macro(expr const & e) {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    virtual expr visit(expr const & e) {
        if (!has_mref(e) || !has_univ_metavar(e))
            return e;
        else
            return replace_visitor::visit(e);
    }

public:
    instantiate_urefs_mrefs_fn(state & s):m_state(s) {}
    expr operator()(expr const & e) { return visit(e); }
};

expr state::instantiate_urefs_mrefs(expr const & e) {
    if (!has_assigned_uref_mref(e))
        return e;
    else
        return instantiate_urefs_mrefs_fn(*this)(e);
}

#ifdef LEAN_DEBUG
bool state::check_hypothesis(expr const & e, branch const & b, unsigned hidx, hypothesis const & h) const {
    lean_assert(closed(e));
    for_each(e, [&](expr const & n, unsigned) {
            lean_assert(!blast::is_local(n));
            if (is_href(n)) {
                lean_assert(h.depends_on(n));
                lean_assert(b.hidx_depends_on(hidx, href_index(n)));
            } else if (is_mref(n)) {
                // metavariable is in the set of used metavariables
                lean_assert(b.has_mvar(n));
            }
            return true;
        });
    return true;
}

bool state::check_hypothesis(branch const & b, unsigned hidx, hypothesis const & h) const {
    lean_assert(check_hypothesis(h.get_type(), b, hidx, h));
    lean_assert(h.is_assumption() || check_hypothesis(h.get_value(), b, hidx, h));
    return true;
}

bool state::check_target(branch const & b) const {
    lean_assert(closed(b.get_target()));
    for_each(b.get_target(), [&](expr const & n, unsigned) {
            lean_assert(!blast::is_local(n));
            if (is_href(n)) {
                lean_assert(b.target_depends_on(n));
            } else if (is_mref(n)) {
                // metavariable is in the set of used metavariables
                lean_assert(b.has_mvar(n));
            }
            return true;
        });
    return true;
}

bool state::check_invariant(branch const & b) const {
    b.for_each_hypothesis([&](unsigned hidx, hypothesis const & h) {
            lean_assert(check_hypothesis(b, hidx, h));
        });
    lean_assert(check_target(b));
    return true;
}

bool state::check_invariant() const {
    return check_invariant(m_main);
}
#endif
}}
