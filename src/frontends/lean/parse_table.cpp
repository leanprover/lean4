/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/rb_map.h"
#include "kernel/free_vars.h"
#include "frontends/lean/parse_table.h"
namespace lean {
namespace notation {
struct action_cell {
    action_kind m_kind;
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc();

    action_cell(action_kind k):m_kind(k), m_rc(1) {}
};

struct expr_action_cell : public action_cell {
    unsigned m_rbp;

    expr_action_cell(action_kind k, unsigned rbp):
        action_cell(k), m_rbp(rbp) {}

    expr_action_cell(unsigned rbp):
        expr_action_cell(action_kind::Expr, rbp) {}
};

struct exprs_action_cell : public expr_action_cell {
    name  m_token_sep;
    expr  m_rec;
    expr  m_ini;
    bool  m_fold_right;

    exprs_action_cell(name const & sep, expr const & rec, expr const & ini, bool right,
                      unsigned rbp):
        expr_action_cell(action_kind::Exprs, rbp),
        m_token_sep(sep), m_rec(rec), m_ini(ini), m_fold_right(right) {}
};

struct scoped_expr_action_cell : public expr_action_cell {
    expr m_rec;

    scoped_expr_action_cell(expr const & rec, unsigned rb):
        expr_action_cell(action_kind::ScopedExpr, rb),
        m_rec(rec) {}
};

struct ext_action_cell : public action_cell {
    parse_fn m_parse_fn;
    ext_action_cell(parse_fn const & fn):
        action_cell(action_kind::Ext), m_parse_fn(fn) {}
};

action::action(action_cell * ptr):m_ptr(ptr) { lean_assert(ptr); }
action::action():action(g_skip_action) {}
action::action(action const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
action::action(action && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
action::~action() { if (m_ptr) m_ptr->dec_ref(); }
action & action::operator=(action const & s) { LEAN_COPY_REF(s); }
action & action::operator=(action && s) { LEAN_MOVE_REF(s); }
action_kind action::kind() const { return m_ptr->m_kind; }
expr_action_cell * to_expr_action(action_cell * c) {
    lean_assert(c->m_kind == action_kind::Expr || c->m_kind == action_kind::Exprs);
    return static_cast<expr_action_cell*>(c);
}
exprs_action_cell * to_exprs_action(action_cell * c) {
    lean_assert(c->m_kind == action_kind::Exprs);
    return static_cast<exprs_action_cell*>(c);
}
scoped_expr_action_cell * to_scoped_expr_action(action_cell * c) {
    lean_assert(c->m_kind == action_kind::ScopedExpr);
    return static_cast<scoped_expr_action_cell*>(c);
}
ext_action_cell * to_ext_action(action_cell * c) {
    lean_assert(c->m_kind == action_kind::Ext);
    return static_cast<ext_action_cell*>(c);
}
unsigned action::rbp() const { return to_expr_action(m_ptr)->m_rbp; }
name const & action::get_sep() const { return to_exprs_action(m_ptr)->m_token_sep; }
expr const & action::get_rec() const { return to_exprs_action(m_ptr)->m_rec; }
expr const & action::get_initial() const { return to_exprs_action(m_ptr)->m_ini; }
bool action::is_fold_right() const { return to_exprs_action(m_ptr)->m_fold_right; }
parse_fn const & action::get_parse_fn() const { return to_ext_action(m_ptr)->m_parse_fn; }
bool action::is_compatible(action const & a) const {
    if (kind() != a.kind())
        return false;
    switch (kind()) {
    case action_kind::Skip: case action_kind::Binder: case action_kind::Binders:
        return true;
    case action_kind::Ext:
        return m_ptr == a.m_ptr;
    case action_kind::Expr:
        return rbp() == a.rbp();
    case action_kind::Exprs:
        return
            rbp() == a.rbp() &&
            get_rec() == a.get_rec() &&
            get_initial() == a.get_initial() &&
            is_fold_right() == a.is_fold_right();
    case action_kind::ScopedExpr:
        return
            rbp() == a.rbp() &&
            get_rec() == a.get_rec();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

void action_cell::dealloc() {
    switch (m_kind) {
    case action_kind::Expr:       delete(to_expr_action(this)); break;
    case action_kind::Exprs:      delete(to_exprs_action(this)); break;
    case action_kind::ScopedExpr: delete(to_exprs_action(this)); break;
    case action_kind::Ext:        delete(to_scoped_expr_action(this)); break;
    default:                      delete this; break;
    }
}

action action::g_skip_action(new action_cell(action_kind::Skip));
action action::g_binder_action(new action_cell(action_kind::Binder));
action action::g_binders_action(new action_cell(action_kind::Binders));

action mk_skip_action() { return action::g_skip_action; }
action mk_binder_action() { return action::g_binder_action; }
action mk_binders_action() { return action::g_binders_action; }
action mk_expr_action(unsigned rbp) { return action(new expr_action_cell(rbp)); }
action mk_exprs_action(name const & sep, expr const & rec, expr const & ini, bool right, unsigned rbp) {
    if (get_free_var_range(rec) > 2)
        throw exception("invalid notation, the expression used to combine a sequence of expressions "
                        "must not contain free variables with de Bruijn indices greater than 1");
    return action(new exprs_action_cell(sep, rec, ini, right, rbp));
}
action mk_scoped_expr_action(expr const & rec, unsigned rb) {
    return action(new scoped_expr_action_cell(rec, rb));
}
action mk_ext_parse_action(parse_fn const & fn) { return action(new ext_action_cell(fn)); }

struct parse_table::cell {
    list<expr>                                                   m_accept;
    rb_map<name, std::pair<action, parse_table>, name_quick_cmp> m_children;
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc() { delete this; }
    cell():m_rc(1) {}
    cell(cell const & c):m_accept(c.m_accept), m_children(c.m_children), m_rc(1) {}
};

parse_table::parse_table(cell * c):m_ptr(c) {}
parse_table::parse_table():m_ptr(new cell()) {}
parse_table::parse_table(parse_table const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
parse_table::parse_table(parse_table && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
parse_table::~parse_table() { if (m_ptr) m_ptr->dec_ref(); }
parse_table & parse_table::operator=(parse_table const & s) { LEAN_COPY_REF(s); }
parse_table & parse_table::operator=(parse_table && s) { LEAN_MOVE_REF(s); }
optional<std::pair<action, parse_table>> parse_table::find(name const & tk) const {
    auto * it = m_ptr->m_children.find(tk);
    if (it)
        return optional<std::pair<action, parse_table>>(*it);
    else
        return optional<std::pair<action, parse_table>>();
}

list<expr> const & parse_table::is_accepting() const {
    return m_ptr->m_accept;
}

// scoped_expr_actions must occur after a Binder/Binders.
static void validate_transitions(unsigned num, transition const * ts, expr const & a) {
    unsigned nargs = 0;
    bool found_binder = false;
    for (unsigned i = 0; i < num; i++) {
        action const & a = ts[i].get_action();
        switch (a.kind()) {
        case action_kind::Binder: case action_kind::Binders:
            found_binder = true;
            break;
        case action_kind::Expr: case action_kind::Exprs: case action_kind::Ext:
            nargs++;
            break;
        case action_kind::ScopedExpr:
            if (!found_binder)
                throw exception("invalid notation declaration, a scoped expression must occur after a binder element");
            nargs++;
            break;
        case action_kind::Skip:
            break;
        }
    }
    if (get_free_var_range(a) > nargs)
        throw exception("invalid notation declaration, expression template has more free variables than arguments");
}

parse_table parse_table::add(unsigned num, transition const * ts, expr const & a, bool overload) const {
    validate_transitions(num, ts, a);
    parse_table r(*this);
    if (num == 0) {
        if (overload)
            r.m_ptr->m_accept = list<expr>(a);
        else
            r.m_ptr->m_accept = list<expr>(a, r.m_ptr->m_accept);
    } else {
        auto * it = r.m_ptr->m_children.find(ts->get_token());
        parse_table new_child;
        if (it) {
            action const & act        = it->first;
            parse_table const & child = it->second;
            if (act.is_compatible(ts->get_action())) {
                new_child = child.add(num-1, ts+1, a, overload);
            } else {
                new_child = parse_table().add(num-1, ts+1, a, overload);
            }
        } else {
            new_child = parse_table().add(num-1, ts+1, a, overload);
        }
        r.m_ptr->m_children.insert(ts->get_token(), mk_pair(ts->get_action(), new_child));
    }
    return r;
}

void parse_table::for_each(buffer<transition> & ts, std::function<void(unsigned, transition const *, list<expr> const &)> const & fn) const {
    if (!is_nil(m_ptr->m_accept))
        fn(ts.size(), ts.data(), m_ptr->m_accept);
    m_ptr->m_children.for_each([&](name const & k, std::pair<action, parse_table> const & p) {
            ts.push_back(transition(k, p.first));
            for_each(ts, fn);
            ts.pop_back();
        });
}

void parse_table::for_each(std::function<void(unsigned, transition const *, list<expr> const &)> const & fn) const {
    buffer<transition> tmp;
    for_each(tmp, fn);
}

parse_table parse_table::merge(parse_table const & s, bool overload) const {
    parse_table r(*this);
    s.for_each([&](unsigned num, transition const * ts, list<expr> const & accept) {
            for (expr const & a : accept)
                r = r.add(num, ts, a, overload);
        });
    return r;
}
}
}
