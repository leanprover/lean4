/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <utility>
#include "runtime/sstream.h"
#include "util/rb_map.h"
#include "kernel/replace_fn.h"
#include "library/io_state_stream.h"
#include "library/annotation.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/parser.h"

namespace lean {
namespace notation {
/** \brief Annotate subterms of "macro" \c e with no_info annotation.

    1- Variables are not annotated.
    2- A constant f in a macro (f ...) is not annotated if (root == true).
    3- Every other subterm is annotated with no_info.
*/
static expr annotate_macro_subterms(expr const & e, bool root = true) {
    if (is_var(e))
        return e;
    if (is_binding(e))
        return update_binding(e,
                              annotate_macro_subterms(binding_domain(e), root),
                              annotate_macro_subterms(binding_body(e), root));
    buffer<expr> args;
    bool modified  = false;
    expr const & f = get_app_args(e, args);
    expr new_f;
    if (is_constant(f) && root) {
        new_f = f;
    } else if (is_annotation(f)) {
        name const & k   = get_annotation_kind(f);
        expr const & arg = get_annotation_arg(f);
        expr new_arg     = annotate_macro_subterms(arg, true);
        if (is_eqp(new_arg, arg)) {
            new_f    = f;
        } else {
            new_f    = mk_annotation(k, new_arg);
            modified = true;
        }
    } else {
        new_f    = f;
        modified = true;
    }
    for (expr & arg : args) {
        expr new_arg = annotate_macro_subterms(arg, false);
        if (!is_eqp(new_arg, arg)) {
            arg      = new_arg;
            modified = true;
        }
    }
    if (!modified)
        return e;
    return mk_app(new_f, args);
}

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

struct binder_action_cell : public expr_action_cell {
    binder_action_cell(unsigned rbp):
        expr_action_cell(action_kind::Binder, rbp) {}
};

struct binders_action_cell : public expr_action_cell {
    binders_action_cell(unsigned rbp):
        expr_action_cell(action_kind::Binders, rbp) {}
};

struct exprs_action_cell : public expr_action_cell {
    name           m_token_sep;
    expr           m_rec;
    optional<expr> m_ini;
    optional<name> m_terminator;
    bool           m_fold_right;
    exprs_action_cell(name const & sep, expr const & rec, optional<expr> const & ini,
                      optional<name> const & terminator, bool right, unsigned rbp):
        expr_action_cell(action_kind::Exprs, rbp),
        m_token_sep(sep), m_rec(rec), m_ini(ini), m_terminator(terminator), m_fold_right(right) {}
};

struct scoped_expr_action_cell : public expr_action_cell {
    expr m_rec;
    bool m_lambda;
    scoped_expr_action_cell(expr const & rec, unsigned rb, bool lambda):
        expr_action_cell(action_kind::ScopedExpr, rb),
        m_rec(rec),
        m_lambda(lambda) {}
};

struct ext_action_cell : public action_cell {
    parse_fn m_parse_fn;
    ext_action_cell(parse_fn const & fn):
        action_cell(action_kind::Ext), m_parse_fn(fn) {}
};

action::action(action_cell * ptr):m_ptr(ptr) { lean_assert(ptr); }
action::action():action(mk_skip_action()) {}
action::action(action const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
action::action(action && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
action::~action() { if (m_ptr) m_ptr->dec_ref(); }
action & action::operator=(action const & s) { LEAN_COPY_REF(s); }
action & action::operator=(action && s) { LEAN_MOVE_REF(s); }
action_kind action::kind() const { return m_ptr->m_kind; }
expr_action_cell * to_expr_action(action_cell * c) {
    lean_assert(c->m_kind == action_kind::Expr || c->m_kind == action_kind::Exprs || c->m_kind == action_kind::ScopedExpr ||
                c->m_kind == action_kind::Binder || c->m_kind == action_kind::Binders);
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
optional<name> const & action::get_terminator() const { return to_exprs_action(m_ptr)->m_terminator; }
expr const & action::get_rec() const {
    if (kind() == action_kind::ScopedExpr)
        return to_scoped_expr_action(m_ptr)->m_rec;
    else
        return to_exprs_action(m_ptr)->m_rec;
}
bool action::use_lambda_abstraction() const { return to_scoped_expr_action(m_ptr)->m_lambda; }
optional<expr> const & action::get_initial() const { return to_exprs_action(m_ptr)->m_ini; }
bool action::is_fold_right() const { return to_exprs_action(m_ptr)->m_fold_right; }
parse_fn const & action::get_parse_fn() const { return to_ext_action(m_ptr)->m_parse_fn; }
bool action::is_equal(action const & a) const {
    if (kind() != a.kind())
        return false;
    switch (kind()) {
    case action_kind::Skip:
        return true;
    case action_kind::Binder: case action_kind::Binders: case action_kind::Expr:
        return rbp() == a.rbp();
    case action_kind::Ext:
        return m_ptr == a.m_ptr;
    case action_kind::Exprs:
        return
            rbp() == a.rbp() &&
            get_sep() == a.get_sep() &&
            get_rec() == a.get_rec() &&
            get_initial() == a.get_initial() &&
            get_terminator() == a.get_terminator() &&
            is_fold_right() == a.is_fold_right();
    case action_kind::ScopedExpr:
        return
            rbp() == a.rbp() &&
            get_rec() == a.get_rec();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
// Similar to is_equal, but ignores information that is "irrelevant" for parsing.
// For example, for Exprs actions, get_rec and get_initial are not relevant when parsing the input stream.
// We only need them when we reach an accepting state.
bool action::is_equivalent(action const & a) const {
    if (kind() != a.kind())
        return false;
    switch (kind()) {
    case action_kind::Exprs:
        return
            rbp() == a.rbp() &&
            get_sep() == a.get_sep() &&
            get_terminator() == a.get_terminator();
    case action_kind::ScopedExpr:
        return rbp() == a.rbp();
    default:
        return is_equal(a);
    }
}

static bool is_compatible_core(action_kind k1, action_kind k2) {
    return k1 == action_kind::Skip && (k2 == action_kind::Expr || k2 == action_kind::Exprs || k2 == action_kind::ScopedExpr);
}

bool action::is_compatible(action const & a) const {
    if (is_equivalent(a))
        return true;
    auto k1 = kind();
    auto k2 = a.kind();
    return is_compatible_core(k1, k2) || is_compatible_core(k2, k1);
}
void action::display(io_state_stream & out) const {
    switch (kind()) {
    case action_kind::Skip:    out << "skip"; break;
    case action_kind::Binder:
        if (rbp() != 0)
            out << "binder:" << rbp();
        else
            out << "binder";
        break;
    case action_kind::Binders:
        if (rbp() != 0)
            out << "binders:" << rbp();
        else
            out << "binders";
        break;
    case action_kind::Ext:     out << "builtin"; break;
    case action_kind::Expr:    out << rbp(); break;
    case action_kind::Exprs:
        out << "(fold" << (is_fold_right() ? "r" : "l");
        if (get_terminator())
            out << "*";
        out << " " << rbp() << " `" << get_sep() << "`";
        if (get_terminator())
            out << " `" << *get_terminator() << "`";
        out << ")";
        break;
    case action_kind::ScopedExpr:
        out << "(scoped " << rbp() << ")";
        break;
    }
}

bool action::is_simple() const {
    return kind() != action_kind::Ext;
}

void action_cell::dealloc() {
    switch (m_kind) {
    case action_kind::Expr:       delete(to_expr_action(this)); break;
    case action_kind::Binder:     delete(to_expr_action(this)); break;
    case action_kind::Binders:    delete(to_expr_action(this)); break;
    case action_kind::Exprs:      delete(to_exprs_action(this)); break;
    case action_kind::ScopedExpr: delete(to_scoped_expr_action(this)); break;
    case action_kind::Ext:        delete(to_ext_action(this)); break;
    default:                      delete this; break;
    }
}

static action * g_skip_action = nullptr;
action mk_skip_action() { return *g_skip_action; }

void initialize_parse_table() {
    g_skip_action    = new action(new action_cell(action_kind::Skip));
}

void finalize_parse_table() {
    delete g_skip_action;
}

action mk_binder_action(unsigned rbp) { return action(new binder_action_cell(rbp)); }
action mk_binders_action(unsigned rbp) { return action(new binders_action_cell(rbp)); }
action mk_expr_action(unsigned rbp) { return action(new expr_action_cell(rbp)); }
action mk_exprs_action(name const & sep, expr const & rec, optional<expr> const & ini,
                       optional<name> const & terminator, bool right, unsigned rbp) {
    if (get_loose_bvar_range(rec) > 2)
        throw exception("invalid notation, the expression used to combine a sequence of expressions "
                        "must not contain bound variables with de Bruijn indices greater than 1");
    expr new_rec = annotate_macro_subterms(rec);
    optional<expr> new_ini = ini ? some_expr(annotate_macro_subterms(*ini)) : none_expr();
    return action(new exprs_action_cell(sep, new_rec, new_ini, terminator, right, rbp));
}
action mk_scoped_expr_action(expr const & rec, unsigned rb, bool lambda) {
    expr new_rec = annotate_macro_subterms(rec);
    return action(new scoped_expr_action_cell(new_rec, rb, lambda));
}
action mk_ext_action_core(parse_fn const & fn) { return action(new ext_action_cell(fn)); }
action mk_ext_action(parse_fn const & fn) {
    auto new_fn = [=](parser & p, unsigned num, expr const * args, pos_info const & pos) -> expr {
        p.next();
        return fn(p, num, args, pos);
    };
    return action(new ext_action_cell(new_fn));
}

action replace(action const & a, std::function<expr(expr const &)> const & f) {
    switch (a.kind()) {
    case action_kind::Skip: case action_kind::Binder: case action_kind::Binders:
    case action_kind::Ext:  case action_kind::Expr:
        return a;
    case action_kind::Exprs:
        return mk_exprs_action(a.get_sep(), f(a.get_rec()), a.get_initial() ? some_expr(f(*a.get_initial())) : none_expr(), a.get_terminator(),
                               a.is_fold_right(), a.rbp());
    case action_kind::ScopedExpr:
        return mk_scoped_expr_action(f(a.get_rec()), a.rbp(), a.use_lambda_abstraction());
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

transition replace(transition const & t, std::function<expr(expr const &)> const & f) {
    return transition(t.get_token(), replace(t.get_action(), f), t.get_pp_token());
}

struct parse_table::cell {
    bool                                          m_nud;
    list<accepting>                               m_accept;
    name_map<list<pair<transition, parse_table>>> m_children;
    MK_LEAN_RC(); // Declare m_rc counter
    void dealloc() { delete this; }
    cell(bool nud = true):m_nud(nud), m_rc(1) {}
    cell(cell const & c):m_nud(c.m_nud), m_accept(c.m_accept), m_children(c.m_children), m_rc(1) {}
};

parse_table::parse_table(cell * c):m_ptr(c) {}
parse_table::parse_table(bool nud):m_ptr(new cell(nud)) {}
parse_table::parse_table(parse_table const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
parse_table::parse_table(parse_table && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
parse_table::~parse_table() { if (m_ptr) m_ptr->dec_ref(); }
parse_table & parse_table::operator=(parse_table const & s) { LEAN_COPY_REF(s); }
parse_table & parse_table::operator=(parse_table && s) { LEAN_MOVE_REF(s); }
list<pair<transition, parse_table>> parse_table::find(name const & tk) const {
    list<pair<transition, parse_table>> const * it = m_ptr->m_children.find(tk);
    if (it)
        return *it;
    else
        return list<pair<transition, parse_table>>();
}

list<accepting> const & parse_table::is_accepting() const {
    return m_ptr->m_accept;
}

// scoped_expr_actions must occur after a Binder/Binders.
static void validate_transitions(bool nud, unsigned num, transition const * ts, expr const & a) {
    unsigned nargs = 0;
    if (!nud)
        nargs++; // led tables have an implicit left argument
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
    if (get_loose_bvar_range(a) > nargs)
        throw exception("invalid notation declaration, expression template has more bound variables than arguments");
}

static list<accepting> insert(list<accepting> const & l, unsigned priority, list<action> const & p, expr const & a) {
    if (!l) {
        return to_list(accepting(priority, p, a));
    } else if (priority <= head(l).get_prio()) {
        return cons(accepting(priority, p, a), l);
    } else {
        return cons(head(l), insert(tail(l), priority, p, a));
    }
}

static bool contains_equivalent_action(list<pair<transition, parse_table>> const & l, action const & a) {
    for (auto const & p : l) {
        if (p.first.get_action().is_equivalent(a))
            return true;
    }
    return false;
}

parse_table parse_table::add_core(unsigned num, transition const * ts, expr const & a,
                                  unsigned priority, bool overload, buffer<action> & post_buffer) const {
    parse_table r(new cell(*m_ptr));
    if (num == 0) {
        list<action> postponed = to_list(post_buffer);
        if (!overload) {
            r.m_ptr->m_accept = to_list(accepting(priority, postponed, a));
        } else {
            auto new_accept   = filter(r.m_ptr->m_accept, [&](accepting const & p) {
                    return p.get_expr() != a || p.get_postponed() != postponed;
                });
            r.m_ptr->m_accept = insert(new_accept, priority, postponed, a);
        }
    } else {
        list<pair<transition, parse_table>> const * it = r.m_ptr->m_children.find(ts->get_token());
        action const & ts_act = ts->get_action();
        action_kind k = ts_act.kind();
        if (k == action_kind::Exprs || k == action_kind::ScopedExpr)
            post_buffer.push_back(ts_act);
        list<pair<transition, parse_table>> new_lst;
        if (it) {
            if (contains_equivalent_action(*it, ts_act)) {
                buffer<pair<transition, parse_table>> tmp;
                to_buffer(*it, tmp);
                for (pair<transition, parse_table> & p : tmp) {
                    if (p.first.get_action().is_equivalent(ts_act)) {
                        p.second = p.second.add_core(num-1, ts+1, a, priority, overload, post_buffer);
                        break;
                    }
                }
                new_lst = to_list(tmp);
            } else {
                // remove incompatible actions
                new_lst = filter(*it, [&](pair<transition, parse_table> const & p) {
                        return p.first.get_action().is_compatible(ts_act);
                    });
                parse_table new_child = parse_table().add_core(num-1, ts+1, a, priority, overload, post_buffer);
                new_lst   = cons(mk_pair(*ts, new_child), new_lst);
            }
        } else {
            parse_table new_child = parse_table().add_core(num-1, ts+1, a, priority, overload, post_buffer);
            new_lst   = to_list(mk_pair(*ts, new_child));
        }
        r.m_ptr->m_children.insert(ts->get_token(), new_lst);
    }
    return r;
}

static bool is_simple(unsigned num, transition const * ts) {
    return std::all_of(ts, ts+num, [](transition const & t) { return t.is_simple(); });
}

/** \brief Given \c a, an expression that is the denotation of an expression, if \c a is a variable,
    then use the actions in the transitions \c ts to expand \c a. The idea is to produce a head symbol
    we can use to decide whether the notation should be considered during pretty printing.

    \see get_head_index
*/
static expr expand_pp_pattern(unsigned num, transition const * ts, expr const & a) {
    lean_assert(is_simple(num, ts));
    if (!is_var(a))
        return a;
    return replace(a, [&](expr const & e) {
            if (is_bvar(e) && bvar_idx(e).is_small()) {
                unsigned vidx = bvar_idx(e).get_small_value();
                unsigned i = num;
                unsigned offset = 0;
                while (i > 0) {
                    --i;
                    action const & act = ts[i].get_action();
                    switch (act.kind()) {
                    case action_kind::Binder: case action_kind::Binders: case action_kind::Skip:
                        break;
                    case action_kind::Ext:
                        lean_unreachable();
                    case action_kind::Expr:
                        if (vidx == 0) return none_expr();
                        offset++;
                        vidx--;
                        break;
                    case action_kind::Exprs:
                        if (vidx == 0)
                            return some_expr(lift_loose_bvars(act.get_rec(), offset));
                        offset++;
                        vidx--;
                        break;
                    case action_kind::ScopedExpr:
                        if (vidx == 0)
                            return some_expr(lift_loose_bvars(act.get_rec(), offset));
                        offset++;
                        vidx--;
                        break;
                    }
                }
                return none_expr();
            } else {
                return none_expr();
            }
        });
}

optional<head_index> get_head_index(unsigned num, transition const * ts, expr const & a) {
    if (is_simple(num, ts)) {
        expr n = unwrap_pos(expand_pp_pattern(num, ts, a));
        if (!is_var(n))
            return some(head_index(n));
    }
    return optional<head_index>();
}

parse_table parse_table::add(unsigned num, transition const * ts, expr const & a, unsigned priority, bool overload) const {
    buffer<action> postponed;
    expr new_a = annotate_macro_subterms(a);
    validate_transitions(is_nud(), num, ts, new_a);
    return add_core(num, ts, new_a, priority, overload, postponed);
}

void parse_table::for_each(buffer<transition> & ts,
                           std::function<void(unsigned, transition const *,
                                              list<accepting> const &)> const & fn) const {
    if (!is_nil(m_ptr->m_accept))
        fn(ts.size(), ts.data(), m_ptr->m_accept);
    m_ptr->m_children.for_each([&](name const &, list<pair<transition, parse_table>> const & lst) {
            for (auto const & p : lst) {
                ts.push_back(p.first);
                p.second.for_each(ts, fn);
                ts.pop_back();
            }
        });
}

void parse_table::for_each(std::function<void(unsigned, transition const *,
                                              list<accepting> const &)> const & fn) const {
    buffer<transition> tmp;
    for_each(tmp, fn);
}

parse_table parse_table::merge(parse_table const & s, bool overload) const {
    if (is_nud() != s.is_nud())
        throw exception("invalid parse table merge, tables have different kinds");
    parse_table r(*this);
    s.for_each([&](unsigned num, transition const * ts, list<accepting> const & accept) {
            for (accepting const & acc : accept) {
                r = r.add(num, ts, acc.get_expr(), acc.get_prio(), overload);
            }
        });
    return r;
}

bool parse_table::is_nud() const { return m_ptr->m_nud; }

void display(io_state_stream & out, unsigned num, transition const * ts, list<accepting> const & es, bool nud,
             optional<token_table> const & tt) {
    if (!nud)
        out << "_ ";
    for (unsigned i = 0; i < num; i++) {
        if (i > 0) out << " ";
        out << "`" << ts[i].get_token() << "`";
        if (tt) {
            if (auto prec = get_expr_precedence(*tt, ts[i].get_token().to_string().c_str())) {
                out << ":" << *prec;
            }
        }
        switch (ts[i].get_action().kind()) {
        case action_kind::Skip:
            break;
        case action_kind::Expr:
            out << " _:"; ts[i].get_action().display(out);
            break;
        default:
            out << " "; ts[i].get_action().display(out);
            break;
        }
    }
    out << " :=";
    if (length(es) == 1) {
        out << " " << head(es).get_expr() << "\n";
    } else {
        buffer<accepting> tmp;
        to_buffer(es, tmp);
        out << "\n";
        unsigned i = tmp.size();
        while (i > 0) {
            --i;
            out << "  | ";
            if (tmp[i].get_prio() != LEAN_DEFAULT_NOTATION_PRIORITY)
                out << "[priority " << tmp[i].get_prio() << "] ";
            out << tmp[i].get_expr() << "\n";
        }
    }
}

void parse_table::display(io_state_stream & out, optional<token_table> const & tt) const {
    for_each([&](unsigned num, transition const * ts, list<accepting> const & es) {
            ::lean::notation::display(out, num, ts, es, is_nud(), tt);
        });
}
}}
