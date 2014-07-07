/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <utility>
#include "util/rb_map.h"
#include "util/sstream.h"
#include "kernel/free_vars.h"
#include "library/kernel_bindings.h"
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

struct ext_lua_action_cell : public action_cell {
    std::string m_lua_fn;
    ext_lua_action_cell(char const * fn):
        action_cell(action_kind::LuaExt), m_lua_fn(fn) {}
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
    lean_assert(c->m_kind == action_kind::Expr || c->m_kind == action_kind::Exprs || c->m_kind == action_kind::ScopedExpr);
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
ext_lua_action_cell * to_ext_lua_action(action_cell * c) {
    lean_assert(c->m_kind == action_kind::LuaExt);
    return static_cast<ext_lua_action_cell*>(c);
}
unsigned action::rbp() const { return to_expr_action(m_ptr)->m_rbp; }
name const & action::get_sep() const { return to_exprs_action(m_ptr)->m_token_sep; }
expr const & action::get_rec() const {
    if (kind() == action_kind::ScopedExpr)
        return to_scoped_expr_action(m_ptr)->m_rec;
    else
        return to_exprs_action(m_ptr)->m_rec;
}
bool action::use_lambda_abstraction() const { return to_scoped_expr_action(m_ptr)->m_lambda; }
expr const & action::get_initial() const { return to_exprs_action(m_ptr)->m_ini; }
bool action::is_fold_right() const { return to_exprs_action(m_ptr)->m_fold_right; }
parse_fn const & action::get_parse_fn() const { return to_ext_action(m_ptr)->m_parse_fn; }
std::string const & action::get_lua_fn() const { return to_ext_lua_action(m_ptr)->m_lua_fn; }
bool action::is_compatible(action const & a) const {
    if (kind() != a.kind())
        return false;
    switch (kind()) {
    case action_kind::Skip: case action_kind::Binder: case action_kind::Binders:
        return true;
    case action_kind::Ext:
        return m_ptr == a.m_ptr;
    case action_kind::LuaExt:
        return get_lua_fn() == a.get_lua_fn();
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
void action::display(std::ostream & out) const {
    switch (kind()) {
    case action_kind::Skip:    out << "skip"; break;
    case action_kind::Binder:  out << "binder"; break;
    case action_kind::Binders: out << "binders"; break;
    case action_kind::Ext:     out << "ext"; break;
    case action_kind::LuaExt:  out << "luaext"; break;
    case action_kind::Expr:    out << rbp(); break;
    case action_kind::Exprs:
        out << "(fold" << (is_fold_right() ? "r" : "l") << " "
            << rbp() << " " << get_rec() << " " << get_initial() << ")";
        break;
    case action_kind::ScopedExpr:
        out << "(scoped " << rbp() << " " << get_rec() << ")";
        break;
    }
}


void action_cell::dealloc() {
    switch (m_kind) {
    case action_kind::Expr:       delete(to_expr_action(this)); break;
    case action_kind::Exprs:      delete(to_exprs_action(this)); break;
    case action_kind::ScopedExpr: delete(to_scoped_expr_action(this)); break;
    case action_kind::Ext:        delete(to_ext_action(this)); break;
    case action_kind::LuaExt:     delete(to_ext_lua_action(this)); break;
    default:                      delete this; break;
    }
}

action mk_skip_action() {
    static optional<action> r;
    if (!r) r = action(new action_cell(action_kind::Skip));
    return *r;
}
action mk_binder_action() {
    static optional<action> r;
    if (!r) r = action(new action_cell(action_kind::Binder));
    return *r;
}
action mk_binders_action() {
    static optional<action> r;
    if (!r) r = action(new action_cell(action_kind::Binders));
    return *r;
}
action mk_expr_action(unsigned rbp) { return action(new expr_action_cell(rbp)); }
action mk_exprs_action(name const & sep, expr const & rec, expr const & ini, bool right, unsigned rbp) {
    if (get_free_var_range(rec) > 2)
        throw exception("invalid notation, the expression used to combine a sequence of expressions "
                        "must not contain free variables with de Bruijn indices greater than 1");
    return action(new exprs_action_cell(sep, rec, ini, right, rbp));
}
action mk_scoped_expr_action(expr const & rec, unsigned rb, bool lambda) {
    return action(new scoped_expr_action_cell(rec, rb, lambda));
}
action mk_ext_action(parse_fn const & fn) { return action(new ext_action_cell(fn)); }
action mk_ext_lua_action(char const * fn) { return action(new ext_lua_action_cell(fn)); }

struct parse_table::cell {
    bool                                                         m_nud;
    list<expr>                                                   m_accept;
    rb_map<name, std::pair<action, parse_table>, name_quick_cmp> m_children;
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
        case action_kind::Expr: case action_kind::Exprs: case action_kind::Ext: case action_kind::LuaExt:
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

parse_table parse_table::add_core(unsigned num, transition const * ts, expr const & a, bool overload) const {
    parse_table r(new cell(*m_ptr));
    if (num == 0) {
        if (!overload)
            r.m_ptr->m_accept = list<expr>(a);
        else
            r.m_ptr->m_accept = list<expr>(a, remove(r.m_ptr->m_accept, a));
    } else {
        auto * it = r.m_ptr->m_children.find(ts->get_token());
        parse_table new_child;
        if (it) {
            action const & act        = it->first;
            parse_table const & child = it->second;
            if (act.is_compatible(ts->get_action())) {
                new_child = child.add_core(num-1, ts+1, a, overload);
            } else {
                new_child = parse_table().add_core(num-1, ts+1, a, overload);
            }
        } else {
            new_child = parse_table().add_core(num-1, ts+1, a, overload);
        }
        r.m_ptr->m_children.insert(ts->get_token(), mk_pair(ts->get_action(), new_child));
    }
    return r;
}

parse_table parse_table::add(unsigned num, transition const * ts, expr const & a, bool overload) const {
    validate_transitions(is_nud(), num, ts, a);
    return add_core(num, ts, a, overload);
}

void parse_table::for_each(buffer<transition> & ts, std::function<void(unsigned, transition const *, list<expr> const &)> const & fn) const {
    if (!is_nil(m_ptr->m_accept))
        fn(ts.size(), ts.data(), m_ptr->m_accept);
    m_ptr->m_children.for_each([&](name const & k, std::pair<action, parse_table> const & p) {
            ts.push_back(transition(k, p.first));
            p.second.for_each(ts, fn);
            ts.pop_back();
        });
}

void parse_table::for_each(std::function<void(unsigned, transition const *, list<expr> const &)> const & fn) const {
    buffer<transition> tmp;
    for_each(tmp, fn);
}

parse_table parse_table::merge(parse_table const & s, bool overload) const {
    if (is_nud() != s.is_nud())
        throw exception("invalid parse table merge, tables have different kinds");
    parse_table r(*this);
    s.for_each([&](unsigned num, transition const * ts, list<expr> const & accept) {
            for (expr const & a : accept)
                r = r.add(num, ts, a, overload);
        });
    return r;
}

bool parse_table::is_nud() const { return m_ptr->m_nud; }

void parse_table::display(std::ostream & out) const {
    for_each([&](unsigned num, transition const * ts, list<expr> const & es) {
            for (unsigned i = 0; i < num; i++) {
                if (i > 0) out << " ";
                out << "`" << ts[i].get_token() << "`:";
                ts[i].get_action().display(out);
            }
            out << " :=";
            if (length(es) == 1) {
                out << " " << head(es) << "\n";
            } else {
                out << "\n";
                for (auto e : es) {
                    out << "  | " << e << "\n";
                }
            }
        });
}

typedef action notation_action;
DECL_UDATA(notation_action)

static int mk_skip_action(lua_State * L) { return push_notation_action(L, mk_skip_action()); }
static int mk_binder_action(lua_State * L) { return push_notation_action(L, mk_binder_action()); }
static int mk_binders_action(lua_State * L) { return push_notation_action(L, mk_binders_action()); }
static int mk_expr_action(lua_State * L) {
    int nargs = lua_gettop(L);
    unsigned rbp = nargs == 0 ? 0 : lua_tonumber(L, 1);
    return push_notation_action(L, mk_expr_action(rbp));
}
static int mk_exprs_action(lua_State * L) {
    int nargs = lua_gettop(L);
    unsigned rbp = nargs <= 4 ? 0 : lua_tonumber(L, 5);
    return push_notation_action(L, mk_exprs_action(to_name_ext(L, 1),
                                                             to_expr(L, 2),
                                                             to_expr(L, 3),
                                                             lua_toboolean(L, 4), rbp));
}
static int mk_scoped_expr_action(lua_State * L) {
    int nargs = lua_gettop(L);
    unsigned rbp = nargs <= 1 ? 0 : lua_tonumber(L, 2);
    bool lambda = (nargs <= 2) || lua_toboolean(L, 3);
    return push_notation_action(L, mk_scoped_expr_action(to_expr(L, 1), rbp, lambda));
}
static int mk_ext_lua_action(lua_State * L) {
    char const * fn = lua_tostring(L, 1);
    lua_getglobal(L, fn);
    if (lua_isnil(L, -1))
        throw exception("arg #1 is a unknown function name");
    lua_pop(L, 1);
    return push_notation_action(L, mk_ext_lua_action(fn));
}
static int is_compatible(lua_State * L) {
    return push_boolean(L, to_notation_action(L, 1).is_compatible(to_notation_action(L, 2)));
}
static void check_action(lua_State * L, int idx, std::initializer_list<action_kind> const & ks) {
    action_kind k = to_notation_action(L, idx).kind();
    if (std::find(ks.begin(), ks.end(), k) == ks.end())
        throw exception(sstream() << "arg #" << idx << " is a notation action, but it has an unexpected kind");
}
static int kind(lua_State * L) { return push_integer(L, static_cast<unsigned>(to_notation_action(L, 1).kind())); }
static int rbp(lua_State * L) {
    check_action(L, 1, { action_kind::Expr, action_kind::Exprs, action_kind::ScopedExpr });
    return push_integer(L, to_notation_action(L, 1).rbp());
}
static int sep(lua_State * L) {
    check_action(L, 1, { action_kind::Exprs });
    return push_name(L, to_notation_action(L, 1).get_sep());
}
static int rec(lua_State * L) {
    check_action(L, 1, { action_kind::Exprs, action_kind::ScopedExpr });
    return push_expr(L, to_notation_action(L, 1).get_rec());
}
static int initial(lua_State * L) {
    check_action(L, 1, { action_kind::Exprs });
    return push_expr(L, to_notation_action(L, 1).get_initial());
}
static int is_fold_right(lua_State * L) {
    check_action(L, 1, { action_kind::Exprs });
    return push_boolean(L, to_notation_action(L, 1).is_fold_right());
}
static int use_lambda_abstraction(lua_State * L) {
    check_action(L, 1, { action_kind::ScopedExpr });
    return push_boolean(L, to_notation_action(L, 1).use_lambda_abstraction());
}
static int fn(lua_State * L) {
    check_action(L, 1, { action_kind::LuaExt });
    return push_string(L, to_notation_action(L, 1).get_lua_fn().c_str());
}

static const struct luaL_Reg notation_action_m[] = {
    {"__gc",                   notation_action_gc},
    {"is_compatible",          safe_function<is_compatible>},
    {"kind",                   safe_function<kind>},
    {"rbp",                    safe_function<rbp>},
    {"sep",                    safe_function<sep>},
    {"separator",              safe_function<sep>},
    {"rec",                    safe_function<rec>},
    {"initial",                safe_function<initial>},
    {"is_fold_right",          safe_function<is_fold_right>},
    {"use_lambda_abstraction", safe_function<use_lambda_abstraction>},
    {"fn",                     safe_function<fn>},
    {0, 0}
};

static void open_notation_action(lua_State * L) {
    luaL_newmetatable(L, notation_action_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, notation_action_m, 0);

    SET_GLOBAL_FUN(notation_action_pred,   "is_notation_action");
    SET_GLOBAL_FUN(mk_skip_action,         "skip_notation_action");
    SET_GLOBAL_FUN(mk_binder_action,       "binder_notation_action");
    SET_GLOBAL_FUN(mk_binders_action,      "binders_notation_action");
    SET_GLOBAL_FUN(mk_expr_action,         "expr_notation_action");
    SET_GLOBAL_FUN(mk_exprs_action,        "exprs_notation_action");
    SET_GLOBAL_FUN(mk_scoped_expr_action,  "scoped_expr_notation_action");
    SET_GLOBAL_FUN(mk_ext_lua_action,      "ext_action");

    push_notation_action(L, mk_skip_action());
    lua_setglobal(L, "Skip");
    push_notation_action(L, mk_binder_action());
    lua_setglobal(L, "Binder");
    push_notation_action(L, mk_binders_action());
    lua_setglobal(L, "Binders");

    lua_newtable(L);
    SET_ENUM("Skip",        action_kind::Skip);
    SET_ENUM("Expr",        action_kind::Expr);
    SET_ENUM("Exprs",       action_kind::Exprs);
    SET_ENUM("Binder",      action_kind::Binder);
    SET_ENUM("Binders",     action_kind::Binders);
    SET_ENUM("ScopedExpr",  action_kind::ScopedExpr);
    SET_ENUM("Ext",         action_kind::Ext);
    SET_ENUM("LuaExt",      action_kind::LuaExt);
    lua_setglobal(L, "notation_action_kind");
}

static notation_action to_notation_action_ext(lua_State * L, int idx) {
    if (is_notation_action(L, idx)) {
        return to_notation_action(L, idx);
    } else if (lua_isnumber(L, idx)) {
        return mk_expr_action(lua_tonumber(L, idx));
    } else {
        throw exception("notation_action expected");
    }
}

DECL_UDATA(parse_table)
static int mk_parse_table(lua_State * L) {
    int nargs = lua_gettop(L);
    bool nud  = nargs == 0 || lua_toboolean(L, 1);
    return push_parse_table(L, parse_table(nud));
}
static int add(lua_State * L) {
    int nargs = lua_gettop(L);
    buffer<transition> ts;
    luaL_checktype(L, 2, LUA_TTABLE);
    int sz = objlen(L, 2);
    for (int i = 1; i <= sz; i++) {
        lua_rawgeti(L, 2, i);
        if (lua_isstring(L, -1) || is_name(L, -1)) {
            ts.push_back(transition(to_name_ext(L, -1), mk_expr_action()));
            lua_pop(L, 1);
        } else {
            luaL_checktype(L, -1, LUA_TTABLE);
            lua_rawgeti(L, -1, 1);
            lua_rawgeti(L, -2, 2);
            ts.push_back(transition(to_name_ext(L, -2), to_notation_action_ext(L, -1)));
            lua_pop(L, 3);
        }
    }
    bool overload = (nargs <= 3) || lua_toboolean(L, 4);
    return push_parse_table(L, to_parse_table(L, 1).add(ts.size(), ts.data(), to_expr(L, 3), overload));
}

static int merge(lua_State * L) {
    int nargs = lua_gettop(L);
    bool overload = (nargs >= 2) && lua_toboolean(L, 2);
    return push_parse_table(L, to_parse_table(L, 1).merge(to_parse_table(L, 2), overload));
}

static int find(lua_State * L) {
    auto p = to_parse_table(L, 1).find(to_name_ext(L, 2));
    if (p) {
        push_notation_action(L, p->first);
        push_parse_table(L, p->second);
        return 2;
    } else {
        return push_nil(L);
    }
}

static int is_accepting(lua_State * L) {
    list<expr> const & l = to_parse_table(L, 1).is_accepting();
    if (is_nil(l))
        return push_nil(L);
    else
        return push_list_expr(L, l);
}

static int for_each(lua_State * L) {
    parse_table const & t = to_parse_table(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION); // user-fun
    t.for_each([&](unsigned num, transition const * ts, list<expr> const & as) {
            lua_pushvalue(L, 2);
            lua_newtable(L);
            for (unsigned i = 0; i < num; i++) {
                lua_newtable(L);
                push_name(L, ts[i].get_token());
                lua_rawseti(L, -2, 1);
                push_notation_action(L, ts[i].get_action());
                lua_rawseti(L, -2, 2);
                lua_rawseti(L, -2, i+1);
            }
            push_list_expr(L, as);
            pcall(L, 2, 0, 0);
        });
    return 0;
}

static int is_nud(lua_State * L) {
    return push_boolean(L, to_parse_table(L, 1).is_nud());
}

static const struct luaL_Reg parse_table_m[] = {
    {"__gc",             parse_table_gc},
    {"add",              safe_function<add>},
    {"merge",            safe_function<merge>},
    {"find",             safe_function<find>},
    {"is_accepting",     safe_function<is_accepting>},
    {"for_each",         safe_function<for_each>},
    {"is_nud",           safe_function<is_nud>},
    {0, 0}
};

static void open_parse_table(lua_State * L) {
    luaL_newmetatable(L, parse_table_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, parse_table_m, 0);

    SET_GLOBAL_FUN(parse_table_pred,   "is_parse_table");
    SET_GLOBAL_FUN(mk_parse_table,     "parse_table");
}
}
void open_parse_table(lua_State * L) {
    notation::open_notation_action(L);
    notation::open_parse_table(L);
}
}
