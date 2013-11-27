/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include "util/sstream.h"
#include "util/sexpr/options.h"
#include "util/sexpr/option_declarations.h"
#include "util/sexpr/sexpr_fn.h"

namespace lean {
std::ostream & operator<<(std::ostream & out, option_kind k) {
    switch (k) {
    case BoolOption: out << "Bool"; break;
    case IntOption:  out << "Int"; break;
    case UnsignedOption: out << "Unsigned Int"; break;
    case DoubleOption: out << "Double"; break;
    case StringOption: out << "String"; break;
    case SExprOption: out << "S-Expression"; break;
    }
    return out;
}

static std::unique_ptr<option_declarations> g_option_declarations;

option_declarations & get_option_declarations_core() {
    if (!g_option_declarations)
        g_option_declarations.reset(new option_declarations());
    return *g_option_declarations;
}

option_declarations const & get_option_declarations() {
    return get_option_declarations_core();
}

mk_option_declaration::mk_option_declaration(name const & n, option_kind k, char const * default_value, char const * description) {
    get_option_declarations_core().insert(mk_pair(n, option_declaration(n, k, default_value, description)));
}

bool options::empty() const {
    return is_nil(m_value);
}

unsigned options::size() const {
    return length(m_value);
}

bool options::contains(name const & n) const {
    return ::lean::contains(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
}

bool options::contains(char const * n) const {
    return ::lean::contains(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
}

sexpr options::get_sexpr(name const & n, sexpr const & default_value) const {
    sexpr const * r = find(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
    return r == nullptr ? default_value : tail(*r);
}

int options::get_int(name const & n, int default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? to_int(r) : default_value;
}

unsigned options::get_unsigned(name const & n, unsigned default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? static_cast<unsigned>(to_int(r)) : default_value;
}

bool options::get_bool(name const & n, bool default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_bool(r) ? to_bool(r) != 0 : default_value;
}

double options::get_double(name const & n, double default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_double(r) ? to_double(r) : default_value;
}

char const * options::get_string(name const & n, char const * default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_string(r) ? to_string(r).c_str() : default_value;
}

sexpr options::get_sexpr(char const * n, sexpr const & default_value) const {
    sexpr const * r = find(m_value, [&](sexpr const & p) { return to_name(head(p)) == n; });
    return r == nullptr ? default_value : tail(*r);
}

int options::get_int(char const * n, int default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? to_int(r) : default_value;
}

unsigned options::get_unsigned(char const * n, unsigned default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_int(r) ? static_cast<unsigned>(to_int(r)) : default_value;
}

bool options::get_bool(char const * n, bool default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_bool(r) ? to_bool(r) != 0 : default_value;
}

double options::get_double(char const * n, double default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_double(r) ? to_double(r) : default_value;
}

char const * options::get_string(char const * n, char const * default_value) const {
    sexpr const & r = get_sexpr(n);
    return !is_nil(r) && is_string(r) ? to_string(r).c_str() : default_value;
}

static char const * g_left_angle_bracket  = "\u27E8";
static char const * g_right_angle_bracket = "\u27E9";
static char const * g_arrow               = "\u21a6";
static char const * g_assign              = ":=";

options options::update(name const & n, sexpr const & v) const {
    if (contains(n)) {
        return map(m_value, [&](sexpr p) {
                if (to_name(car(p)) == n)
                    return cons(car(p), v);
                else
                    return p;
            });
    } else {
        return options(cons(cons(sexpr(n), v), m_value));
    }
}

options join(options const & opts1, options const & opts2) {
    sexpr r = opts2.m_value;
    for_each(opts1.m_value, [&](sexpr const & p) {
            if (!opts2.contains(to_name(car(p))))
                r = cons(p, r);
        });
    return options(r);
}

format pp(options const & o) {
    bool unicode = get_pp_unicode(o);
    format r;
    bool first = true;
    char const * arrow = unicode ? g_arrow : g_assign;
    for_each(o.m_value, [&](sexpr const & p) {
            if (first) { first = false; } else { r += comma(); r += line(); }
            name const & n = to_name(head(p));
            unsigned sz = n.size();
            unsigned indent = unicode ? sz+3 : sz+4;
            r += group(nest(indent, format{pp(head(p)), space(), format(arrow), space(), pp(tail(p))}));
        });
    format open  = unicode ? format(g_left_angle_bracket) : lp();
    format close = unicode ? format(g_right_angle_bracket) : rp();
    return group(nest(1, format{open, r, close}));
}

std::ostream & operator<<(std::ostream & out, options const & o) {
    bool unicode = get_pp_unicode(o);
    out << (unicode ? g_left_angle_bracket : "(");
    bool first = true;
    for_each(o.m_value, [&](sexpr const & p) {
            if (first) first = false; else out << ", ";
            out << head(p) << " " << (unicode ? g_arrow : g_assign) << " " << tail(p);
        });
    out << (unicode ? g_right_angle_bracket : ")");
    return out;
}

DECL_UDATA(options)

static int mk_options(lua_State * L) {
    options r;
    int nargs = lua_gettop(L);
    if (nargs % 2 != 0)
        throw exception("options expects an even number of arguments");
    for (int i = 1; i < nargs; i+=2) {
        name k = to_name_ext(L, i);
        auto it = get_option_declarations().find(k);
        if (it == get_option_declarations().end()) {
            throw exception(sstream() << "unknown option '" << k.to_string().c_str() << "'");
        } else {
            option_declaration const & d = it->second;
            switch (d.kind()) {
            case BoolOption:      r = r.update(k, static_cast<bool>(lua_toboolean(L, i+1))); break;
            case IntOption:       r = r.update(k, static_cast<int>(lua_tointeger(L, i+1))); break;
            case UnsignedOption:  r = r.update(k, static_cast<unsigned>(lua_tointeger(L, i+1))); break;
            case DoubleOption:    r = r.update(k, static_cast<double>(lua_tonumber(L, i+1))); break;
            case StringOption:    r = r.update(k, lua_tostring(L, i+1)); break;
            default:              throw exception(sstream() << "unsupported option kind for '" << k.to_string().c_str() << "'");
            }
        }
    }
    return push_options(L, r);
}

static int options_tostring(lua_State * L) {
    std::ostringstream out;
    out << to_options(L, 1);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int options_size(lua_State * L) {
    lua_pushinteger(L, to_options(L, 1).size());
    return 1;
}

static int options_contains(lua_State * L) {
    lua_pushboolean(L, to_options(L, 1).contains(to_name_ext(L, 2)));
    return 1;
}

static int options_empty(lua_State * L) {
    lua_pushboolean(L, to_options(L, 1).empty());
    return 1;
}

static int options_get_bool(lua_State * L) {
    int nargs = lua_gettop(L);
    bool defval = nargs < 3 ? false : lua_toboolean(L, 3);
    lua_pushboolean(L, to_options(L, 1).get_bool(to_name_ext(L, 2), defval));
    return 1;
}

static int options_get_int(lua_State * L) {
    int nargs = lua_gettop(L);
    int defval = nargs < 3 ? 0 : lua_tointeger(L, 3);
    lua_pushinteger(L, to_options(L, 1).get_int(to_name_ext(L, 2), defval));
    return 1;
}

static int options_get_unsigned(lua_State * L) {
    int nargs = lua_gettop(L);
    unsigned defval = nargs < 3 ? 0 : lua_tointeger(L, 3);
    lua_pushnumber(L, to_options(L, 1).get_unsigned(to_name_ext(L, 2), defval));
    return 1;
}

static int options_get_double(lua_State * L) {
    int nargs = lua_gettop(L);
    double defval = nargs < 3 ? 0.0 : lua_tonumber(L, 3);
    lua_pushnumber(L, to_options(L, 1).get_double(to_name_ext(L, 2), defval));
    return 1;
}

static int options_get_string(lua_State * L) {
    int nargs = lua_gettop(L);
    char const * defval = nargs < 3 ? "" : lua_tostring(L, 3);
    lua_pushstring(L, to_options(L, 1).get_string(to_name_ext(L, 2), defval));
    return 1;
}

static int options_update_bool(lua_State * L) {
    return push_options(L, to_options(L, 1).update(to_name_ext(L, 2), static_cast<bool>(lua_toboolean(L, 3))));
}

static int options_update_int(lua_State * L) {
    return push_options(L, to_options(L, 1).update(to_name_ext(L, 2), static_cast<int>(lua_tointeger(L, 3))));
}

static int options_update_unsigned(lua_State * L) {
    return push_options(L, to_options(L, 1).update(to_name_ext(L, 2), static_cast<unsigned>(lua_tointeger(L, 3))));
}

static int options_update_double(lua_State * L) {
    return push_options(L, to_options(L, 1).update(to_name_ext(L, 2), lua_tonumber(L, 3)));
}

static int options_update_string(lua_State * L) {
    return push_options(L, to_options(L, 1).update(to_name_ext(L, 2), lua_tostring(L, 3)));
}

static int options_get(lua_State * L) {
    name k = to_name_ext(L, 2);
    auto it = get_option_declarations().find(k);
    if (it == get_option_declarations().end()) {
        throw exception(sstream() << "unknown option '" << k.to_string().c_str() << "'");
    } else {
        option_declaration const & d = it->second;
        switch (d.kind()) {
        case BoolOption:      return options_get_bool(L);
        case IntOption:       return options_get_int(L);
        case UnsignedOption:  return options_get_unsigned(L);
        case DoubleOption:    return options_get_double(L);
        case StringOption:    return options_get_string(L);
        default:              throw exception(sstream() << "unsupported option kind for '" << k.to_string().c_str() << "'");
        }
    }
}

int options_update(lua_State * L) {
    name k = to_name_ext(L, 2);
    auto it = get_option_declarations().find(k);
    if (it == get_option_declarations().end()) {
        throw exception(sstream() << "unknown option '" << k.to_string().c_str() << "'");
    } else {
        option_declaration const & d = it->second;
        switch (d.kind()) {
        case BoolOption:      return options_update_bool(L);
        case IntOption:       return options_update_int(L);
        case UnsignedOption:  return options_update_unsigned(L);
        case DoubleOption:    return options_update_double(L);
        case StringOption:    return options_update_string(L);
        default:              throw exception(sstream() << "unsupported option kind for '" << k.to_string().c_str() << "'");
        }
    }
}

static const struct luaL_Reg options_m[] = {
    {"__gc",            options_gc}, // never throws
    {"__tostring",      safe_function<options_tostring>},
    {"__len",           safe_function<options_size> },
    {"contains",        safe_function<options_contains>},
    {"size",            safe_function<options_size>},
    {"empty",           safe_function<options_empty>},
    {"get",             safe_function<options_get>},
    {"update",          safe_function<options_update>},
    // low-level API
    {"get_bool",        safe_function<options_get_bool>},
    {"get_int",         safe_function<options_get_int>},
    {"get_unsigned",    safe_function<options_get_unsigned>},
    {"get_double",      safe_function<options_get_double>},
    {"get_string",      safe_function<options_get_string>},
    {"update_bool",     safe_function<options_update_bool>},
    {"update_int",      safe_function<options_update_int>},
    {"update_unsigned", safe_function<options_update_unsigned>},
    {"update_double",   safe_function<options_update_double>},
    {"update_string",   safe_function<options_update_string>},
    {0, 0}
};

static char g_options_key;

options get_global_options(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_options_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    options r;
    if (is_options(L, -1))
        r = to_options(L, -1);
    lua_pop(L, 1);
    return r;
}

void set_global_options(lua_State * L, options const & o) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_options_key));
    push_options(L, o);
    lua_settable(L, LUA_REGISTRYINDEX);
}

static int _get_global_options(lua_State * L) {
    return push_options(L, get_global_options(L));
}

static int _set_global_options(lua_State * L) {
    options o = to_options(L, 1);
    set_global_options(L, o);
    return 0;
}

static int _set_global_option(lua_State * L) {
    options o = get_global_options(L);
    push_options(L, o);
    lua_insert(L, 1);
    options_update(L);
    o = to_options(L, -1);
    set_global_options(L, o);
    return 0;
}

static void options_migrate(lua_State * src, int i, lua_State * tgt) {
    push_options(tgt, to_options(src, i));
}

void open_options(lua_State * L) {
    luaL_newmetatable(L, options_mt);
    set_migrate_fn_field(L, -1, options_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, options_m, 0);

    SET_GLOBAL_FUN(mk_options,          "options");
    SET_GLOBAL_FUN(options_pred,        "is_options");
    SET_GLOBAL_FUN(_get_global_options, "get_options");
    SET_GLOBAL_FUN(_set_global_options, "set_options");
    SET_GLOBAL_FUN(_set_global_option,  "set_option");
}
}
